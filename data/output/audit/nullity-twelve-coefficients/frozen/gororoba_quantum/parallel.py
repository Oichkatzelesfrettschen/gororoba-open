"""Order-preserving process-parallel map over CPU-bound, picklable work.

Workers start under the spawn method on every platform: forking a process
that already runs Aer or rustworkx thread pools can deadlock a child on a lock
another thread held, while spawn starts each worker from a fresh interpreter.
One pool serves the whole process, so the interpreter and import start-up of
its workers is paid once. The callable travels as pickled bytes keyed by their
sha256; each worker unpickles a given callable once and reuses it for every
later chunk, so a large callable such as a Target with its circuits costs one
deserialization per worker. Results come back in input order, so a parallel
run returns exactly what the serial loop returns.

GOROROBA_WORKERS caps the worker count; 1 runs serially in-process. The
default is the CPU count available to this process.

Each worker's BLAS and OpenMP libraries start with one thread: the pool is
the parallelism. OpenBLAS and OpenMP read OPENBLAS_NUM_THREADS and
OMP_NUM_THREADS when a worker imports them and otherwise start one thread
per CPU in every worker, so N workers would run N times the CPUs' threads on
matrices too small to repay BLAS threading (WORKER_BLAS_THREADS). A variable
the caller already set keeps its value. The variables apply only while the
pool spawns workers, which ProcessPoolExecutor does inside submit, so the
calling process keeps its own settings.
"""

from __future__ import annotations

import argparse
import atexit
import contextlib
import hashlib
import math
import multiprocessing
import os
import pickle
from collections.abc import Callable, Iterator, Sequence
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from typing import Any

# Below this many fine-grained items the work does not repay the
# inter-process transfer; a caller whose items each run for seconds passes a
# smaller min_items.
MIN_PARALLEL_ITEMS = 64
# Chunks per worker: enough to balance uneven item costs, few enough that the
# per-chunk callable transfer stays small against the work.
CHUNKS_PER_WORKER = 4
# Callables each worker keeps deserialized; one pipeline stage reuses one.
WORKER_CACHE_SIZE = 4
# Thread-count variables of the BLAS builds numpy and scipy link (OpenBLAS,
# MKL, BLIS, Accelerate) and of OpenMP, which Aer and OpenMP-threaded BLAS read.
WORKER_THREAD_VARIABLES = (
    "OPENBLAS_NUM_THREADS",
    "OMP_NUM_THREADS",
    "MKL_NUM_THREADS",
    "BLIS_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "RAYON_NUM_THREADS",
    "QISKIT_NUM_PROCS",
)
# BLAS and OpenMP threads per worker: the pool supplies the parallelism, and
# the matrices a worker handles are too small to repay BLAS threading. core-520
# checks that every spawned worker reads this value.
WORKER_BLAS_THREADS = 1

_pool: ProcessPoolExecutor | None = None
_pool_size = 0
_worker_cache: dict[str, Callable[[Any], Any]] = {}


PROC_SELF_CGROUP = Path("/proc/self/cgroup")
CGROUP_ROOT = Path("/sys/fs/cgroup")


def workers() -> int:
    """The process budget, bounded by affinity/quota and GOROROBA_WORKERS."""
    return default_threads()


def default_threads() -> int:
    """Bound simulation threads and process workers by the same CPU allocation.

    A caller's GOROROBA_WORKERS cap limits both executors. A spawned pool
    worker receives one slot so its simulations and nested maps share that
    slot instead of multiplying the outer pool's allocation.
    """
    capacity = available_cpus()
    configured = os.environ.get("GOROROBA_WORKERS")
    if configured is None:
        return capacity
    count = int(configured)
    if count < 1:
        raise ValueError(f"GOROROBA_WORKERS must be a positive integer, got {configured!r}")
    return min(capacity, count)


def available_cpus() -> int:
    """The CPUs available to this process.

    The affinity mask counts the CPUs the scheduler may use; the process's
    cgroup hierarchy can grant fewer through a CPU quota on its own cgroup or
    any ancestor, so the smaller of the two is the count, rounded up to a
    whole CPU.
    """
    # sched_getaffinity honors CPU pinning where the platform provides it
    # (Linux); cpu_count covers macOS and Windows.
    if hasattr(os, "sched_getaffinity"):
        available = len(os.sched_getaffinity(0)) or 1
    else:
        available = os.cpu_count() or 1
    quota = cgroup_cpu_quota()
    return max(1, min(available, math.ceil(quota))) if quota is not None else available


def cgroup_cpu_quota(proc_cgroup: Path = PROC_SELF_CGROUP, cgroup_root: Path = CGROUP_ROOT) -> float | None:
    """CPUs the process's cgroup hierarchy grants: the tightest quota on its cgroup or any ancestor, or None.

    /proc/self/cgroup names the process's cgroup in each hierarchy. A cgroup
    v2 line "0::/path" places cpu.max ("QUOTA PERIOD" in microseconds, "max"
    for none) under cgroup_root/path and in every ancestor directory up to the
    root. A cgroup v1 line whose controllers include cpu places
    cpu.cfs_quota_us (-1 for none) and cpu.cfs_period_us under the cpu
    controller mount, cgroup_root/cpu or cgroup_root/cpu,cpuacct. Quotas on
    ancestors bind the descendant, so the minimum over the walk is the grant.
    An unreadable or malformed file counts as no quota at that node.
    """
    try:
        lines = proc_cgroup.read_text().splitlines()
    except OSError:
        return None
    quotas: list[float] = []
    for line in lines:
        fields = line.split(":", 2)
        if len(fields) != 3:
            continue
        hierarchy, controllers, path = fields
        if hierarchy == "0" and controllers == "":
            for node in _cgroup_ancestors(cgroup_root, path):
                quota = _cgroup_v2_quota(node / "cpu.max")
                if quota is not None:
                    quotas.append(quota)
        elif "cpu" in controllers.split(","):
            for mount in (cgroup_root / "cpu", cgroup_root / "cpu,cpuacct"):
                if not mount.is_dir():
                    continue
                for node in _cgroup_ancestors(mount, path):
                    quota = _cgroup_v1_quota(node / "cpu.cfs_quota_us", node / "cpu.cfs_period_us")
                    if quota is not None:
                        quotas.append(quota)
                break
    return min(quotas) if quotas else None


def _cgroup_ancestors(mount: Path, path: str) -> list[Path]:
    """The cgroup directory named by path under mount, then each ancestor up to mount."""
    parts = [part for part in path.strip("/").split("/") if part]
    return [mount.joinpath(*parts[:depth]) for depth in range(len(parts), -1, -1)]


def _cgroup_v2_quota(cpu_max: Path) -> float | None:
    try:
        quota_text, period_text = cpu_max.read_text().split()
        if quota_text == "max":
            return None
        quota, period = int(quota_text), int(period_text)
    except (OSError, ValueError):
        return None
    return quota / period if quota > 0 and period > 0 else None


def _cgroup_v1_quota(quota_file: Path, period_file: Path) -> float | None:
    try:
        quota, period = int(quota_file.read_text()), int(period_file.read_text())
    except (OSError, ValueError):
        return None
    return quota / period if quota > 0 and period > 0 else None


@contextlib.contextmanager
def _worker_environment() -> Iterator[None]:
    """Set every unset thread-count variable for workers spawned inside the block, then restore the environment."""
    value = str(WORKER_BLAS_THREADS)
    added = [name for name in WORKER_THREAD_VARIABLES if name not in os.environ]
    for name in added:
        os.environ[name] = value
    try:
        yield
    finally:
        for name in added:
            os.environ.pop(name, None)


def _initialize_worker() -> None:
    """Give each spawned worker one slot without mutating the parent's budget."""
    os.environ["GOROROBA_WORKERS"] = "1"


def _executor(count: int) -> ProcessPoolExecutor:
    global _pool, _pool_size
    if _pool is None or _pool_size != count:
        if _pool is not None:
            _pool.shutdown()
        _pool = ProcessPoolExecutor(
            count, mp_context=multiprocessing.get_context("spawn"), initializer=_initialize_worker
        )
        _pool_size = count
    return _pool


@atexit.register
def _shutdown() -> None:
    global _pool
    if _pool is not None:
        _pool.shutdown()
        _pool = None


def _run_chunk(key: str, payload: bytes, chunk: list[Any]) -> list[Any]:
    function = _worker_cache.get(key)
    if function is None:
        function = pickle.loads(payload)
        if len(_worker_cache) >= WORKER_CACHE_SIZE:
            _worker_cache.pop(next(iter(_worker_cache)))
        _worker_cache[key] = function
    return [function(item) for item in chunk]


def ordered_map(function: Callable[[Any], Any], items: Sequence[Any], min_items: int = MIN_PARALLEL_ITEMS) -> list[Any]:
    """[function(item) for item in items], spread over the process pool.

    function and every item must pickle; function must be a module-level
    callable or an instance of a module-level class.
    """
    count = min(workers(), len(items))
    if count <= 1 or len(items) < min_items:
        return [function(item) for item in items]
    payload = pickle.dumps(function)
    key = hashlib.sha256(payload).hexdigest()
    size = -(-len(items) // (CHUNKS_PER_WORKER * count))
    chunks = [list(items[start : start + size]) for start in range(0, len(items), size)]
    with _worker_environment():
        pool = _executor(count)
        futures = [pool.submit(_run_chunk, key, payload, chunk) for chunk in chunks]
    return [result for future in futures for result in future.result()]


def _thread_settings(_item: int) -> dict[str, str | None]:
    return {name: os.environ.get(name) for name in WORKER_THREAD_VARIABLES}


def _process_budget(item: int) -> tuple[int, int, int, int]:
    return item, os.getpid(), workers(), default_threads()


def _nested_budget(item: int) -> tuple[int, list[tuple[int, int, int, int]]]:
    return os.getpid(), ordered_map(_process_budget, [4 * item + offset for offset in range(4)], min_items=1)


def _square(item: int) -> int:
    return item * item


def self_test() -> str:
    """Workers start one BLAS/OpenMP thread, a caller's setting wins, the parent is restored, order is kept."""
    saved = {name: os.environ.pop(name, None) for name in (*WORKER_THREAD_VARIABLES, "GOROROBA_WORKERS")}
    _shutdown()
    try:
        count = min(2, available_cpus())
        os.environ["GOROROBA_WORKERS"] = str(count)
        expected = str(WORKER_BLAS_THREADS) if count > 1 else None
        os.environ["MKL_NUM_THREADS"] = "3"
        seen = ordered_map(_thread_settings, list(range(4 * count)), min_items=1)
        for settings in seen:
            for name in WORKER_THREAD_VARIABLES:
                want = "3" if name == "MKL_NUM_THREADS" else expected
                if settings[name] != want:
                    raise SystemExit(f"parallel: a worker read {name}={settings[name]!r}, expected {want!r}")
        if {name: os.environ.get(name) for name in WORKER_THREAD_VARIABLES} != {
            name: ("3" if name == "MKL_NUM_THREADS" else None) for name in WORKER_THREAD_VARIABLES
        }:
            raise SystemExit("parallel: the parent environment kept a worker thread setting")
        for owner, nested in ordered_map(_nested_budget, list(range(4 * count)), min_items=1):
            if any(pid != owner or process_budget != 1 or threads != 1 for _, pid, process_budget, threads in nested):
                raise SystemExit(f"parallel: a nested map left its worker's single slot: {nested}")
        if workers() != count or default_threads() != count:
            raise SystemExit("parallel: a spawned worker changed the parent's CPU budget")
        items = list(range(257))
        if ordered_map(_square, items, min_items=1) != [_square(item) for item in items]:
            raise SystemExit("parallel: the pooled map differs from the serial loop")
    finally:
        _shutdown()
        for name, value in saved.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
    native = f"{expected} BLAS/OpenMP threads each" if count > 1 else "the serial caller's native settings"
    return f"{count} workers read {native}; nested maps keep one slot; caller settings and order preserved"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    if not parser.parse_args().self_test:
        parser.error("--self-test is the only action")
    print(f"parallel: {self_test()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
