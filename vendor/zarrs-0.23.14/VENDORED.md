# Vendored zarrs 0.23.14

Upstream: zarrs 0.23.14 as published on crates.io (archive SHA-256
`fbd6697e73e803a80f182036563038ccfaf7fca1b71fc510cce65daaa45478f8`), source
repository https://github.com/zarrs/zarrs.

Applied upstream change: zarrs pull request 497 (merge commit `3e9f64add5`),
which moves the `blusc` dependency from 0.0.6 to 0.0.7 and sets the blosc
compression typesize to `typesize.max(1)` in
`src/array/codec/bytes_to_bytes/blosc/blosc_via_blusc.rs`. blusc 0.0.7 replaces
the C `zstd` crate with the pure-Rust `zrip`. The pull request's removal of the
`std::borrow::Cow` import in `blosc_codec_via_blusc.rs` is not applied, because
0.23.14 still uses `Cow` in that file.

Local change beyond the upstream commit: `Cargo.toml` and `Cargo.toml.orig` drop
the `zstd` feature of the non-wasm `blosc-src` dependency. That feature pulls
the C `zstd-sys` crate. Blosc chunks that use the zstd compressor therefore fail
to decode on native targets; lz4, lz4hc, zlib and snappy chunks decode.

Reason: the C `zstd`, `zstd-safe` and `zstd-sys` crates carry RustSec advisories
and the workspace dependency graph removes them in every feature combination.

Removal condition: drop the `[patch.crates-io] zarrs` entry in the root
`Cargo.toml` and delete this directory when a zarrs release requires
`blusc >= 0.0.7`, and re-evaluate the `blosc-src` zstd feature at that time.
