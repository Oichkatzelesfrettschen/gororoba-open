# awaiting-triage

This orphan branch mirrors the workspace folder `awaiting-triage/`: material that no repository owns yet. Each item
sits in its own subdirectory until the owner decides its home: a repository, a documents manifest, the planned
workspace data folder, or deletion. The branch shares no history with `main`, carries no workflows, and takes no pull
request.

## scientific-payload-archive

`scientific-payloads-7a5e2494d6f5afee30ea62641bd474929d365d52cdec26426f70e1e3f9766459.tar.zst` is the asset that the
gororoba-open release `scientific-payload-archive` held until it was deleted on 2026-11-01. GitHub rejects files over
100 MB, so the branch stores it as 19 numbered parts of 95 MiB each, listed in `parts.sha256`. The joined archive is
1,836,011,796 bytes, and its SHA-256 is the hex string in its name. It unpacks to 7.44 GB. Its tar members are named by
content hash, and `scientific-payloads.json`, copied from the `main` branch at `data/retention/`, maps each of
the 3,419 repository paths to its member digest.

Reassemble and verify from `scientific-payload-archive/`:

```sh
sha256sum -c parts.sha256
F=scientific-payloads-7a5e2494d6f5afee30ea62641bd474929d365d52cdec26426f70e1e3f9766459.tar.zst
cat "$F".part-* > "$F"
sha256sum "$F"   # prints the digest in the name
zstd -t "$F"
```

Unique contents: 173 members exist nowhere else. 140.6 MB of them is first-party claim-family audit output: geometric
training and evaluation, control recovery, null-pilot binaries and a Euclid measurement parquet. The 23 third-party
PDFs among them are filed in the documents repositories. Pull request #252 (`060f652c`) moved the first-party
`curated/`, `data/csv` and `data/results` members into `main`. gororoba-infrastructure
`docs/design/workspace-data-folder.md` records the custody and the open decision on the data folder.
