-- SPDX-License-Identifier: GPL-2.0-or-later
-- Separate observation ledger. Never execute against control_plane.sqlite3.
PRAGMA foreign_keys = ON;
BEGIN;
CREATE TABLE IF NOT EXISTS observatory_source (
 source_id TEXT PRIMARY KEY,
 domain TEXT NOT NULL,
 url TEXT NOT NULL CHECK(url LIKE 'https://%'),
 access TEXT NOT NULL,
 metadata_json TEXT NOT NULL CHECK(json_valid(metadata_json))
) STRICT;
CREATE TABLE IF NOT EXISTS observatory_capture (
 capture_id TEXT PRIMARY KEY,
 captured_at TEXT NOT NULL CHECK(julianday(captured_at) IS NOT NULL),
 content_sha256 TEXT NOT NULL CHECK(length(content_sha256)=64),
 evidence_status TEXT NOT NULL,
 description TEXT NOT NULL
) STRICT;
CREATE TABLE IF NOT EXISTS observatory_geography (
 geography_id TEXT PRIMARY KEY,
 name TEXT NOT NULL,
 level TEXT NOT NULL,
 parent_id TEXT REFERENCES observatory_geography(geography_id) DEFERRABLE INITIALLY DEFERRED,
 code TEXT,
 boundary_vintage TEXT,
 CHECK(parent_id IS NULL OR parent_id != geography_id)
) STRICT;
CREATE TABLE IF NOT EXISTS observatory_study (
 study_id TEXT PRIMARY KEY,
 source_id TEXT NOT NULL REFERENCES observatory_source,
 capture_id TEXT NOT NULL REFERENCES observatory_capture,
 geography_id TEXT NOT NULL REFERENCES observatory_geography,
 population TEXT NOT NULL CHECK(length(population)>0),
 reference_start TEXT NOT NULL CHECK(date(reference_start) IS NOT NULL),
 reference_end TEXT NOT NULL CHECK(date(reference_end) IS NOT NULL),
 published_on TEXT CHECK(published_on IS NULL OR date(published_on) IS NOT NULL),
 available_at TEXT NOT NULL CHECK(julianday(available_at) IS NOT NULL),
 availability_basis TEXT NOT NULL,
 sample_size INTEGER CHECK(sample_size IS NULL OR sample_size>0),
 dependence_cluster TEXT NOT NULL,
 design TEXT NOT NULL,
 notes TEXT NOT NULL,
 CHECK(reference_start<=reference_end),
 CHECK(julianday(reference_end)<=julianday(available_at)),
 CHECK(published_on IS NULL OR julianday(published_on)<=julianday(available_at))
) STRICT;
CREATE TABLE IF NOT EXISTS observatory_observation (
 observation_id TEXT PRIMARY KEY,
 study_id TEXT NOT NULL REFERENCES observatory_study,
 series TEXT NOT NULL,
 value REAL NOT NULL CHECK(value > -1e308 AND value < 1e308),
 unit TEXT NOT NULL CHECK(unit IN ('percent','percent_change','votes','persons','index_points','USD_per_gallon','USD_billion')),
 uncertainty_json TEXT CHECK(uncertainty_json IS NULL OR json_valid(uncertainty_json)),
 notes TEXT NOT NULL,
 UNIQUE(study_id,series),
 CHECK(unit!='percent' OR (value>=0 AND value<=100)),
 CHECK(unit!='votes' OR (value>=0 AND value=CAST(value AS INTEGER))),
 CHECK(unit NOT IN ('USD_per_gallon','USD_billion') OR value>=0)
) STRICT;
CREATE INDEX IF NOT EXISTS observatory_study_availability ON observatory_study(available_at);
CREATE INDEX IF NOT EXISTS observatory_study_geography ON observatory_study(geography_id,population,reference_end);
CREATE TABLE IF NOT EXISTS observatory_contrast (
 contrast_id TEXT PRIMARY KEY,
 left_id TEXT NOT NULL REFERENCES observatory_observation,
 right_id TEXT NOT NULL REFERENCES observatory_observation,
 unit TEXT NOT NULL,
 interpretation TEXT NOT NULL
) STRICT;
CREATE TABLE IF NOT EXISTS observatory_quarantine (
 quarantine_id TEXT PRIMARY KEY,
 source_id TEXT NOT NULL REFERENCES observatory_source,
 reason TEXT NOT NULL,
 observed_at TEXT NOT NULL,
 resolution TEXT
) STRICT;
CREATE VIEW IF NOT EXISTS observatory_differences AS
 SELECT c.contrast_id, a.value-b.value AS difference, c.unit,
        c.interpretation, sa.available_at AS left_available_at,
        sb.available_at AS right_available_at
 FROM observatory_contrast AS c
 JOIN observatory_observation AS a ON a.observation_id=c.left_id
 JOIN observatory_observation AS b ON b.observation_id=c.right_id
 JOIN observatory_study AS sa ON sa.study_id=a.study_id
 JOIN observatory_study AS sb ON sb.study_id=b.study_id;
-- Query with bound cutoff on BOTH study availabilities. This view alone is not
-- an as-of selector. Preserve all releases; do not UPDATE away older vintages.
COMMIT;

