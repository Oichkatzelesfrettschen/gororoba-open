// SPDX-License-Identifier: MIT
//! Audit curated political observations without inferring unmeasured local opinion.
use anyhow::{Context, Result, ensure};
use chrono::{DateTime, NaiveDate, Utc};
use clap::Parser;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{collections::{BTreeMap, BTreeSet}, fs, path::PathBuf};

#[derive(Parser)]
struct Args {
    /// Directory containing sources.json and pilot.json.
    #[arg(long)]
    bundle: PathBuf,
    /// RFC3339 availability cutoff; reference dates alone never admit a record.
    #[arg(long)]
    cutoff: DateTime<Utc>,
    /// New JSON report path. Existing reports are never overwritten.
    #[arg(long)]
    report: PathBuf,
}

#[derive(Deserialize)]
struct Catalog {
    sources: Vec<Source>,
}
#[derive(Deserialize)]
struct Source {
    id: String,
    url: String,
    domain: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Geography {
    id: String,
    name: String,
    level: String,
    parent: Option<String>,
    code: Option<String>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Study {
    id: String,
    source_id: String,
    geography_id: String,
    population: String,
    reference_start: NaiveDate,
    reference_end: NaiveDate,
    sample_size: Option<u64>,
    published_on: Option<NaiveDate>,
    available_at: DateTime<Utc>,
    availability_basis: String,
    dependence_cluster: String,
    design: String,
    notes: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Observation {
    id: String,
    study_id: String,
    series: String,
    value: f64,
    unit: String,
    uncertainty: Option<Value>,
    notes: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Contrast {
    id: String,
    left_id: String,
    right_id: String,
    unit: String,
    interpretation: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Bundle {
    spdx_license_identifier: String,
    schema_version: u32,
    captured_at: DateTime<Utc>,
    evidence_status: String,
    geographies: Vec<Geography>,
    studies: Vec<Study>,
    observations: Vec<Observation>,
    contrasts: Vec<Contrast>,
}
#[derive(Serialize)]
struct Difference<'a> {
    id: &'a str,
    value: Option<f64>,
    unit: &'a str,
    status: &'a str,
    interpretation: &'a str,
}

/// Reject duplicate identifiers rather than silently overwriting them.
fn unique<'a>(kind: &str, ids: impl Iterator<Item = &'a str>) -> Result<()> {
    let mut seen = BTreeSet::new();
    for id in ids {
        ensure!(!id.trim().is_empty(), "empty {kind} identifier");
        ensure!(seen.insert(id), "duplicate {kind}: {id}");
    }
    Ok(())
}

/// Check semantics before constructing any report. No statistical model is fitted.
fn validate(bundle: &Bundle, catalog: &Catalog) -> Result<()> {
    ensure!(bundle.schema_version == 1, "unsupported bundle schema");
    ensure!(!bundle.spdx_license_identifier.is_empty(), "missing license");
    unique("source", catalog.sources.iter().map(|s| s.id.as_str()))?;
    unique("geography", bundle.geographies.iter().map(|g| g.id.as_str()))?;
    unique("study", bundle.studies.iter().map(|s| s.id.as_str()))?;
    unique("observation", bundle.observations.iter().map(|o| o.id.as_str()))?;
    unique("contrast", bundle.contrasts.iter().map(|c| c.id.as_str()))?;
    let sources: BTreeMap<_, _> = catalog.sources.iter().map(|s| (s.id.as_str(), s)).collect();
    for source in &catalog.sources {
        ensure!(source.url.starts_with("https://"), "non-HTTPS source: {}", source.id);
        ensure!(!source.domain.is_empty(), "missing source domain");
    }
    let geographies: BTreeMap<_, _> =
        bundle.geographies.iter().map(|g| (g.id.as_str(), g)).collect();
    for geography in &bundle.geographies {
        ensure!(!geography.name.is_empty() && !geography.level.is_empty(), "missing geography metadata");
        if let Some(code) = &geography.code {
            ensure!(!code.is_empty(), "empty geographic code");
        }
        let mut seen = BTreeSet::new();
        let mut current = Some(&geography.id);
        while let Some(id) = current {
            ensure!(seen.insert(id), "geography parent cycle at {id}");
            let node = geographies.get(id.as_str()).context("unknown geography parent")?;
            current = node.parent.as_ref();
        }
    }
    let studies: BTreeMap<_, _> = bundle.studies.iter().map(|s| (s.id.as_str(), s)).collect();
    for study in &bundle.studies {
        ensure!(sources.contains_key(study.source_id.as_str()), "unknown source in {}", study.id);
        ensure!(geographies.contains_key(study.geography_id.as_str()), "unknown study geography");
        ensure!(study.reference_start <= study.reference_end, "reversed reference interval");
        ensure!(study.reference_end <= study.available_at.date_naive(), "reference after availability");
        ensure!(study.available_at <= bundle.captured_at, "availability after capture");
        if let Some(date) = study.published_on {
            ensure!(date <= study.available_at.date_naive(), "publication after availability");
        }
        ensure!(study.sample_size != Some(0), "zero sample size is not missing");
        ensure!(!study.population.is_empty() && !study.dependence_cluster.is_empty(), "missing population or dependence");
        ensure!(!study.availability_basis.is_empty() && !study.design.is_empty(), "missing measurement metadata");
        // Notes are retained in the source bundle; empty notes do not imply missing measurements.
        let _ = &study.notes;
    }
    let mut measurement_keys = BTreeSet::new();
    for observation in &bundle.observations {
        ensure!(studies.contains_key(observation.study_id.as_str()), "unknown observation study");
        ensure!(observation.value.is_finite(), "non-finite observation");
        ensure!(!observation.series.is_empty() && !observation.unit.is_empty(), "missing series or units");
        ensure!(measurement_keys.insert((&observation.study_id, &observation.series)), "duplicate study/series");
        match observation.unit.as_str() {
            "percent" => ensure!((0.0..=100.0).contains(&observation.value), "percentage outside [0,100]"),
            "votes" => ensure!(observation.value >= 0.0 && observation.value.fract() == 0.0, "invalid vote count"),
            "USD_per_gallon" | "USD_billion" => ensure!(observation.value >= 0.0, "negative monetary level"),
            "persons" | "index_points" | "percent_change" => {}
            _ => anyhow::bail!("unregistered unit: {}", observation.unit),
        }
        ensure!(observation.uncertainty.is_none(), "pilot v1 does not parse uncertainty: use notes until a typed schema is added");
        let _ = &observation.notes;
    }
    let observations: BTreeMap<_, _> = bundle.observations.iter().map(|o| (o.id.as_str(), o)).collect();
    for contrast in &bundle.contrasts {
        let a = observations.get(contrast.left_id.as_str()).context("missing contrast left")?;
        let b = observations.get(contrast.right_id.as_str()).context("missing contrast right")?;
        ensure!(a.unit == b.unit, "incompatible contrast inputs");
        let expected = if matches!(a.unit.as_str(), "percent" | "percent_change") { "percentage_points" } else { &a.unit };
        ensure!(contrast.unit == expected, "incorrect difference units");
        ensure!(!contrast.interpretation.is_empty(), "missing contrast interpretation");
    }
    Ok(())
}

/// Filter by first-known availability, not field date. Complexity is O(n log n).
fn audit(bundle: &Bundle, catalog: &Catalog, cutoff: DateTime<Utc>) -> Result<Value> {
    validate(bundle, catalog)?;
    let sources: BTreeMap<_, _> = catalog.sources.iter().map(|s| (s.id.as_str(), s)).collect();
    let studies: BTreeMap<_, _> = bundle.studies.iter().map(|s| (s.id.as_str(), s)).collect();
    let admitted: BTreeMap<_, _> = bundle.observations.iter().filter(|o| {
        studies.get(o.study_id.as_str()).is_some_and(|s| s.available_at <= cutoff)
    }).map(|o| (o.id.as_str(), o)).collect();
    let mut by_geography = BTreeMap::<&str, usize>::new();
    let mut by_domain = BTreeMap::<&str, usize>::new();
    let mut admitted_studies = BTreeSet::new();
    let mut observed_sources = BTreeSet::new();
    for observation in admitted.values() {
        let study = studies.get(observation.study_id.as_str()).context("missing validated study")?;
        let source = sources.get(study.source_id.as_str()).context("missing validated source")?;
        *by_geography.entry(&study.geography_id).or_default() += 1;
        *by_domain.entry(&source.domain).or_default() += 1;
        admitted_studies.insert(&study.id);
        observed_sources.insert(&source.id);
    }
    let contrasts: Vec<_> = bundle.contrasts.iter().map(|contrast| {
        let value = admitted.get(contrast.left_id.as_str()).zip(admitted.get(contrast.right_id.as_str()))
            .map(|(a, b)| a.value - b.value);
        Difference {
            id: &contrast.id, value, unit: &contrast.unit,
            status: if value.is_some() { "descriptive_arithmetic_only" } else { "unavailable_at_cutoff" },
            interpretation: &contrast.interpretation,
        }
    }).collect();
    Ok(json!({
        "schema_version": 1,
        "evidence_status": bundle.evidence_status,
        "cutoff": cutoff,
        "captured_at": bundle.captured_at,
        "catalog_sources": catalog.sources.len(),
        "sources_with_admitted_observations": observed_sources.len(),
        "admitted_studies": admitted_studies.len(),
        "admitted_observations": admitted.len(),
        "excluded_not_available": bundle.observations.len() - admitted.len(),
        "observation_counts_by_geography": by_geography,
        "observation_counts_by_domain": by_domain,
        "contrasts": contrasts,
        "model_status": "not_fitted",
        "forecast": null,
        "political_32d_diagnostic": null,
        "quantum_advantage": null,
        "litigation_success_rate": null,
        "limitations": [
            "Curated summary extraction, not bulk source ingestion or a representative panel.",
            "No covariance or confidence interval is inferred from rounded toplines.",
            "Related questions and nested geographies are not independent samples.",
            "Unknown sample sizes, original vintages and local measurements remain unknown."
        ]
    }))
}

fn main() -> Result<()> {
    let args = Args::parse();
    let catalog_bytes = fs::read(args.bundle.join("sources.json")).context("read source catalog")?;
    let bundle_bytes = fs::read(args.bundle.join("pilot.json")).context("read observation bundle")?;
    let catalog: Catalog = serde_json::from_slice(&catalog_bytes).context("parse source catalog")?;
    let bundle: Bundle = serde_json::from_slice(&bundle_bytes).context("parse observation bundle")?;
    let mut report = audit(&bundle, &catalog, args.cutoff)?;
    report["input_sha256"] = json!({
        "sources": format!("{:x}", Sha256::digest(&catalog_bytes)),
        "pilot": format!("{:x}", Sha256::digest(&bundle_bytes)),
    });
    let mut file = fs::OpenOptions::new().write(true).create_new(true).open(&args.report)
        .context("create new report; existing reports are never overwritten")?;
    serde_json::to_writer_pretty(&mut file, &report).context("write report")?;
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn duplicate_identifiers_are_rejected() {
        assert!(unique("source", ["eia_gas26", "eia_gas26"].into_iter()).is_err());
    }

    #[test]
    fn blank_identifiers_are_rejected() {
        assert!(unique("source", [" "].into_iter()).is_err());
    }

    #[test]
    fn distinct_identifiers_are_accepted() {
        assert!(unique("source", ["eia_gas26", "ppic_oct26"].into_iter()).is_ok());
    }

    // EIA published values are software fixtures, not model-performance evidence.
    fn fixture() -> Result<(Bundle, Catalog)> {
        let catalog = Catalog { sources: vec![Source {
            id: "eia_gas26".into(), url: "https://www.eia.gov/petroleum/gasdiesel/".into(),
            domain: "energy".into(),
        }] };
        let bundle = serde_json::from_value(json!({
            "spdx_license_identifier": "GPL-2.0-or-later", "schema_version": 1,
            "captured_at": "2026-11-03T18:59:14.557Z",
            "evidence_status": "measured_price_software_fixture",
            "geographies": [{"id": "united_states", "name": "United States",
                "level": "country", "parent": null, "code": "US"}],
            "studies": [{"id": "eia_week", "source_id": "eia_gas26",
                "geography_id": "united_states", "population": "retail_regular_gasoline",
                "reference_start": "2026-11-02", "reference_end": "2026-11-02",
                "sample_size": null, "published_on": "2026-11-03",
                "available_at": "2026-11-03T18:59:14.557Z",
                "availability_basis": "observed_by_retrieval_not_original_vintage",
                "dependence_cluster": "eia_week", "design": "weekly_price_survey", "notes": ""}],
            "observations": [{"id": "gas_us", "study_id": "eia_week",
                "series": "regular_gasoline_price", "value": 4.153,
                "unit": "USD_per_gallon", "uncertainty": null, "notes": ""}],
            "contrasts": []
        }))?;
        Ok((bundle, catalog))
    }

    #[test]
    fn reference_date_does_not_admit_later_retrieval() -> Result<()> {
        let (bundle, catalog) = fixture()?;
        let report = audit(&bundle, &catalog, "2026-11-03T18:00:00Z".parse()?)?;
        assert_eq!(report["admitted_observations"], 0);
        assert_eq!(report["excluded_not_available"], 1);
        Ok(())
    }

    #[test]
    fn observation_is_admitted_at_exact_availability() -> Result<()> {
        let (bundle, catalog) = fixture()?;
        let report = audit(&bundle, &catalog, bundle.captured_at)?;
        assert_eq!(report["admitted_observations"], 1);
        assert!(report["forecast"].is_null());
        Ok(())
    }

    #[test]
    fn missing_source_is_rejected() -> Result<()> {
        let (mut bundle, catalog) = fixture()?;
        bundle.studies[0].source_id = "not_acquired".into();
        assert!(validate(&bundle, &catalog).is_err());
        Ok(())
    }

    #[test]
    fn missing_parent_and_parent_cycles_are_rejected() -> Result<()> {
        let (mut bundle, catalog) = fixture()?;
        bundle.geographies[0].parent = Some("missing".into());
        assert!(validate(&bundle, &catalog).is_err());
        bundle.geographies[0].parent = Some("united_states".into());
        assert!(validate(&bundle, &catalog).is_err());
        Ok(())
    }

    #[test]
    fn non_finite_and_negative_price_are_rejected() -> Result<()> {
        let (mut bundle, catalog) = fixture()?;
        bundle.observations[0].value = f64::NAN;
        assert!(validate(&bundle, &catalog).is_err());
        bundle.observations[0].value = -4.153;
        assert!(validate(&bundle, &catalog).is_err());
        Ok(())
    }

    #[test]
    fn percent_change_allows_declines_but_share_is_bounded() -> Result<()> {
        let (mut bundle, catalog) = fixture()?;
        bundle.observations[0].unit = "percent_change".into();
        bundle.observations[0].value = -0.116;
        assert!(validate(&bundle, &catalog).is_ok());
        bundle.observations[0].unit = "percent".into();
        assert!(validate(&bundle, &catalog).is_err());
        Ok(())
    }

    #[test]
    fn zero_sample_size_and_future_reference_are_rejected() -> Result<()> {
        let (mut bundle, catalog) = fixture()?;
        bundle.studies[0].sample_size = Some(0);
        assert!(validate(&bundle, &catalog).is_err());
        bundle.studies[0].sample_size = None;
        bundle.studies[0].reference_end = "2026-11-04".parse()?;
        assert!(validate(&bundle, &catalog).is_err());
        Ok(())
    }

    #[test]
    fn contrast_units_and_cutoff_are_enforced() -> Result<()> {
        let (mut bundle, catalog) = fixture()?;
        bundle.contrasts.push(Contrast { id: "self_difference".into(),
            left_id: "gas_us".into(), right_id: "gas_us".into(),
            unit: "percentage_points".into(), interpretation: "Unit rejection check".into() });
        assert!(validate(&bundle, &catalog).is_err());
        bundle.contrasts[0].unit = "USD_per_gallon".into();
        let report = audit(&bundle, &catalog, bundle.captured_at)?;
        assert_eq!(report["contrasts"][0]["value"], 0.0);
        let unavailable = audit(&bundle, &catalog, "2026-11-03T18:00:00Z".parse()?)?;
        assert!(unavailable["contrasts"][0]["value"].is_null());
        Ok(())
    }
}

