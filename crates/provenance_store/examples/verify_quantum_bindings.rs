//! Replay finite retained observables without importing a quantum SDK.
use anyhow::{Context, Result, ensure};
use provenance_store::quantum_bindings::QuantumBindingManifest;
use std::path::PathBuf;
fn main() -> Result<()> {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    ensure!(
        arguments.len() == 2,
        "usage: verify_quantum_bindings MANIFEST REPOSITORY_ROOT"
    );
    let manifest = QuantumBindingManifest::load(&PathBuf::from(&arguments[0]))
        .context("load quantum bindings")?;
    let report = manifest
        .validate(&PathBuf::from(&arguments[1]))
        .context("validate quantum bindings")?;
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
