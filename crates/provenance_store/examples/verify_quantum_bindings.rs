//! Replay finite retained observables without importing a quantum SDK.
//!
//! The manifest and the sources it binds live in the proof tree of the
//! gororoba-math checkout that `GOROROBA_MATH` names.
use anyhow::{Context, Result, ensure};
use provenance_store::{ProofTree, quantum_bindings::QuantumBindingManifest};
use std::path::PathBuf;
fn main() -> Result<()> {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    ensure!(
        arguments.len() == 1,
        "usage: GOROROBA_MATH=CHECKOUT verify_quantum_bindings MANIFEST"
    );
    let tree = ProofTree::from_environment().context("resolve the proof tree")?;
    let manifest = QuantumBindingManifest::load(&PathBuf::from(&arguments[0]))
        .context("load quantum bindings")?;
    let report = manifest
        .validate(&tree)
        .context("validate quantum bindings")?;
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
