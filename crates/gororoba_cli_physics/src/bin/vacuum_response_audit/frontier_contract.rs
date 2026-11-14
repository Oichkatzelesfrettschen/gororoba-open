//! Exact coverage and dependency checks for the vacuum integration ledger.
//! Declaration lookup measures source linkage; Rocq owns theorem execution.
use serde::Deserialize;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path},
};

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Contract {
    title: String,
    source_ledger: String,
    leaf_count: usize,
    scope: String,
    proof_boundary: String,
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Leaf {
    id: String,
    disposition: String,
    formal: Vec<String>,
    implementation: Vec<String>,
    dependencies: Vec<String>,
    physical_validation: String,
    next_gate: String,
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Ledger {
    contract: Contract,
    leaf: Vec<Leaf>,
}

/// Checks one evidence reference. An implementation reference names a file of
/// this repository below `root`. A formal reference names a theory of the proof
/// tree by its recorded `proofs/theories/<file>.v::<declaration>` locator:
/// its shape is checked always, and the file, the declaration and the project
/// listing are checked when `tree` holds the gororoba-math proof tree.
fn validate_reference(
    root: &Path,
    tree: Option<&repo_root::ProofTree>,
    reference: &str,
    formal: bool,
) -> Result<(), String> {
    let (file, symbol) = reference
        .split_once("::")
        .map_or((reference, None), |(file, symbol)| (file, Some(symbol)));
    let path = Path::new(file);
    if path
        .components()
        .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(format!(
            "reference escapes its relative evidence boundary: {reference}"
        ));
    }
    if formal
        && (!file.starts_with("proofs/theories/") || !file.ends_with(".v") || symbol.is_none())
    {
        return Err(format!(
            "formal reference requires a theory and declaration: {reference}"
        ));
    }
    if let Some(symbol) = symbol
        && (symbol.is_empty()
            || !symbol
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'))
    {
        return Err(format!("malformed declaration in {reference}"));
    }
    let located = if formal {
        match tree {
            Some(tree) => tree
                .locate(file)
                .ok_or_else(|| format!("{reference}: locator lies outside the proof tree"))?,
            None => return Ok(()),
        }
    } else {
        root.join(path)
    };
    let metadata =
        fs::symlink_metadata(&located).map_err(|error| format!("{reference}: {error}"))?;
    if !metadata.is_file() {
        return Err(format!(
            "reference is not a regular evidence file: {reference}"
        ));
    }
    if let Some(symbol) = symbol {
        let source = fs::read_to_string(&located).map_err(|error| error.to_string())?;
        let prefixes: &[&str] = if formal {
            &["Theorem ", "Lemma ", "Corollary "]
        } else {
            &["fn "]
        };
        let exists = prefixes.iter().any(|prefix| {
            source
                .match_indices(&format!("{prefix}{symbol}"))
                .any(|(offset, matched)| {
                    source[offset + matched.len()..]
                        .chars()
                        .next()
                        .is_some_and(|character| {
                            character.is_whitespace() || matches!(character, ':' | '(' | '<')
                        })
                })
        });
        if !exists {
            return Err(format!("missing declaration: {reference}"));
        }
        if let Some(tree) = tree.filter(|_| formal) {
            let project =
                fs::read_to_string(tree.project_file()).map_err(|error| error.to_string())?;
            if !project
                .lines()
                .any(|line| Some(line) == file.strip_prefix("proofs/"))
            {
                return Err(format!(
                    "formal source is outside the compiled corpus: {reference}"
                ));
            }
        }
    }
    Ok(())
}

fn visit<'a>(
    id: &'a str,
    rows: &BTreeMap<&'a str, &'a Leaf>,
    visiting: &mut BTreeSet<&'a str>,
    complete: &mut BTreeSet<&'a str>,
) -> Result<(), String> {
    if complete.contains(id) {
        return Ok(());
    }
    if !visiting.insert(id) {
        return Err(format!("cyclic integration dependency at {id}"));
    }
    let row = rows
        .get(id)
        .ok_or_else(|| format!("unknown integration dependency {id}"))?;
    for dependency in &row.dependencies {
        visit(dependency, rows, visiting, complete)?;
    }
    visiting.remove(id);
    complete.insert(id);
    Ok(())
}

fn validate(
    root: &Path,
    tree: Option<&repo_root::ProofTree>,
    expected: &BTreeSet<String>,
    ledger: &Ledger,
) -> Result<(), String> {
    let contract = &ledger.contract;
    if contract.source_ledger != "plans/vacuum_energy_falsification.toml"
        || contract.leaf_count != expected.len()
        || [&contract.title, &contract.scope, &contract.proof_boundary]
            .iter()
            .any(|value| value.trim().is_empty())
    {
        return Err("integration contract denominator or boundary is inconsistent".to_owned());
    }
    let actual: BTreeSet<_> = ledger.leaf.iter().map(|leaf| leaf.id.clone()).collect();
    if actual != *expected || ledger.leaf.len() != actual.len() {
        return Err("integration ledger must cover each original leaf exactly once".to_owned());
    }
    let dispositions = [
        "formal_model",
        "formal_counterexample",
        "numerical_counterexample",
        "source_reconciled",
        "source_open",
        "measurement_open",
        "implementation_repaired",
        "model_composed_measurement_open",
        "analytic_counterexample_recorded",
        "definition_open",
        "source_reconciled_model_open",
    ];
    for leaf in &ledger.leaf {
        if !dispositions.contains(&leaf.disposition.as_str())
            || leaf.next_gate.trim().is_empty()
            || leaf.physical_validation != "unperformed"
            || leaf.implementation.is_empty()
        {
            return Err(format!(
                "{} lacks an admissible evidence disposition, implementation link or remaining gate",
                leaf.id
            ));
        }
        if leaf.disposition.starts_with("formal_") && leaf.formal.is_empty() {
            return Err(format!(
                "{} claims formal coverage without a declaration",
                leaf.id
            ));
        }
        for reference in &leaf.formal {
            validate_reference(root, tree, reference, true)?;
        }
        for reference in &leaf.implementation {
            validate_reference(root, tree, reference, false)?;
        }
        if leaf.dependencies.iter().collect::<BTreeSet<_>>().len() != leaf.dependencies.len() {
            return Err(format!("{} repeats a dependency", leaf.id));
        }
    }
    let rows: BTreeMap<_, _> = ledger
        .leaf
        .iter()
        .map(|row| (row.id.as_str(), row))
        .collect();
    let mut complete = BTreeSet::new();
    for id in rows.keys() {
        visit(id, &rows, &mut BTreeSet::new(), &mut complete)?;
    }
    Ok(())
}

fn fixture() -> (std::path::PathBuf, BTreeSet<String>, Ledger) {
    let root = repo_root::discover().expect("run inside the workspace or set GOROROBA_REPO_ROOT");
    let source: toml::Value = toml::from_str(
        &fs::read_to_string(root.join("plans/vacuum_energy_falsification.toml")).unwrap(),
    )
    .unwrap();
    let original_rows = source["leaf"].as_array().unwrap();
    let expected: BTreeSet<_> = original_rows
        .iter()
        .map(|row| row["id"].as_str().unwrap().to_owned())
        .collect();
    assert_eq!(
        expected.len(),
        original_rows.len(),
        "original ledger IDs are unique"
    );
    let ledger = toml::from_str(
        &fs::read_to_string(root.join("plans/vacuum_integration_contract.toml")).unwrap(),
    )
    .unwrap();
    (root, expected, ledger)
}

/// The gororoba-math proof tree that GOROROBA_MATH names; the tests that read
/// it are ignored by default and run with `--include-ignored`.
fn proof_tree() -> repo_root::ProofTree {
    repo_root::ProofTree::from_environment().expect("GOROROBA_MATH names a gororoba-math checkout")
}

#[test]
fn every_original_leaf_has_one_checked_integration_and_acyclic_dependencies() {
    // Without the proof tree the formal references are checked for shape only.
    let (root, expected, ledger) = fixture();
    validate(&root, None, &expected, &ledger).unwrap();
}

#[test]
#[ignore = "reads the gororoba-math proof tree; set GOROROBA_MATH and run with --include-ignored"]
fn every_formal_reference_resolves_in_the_proof_tree() {
    let (root, expected, ledger) = fixture();
    validate(&root, Some(&proof_tree()), &expected, &ledger).unwrap();
}

#[test]
fn missing_duplicate_or_invented_leaf_rejects() {
    let (root, expected, ledger) = fixture();
    let mut missing = ledger.clone();
    missing.leaf.pop();
    assert!(validate(&root, None, &expected, &missing).is_err());
    let mut duplicate = ledger.clone();
    duplicate.leaf.push(duplicate.leaf[0].clone());
    assert!(validate(&root, None, &expected, &duplicate).is_err());
    let mut invented = ledger.clone();
    invented.leaf[0].id = "unregistered-inference".to_owned();
    assert!(validate(&root, None, &expected, &invented).is_err());
}

#[test]
fn cycles_unknown_dependencies_and_unearned_physical_closure_reject() {
    let (root, expected, ledger) = fixture();
    let mut cycle = ledger.clone();
    let first_id = cycle.leaf[0].id.clone();
    cycle.leaf[0].dependencies.push(first_id);
    assert!(validate(&root, None, &expected, &cycle).is_err());
    let mut unknown = ledger.clone();
    unknown.leaf[0].dependencies.push("unknown".to_owned());
    assert!(validate(&root, None, &expected, &unknown).is_err());
    let mut closed = ledger.clone();
    closed.leaf[0].physical_validation = "established".to_owned();
    assert!(validate(&root, None, &expected, &closed).is_err());
    let mut empty = ledger.clone();
    empty.leaf[0].next_gate.clear();
    assert!(validate(&root, None, &expected, &empty).is_err());
}

#[test]
fn unproved_leaves_and_path_escapes_reject() {
    let (root, expected, ledger) = fixture();
    let mut unproved = ledger.clone();
    unproved.leaf[0].formal.clear();
    assert!(validate(&root, None, &expected, &unproved).is_err());
    assert!(validate_reference(&root, None, "../AGENTS.md", false).is_err());
    assert!(validate_reference(&root, None, "proofs/../AGENTS.md::x", true).is_err());
    assert!(validate_reference(&root, None, "proofs/verified/Other.v::x", true).is_err());
}

#[test]
#[ignore = "reads the gororoba-math proof tree; set GOROROBA_MATH and run with --include-ignored"]
fn stale_declarations_and_missing_theories_reject_against_the_proof_tree() {
    let (root, expected, ledger) = fixture();
    let tree = proof_tree();
    let mut stale = ledger.clone();
    stale.leaf[0].formal[0].push_str("_invented");
    assert!(validate(&root, Some(&tree), &expected, &stale).is_err());
    assert!(
        validate_reference(
            &root,
            Some(&tree),
            "proofs/theories/Absent.v::invented",
            true
        )
        .is_err()
    );
}
