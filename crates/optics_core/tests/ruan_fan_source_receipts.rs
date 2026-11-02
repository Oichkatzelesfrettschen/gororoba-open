//! Declaration shape of the legacy source-hash constant in the Ruan and Fan reproduction runner.

use std::error::Error;

#[test]
fn legacy_source_hash_declaration_is_not_a_sha256_digest() -> Result<(), Box<dyn Error>> {
    let runner = include_str!("../src/bin/p2b_ruan_fan_reproduction.rs");
    let legacy = runner
        .lines()
        .find(|line| line.starts_with("const SOURCE_TEX_SHA256:"))
        .and_then(|line| line.split('"').nth(1))
        .ok_or("historical source-hash declaration missing")?;
    assert_eq!(legacy.len(), 61);
    Ok(())
}
