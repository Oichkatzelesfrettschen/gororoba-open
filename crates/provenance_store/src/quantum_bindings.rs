//! Offline byte-identity and register-decoder contracts for quantum observables.
//!
//! The validator reconstructs finite recorded statistics. It neither decodes QPY
//! semantics nor establishes calibration, stationarity, or shot independence.
use anyhow::{Context, Result, bail, ensure};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path},
};

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct QuantumBindingManifest {
    pub schema_version: u32,
    pub source_repository: String,
    pub source_commit: String,
    pub semantic_boundary: String,
    pub assets: Vec<QuantumAsset>,
    pub theorems: Vec<QuantumTheoremBinding>,
    pub decoders: Vec<QuantumDecoder>,
    pub terminal: TerminalFixture,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct QuantumAsset {
    pub path: String,
    pub sha256: String,
    pub source_path: String,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct QuantumTheoremBinding {
    pub source: String,
    pub sha256: String,
    pub declaration: String,
    pub basis: String,
    pub normalization: String,
    pub execution: String,
    pub not_applicable_reason: String,
    pub premises: Vec<String>,
    pub decoder_members: Vec<String>,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct QuantumDecoder {
    pub member: String,
    pub record: String,
    pub qpy: String,
    pub raw: String,
    pub pub_name: String,
    pub registers_by_replica: Vec<Vec<String>>,
    pub width: usize,
    pub shots_per_replica: usize,
    pub bit_order: String,
    pub recipe: DecoderRecipe,
    pub basis_convention: String,
    pub observable_formula: String,
    pub normalization: String,
    pub numerator: i64,
    pub denominator: usize,
}
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DecoderRecipe {
    ProbabilityZero,
    TerminalBitOne,
    BranchSignedParity,
}
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TerminalFixture {
    pub covered_means: Vec<CoveredMean>,
    pub selected_test_means: Vec<SelectedTestMean>,
    pub means: u32,
    pub alpha_numerator: u32,
    pub alpha_denominator: u32,
    pub radius_numerator: u32,
    pub radius_denominator: u32,
    pub hardware_numerators: [i64; 2],
    pub replay_numerators: [i64; 2],
    pub shots: usize,
    pub margin_numerator: i64,
    pub margin_denominator: i64,
}
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct CoveredMean {
    pub member: String,
    pub pub_name: String,
    pub data_source: MeanSource,
}
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub enum MeanSource {
    Hardware,
    Replay,
}
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct SelectedTestMean {
    pub theorem_index: usize,
    pub role: String,
    pub mean: CoveredMean,
}
#[derive(Debug, Serialize)]
pub struct QuantumBindingReport {
    pub verified_assets: usize,
    pub verified_theorem_sources: usize,
    pub verified_theorem_declarations: usize,
    pub decoded_members: usize,
    pub signed_coherence: BTreeMap<String, [f64; 2]>,
    pub terminal_margin: [i64; 2],
    pub physical_premises: String,
}
fn regular_bytes(root: &Path, relative: &str) -> Result<Vec<u8>> {
    let path = Path::new(relative);
    ensure!(
        !relative.is_empty()
            && path
                .components()
                .all(|part| matches!(part, Component::Normal(_))),
        "unsafe relative path: {relative}"
    );
    let mut current = root.to_path_buf();
    for part in path.components() {
        current.push(part);
        let metadata = fs::symlink_metadata(&current)
            .with_context(|| format!("inspect {}", current.display()))?;
        ensure!(
            !metadata.file_type().is_symlink(),
            "symlink in artifact path: {relative}"
        );
    }
    ensure!(
        fs::metadata(&current)?.is_file(),
        "artifact is not regular: {relative}"
    );
    Ok(fs::read(current)?)
}
fn verify_hash(bytes: &[u8], expected: &str) -> Result<()> {
    ensure!(
        expected.len() == 64
            && expected
                .bytes()
                .all(|value| value.is_ascii_digit() || (b'a'..=b'f').contains(&value)),
        "SHA256 must be lowercase hexadecimal"
    );
    ensure!(
        Sha256::digest(bytes)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
            == expected,
        "SHA256 mismatch"
    );
    Ok(())
}
fn json(bytes: &[u8]) -> Result<serde_json::Value> {
    Ok(serde_json::from_slice(bytes)?)
}
fn convention(source: &str) -> Result<(&'static str, &'static str)> {
    Ok(
        match Path::new(source)
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("")
        {
            "C881_GF2CubicMinDegree.v" => ("gf2_fixed_labels", "gf2_unit_coefficients"),
            "SedenionFoldTransport.v" => ("sedenion_lo_hi", "half_sum_half_difference"),
            "FoldAverageDescent.v" => ("qc_ordered_pair", "half_sum_half_difference"),
            "NullityTwelveQuadraticLocus.v" => (
                "real_z5_z6_z13_z16_z17_z18_z19_z20",
                "unnormalized_quadratic",
            ),
            "C014_AnnihilatorDim4.v" => ("sedenion_lo_hi", "unnormalized_product"),
            "TerminalChannelSeparation.v"
            | "TerminalChannelSeparationReal.v"
            | "TerminalChannelEmpiricalCertificate.v" => {
                ("binary_zero_one", "probability_unit_interval")
            }
            "BranchSignedCoherence.v" => ("b0_c0_a_c1_b_c2_spectator_c3", "signed_pauli_quarter"),
            "FiniteProbability.v" | "FiniteBernoulliConcentration.v" => {
                ("finite_boolean_sample_space", "probability_unit_interval")
            }
            _ => bail!("unsupported theorem source domain: {source}"),
        },
    )
}
fn required_semantics(source: &str) -> Result<(&'static str, &'static [&'static str])> {
    Ok(
        match Path::new(source)
            .file_name()
            .and_then(|name| name.to_str())
            .context("source filename missing")?
        {
            "C881_GF2CubicMinDegree.v"
            | "SedenionFoldTransport.v"
            | "FoldAverageDescent.v"
            | "NullityTwelveQuadraticLocus.v"
            | "C014_AnnihilatorDim4.v" => (
                "mathematical_only",
                &["algebraic definitions and hypotheses in the pinned source"],
            ),
            "TerminalChannelSeparation.v"
            | "TerminalChannelSeparationReal.v"
            | "TerminalChannelEmpiricalCertificate.v" => (
                "conditional_terminal_fixture",
                &[
                    "common binary stochastic channel",
                    "simultaneous coverage of all 32 means",
                    "independent Bernoulli shots within each mean; stationarity and decoder validity remain empirical assumptions",
                    "readout calibration and assignment errors; coherent gate error; device drift; crosstalk; leakage; and context-dependent noise remain empirical nuisance mechanisms, outside the common terminal channel class",
                ],
            ),
            "FiniteProbability.v" | "FiniteBernoulliConcentration.v" => (
                "conditional_terminal_fixture",
                &[
                    "common binary stochastic channel",
                    "simultaneous coverage of all 32 means",
                    "independent Bernoulli shots within each mean; stationarity and decoder validity remain empirical assumptions",
                    "readout calibration and assignment errors; coherent gate error; device drift; crosstalk; leakage; and context-dependent noise remain empirical nuisance mechanisms, outside the common terminal channel class",
                    "finite nonnegative normalized law; each within-mean centered sample sum has the declared IID Bernoulli convolution law; cross-mean dependence is unrestricted by the finite union bound",
                ],
            ),
            "BranchSignedCoherence.v" => (
                "conditional_coherence_fixture",
                &[
                    "same latent two-work-qubit state across Pauli settings within context",
                    "Born projective measurement law with X=H and Y=Sdg then H; b0=c0,a=c1,b=c2,spectator=c3",
                    "stationary within-context marginal distributions and shot independence remain empirical premises",
                    "independent first-bit assignment error is required for the (1-2*epsilon) scaling law",
                    "readout error, drift, leakage, crosstalk and coherent gate errors remain nuisance mechanisms; a C rotation alone cannot identify a physical cause",
                    "both unnormalized branch matrices are positive semidefinite and their combined trace equals one; Born-score identities alone establish neither positivity nor normalization",
                    "0<=epsilon<=1 and the physical independent assignment-error process induces the declared mix_matrix mixture; the factorization predicate is not proved to imply that mixture",
                ],
            ),
            _ => bail!("unsupported theorem semantic domain"),
        },
    )
}
impl QuantumBindingManifest {
    pub fn load(path: &Path) -> Result<Self> {
        Ok(serde_json::from_slice(&fs::read(path)?)?)
    }
    pub fn validate(&self, root: &Path) -> Result<QuantumBindingReport> {
        ensure!(self.schema_version == 1, "unsupported binding schema");
        ensure!(
            self.source_repository == "IBMQuantum"
                && self.source_commit == "a3d95ab60b25c4a6f18e5ff7c0435b4947abceb8",
            "source snapshot identity changed"
        );
        ensure!(
            self.semantic_boundary
                == "Hashes verify QPY byte identity only. Circuit semantics and physical premises remain asserted and unproved by this offline validator.",
            "semantic boundary changed"
        );
        let mut assets = BTreeMap::new();
        for asset in &self.assets {
            ensure!(
                asset.path
                    == format!(
                        "proofs/evidence/quantum_observables/frozen/{}",
                        asset.source_path
                    ),
                "frozen source locator mismatch"
            );
            let bytes = regular_bytes(root, &asset.path)?;
            verify_hash(&bytes, &asset.sha256).with_context(|| asset.path.clone())?;
            ensure!(
                assets.insert(asset.path.as_str(), bytes).is_none(),
                "duplicate artifact"
            );
        }
        let mut declarations = BTreeSet::new();
        for theorem in &self.theorems {
            ensure!(
                declarations.insert((&theorem.source, &theorem.declaration)),
                "duplicate theorem declaration"
            );
            let bytes = regular_bytes(root, &theorem.source)?;
            verify_hash(&bytes, &theorem.sha256).with_context(|| theorem.source.clone())?;
            let text = std::str::from_utf8(&bytes)?;
            ensure!(
                theorem
                    .declaration
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
                    && !theorem.declaration.is_empty(),
                "invalid declaration identifier"
            );
            ensure!(
                text.lines()
                    .any(|line| ["Theorem ", "Lemma ", "Corollary "]
                        .iter()
                        .any(|prefix| line
                            .strip_prefix(prefix)
                            .and_then(|tail| tail.strip_prefix(&theorem.declaration))
                            .is_some_and(|tail| tail.starts_with([' ', ':'])))),
                "stale theorem declaration: {}",
                theorem.declaration
            );
            let (basis, normalization) = convention(&theorem.source)?;
            ensure!(theorem.basis == basis, "basis convention changed");
            ensure!(
                theorem.normalization == normalization,
                "normalization changed"
            );
            ensure!(
                !theorem.premises.is_empty()
                    && theorem
                        .premises
                        .iter()
                        .all(|premise| !premise.trim().is_empty()),
                "explicit premises required"
            );
            let (required_execution, required_premises) = required_semantics(&theorem.source)?;
            ensure!(
                theorem.execution == required_execution,
                "theorem execution domain mismatch"
            );
            ensure!(
                theorem.premises.len() == required_premises.len()
                    && theorem
                        .premises
                        .iter()
                        .map(String::as_str)
                        .collect::<BTreeSet<_>>()
                        == required_premises.iter().copied().collect::<BTreeSet<_>>(),
                "theorem premise set mismatch"
            );
            let required_decoder_members: BTreeSet<_> = match required_execution {
                "mathematical_only" => BTreeSet::new(),
                "conditional_terminal_fixture" => {
                    ["qpe_no_feed_forward_s1", "qpe_no_feed_forward_s3"]
                        .into_iter()
                        .map(str::to_owned)
                        .collect()
                }
                "conditional_coherence_fixture" => ["immediate", "matched_idle", "measure_reset"]
                    .into_iter()
                    .flat_map(|context| {
                        ["xx", "xy", "yx", "yy"]
                            .into_iter()
                            .map(move |basis| format!("coherence_{context}_{basis}"))
                    })
                    .collect(),
                _ => bail!("unsupported execution domain"),
            };
            ensure!(
                theorem.decoder_members.len() == required_decoder_members.len()
                    && theorem
                        .decoder_members
                        .iter()
                        .cloned()
                        .collect::<BTreeSet<_>>()
                        == required_decoder_members,
                "theorem decoder domain mismatch"
            );
            match theorem.execution.as_str() {
                "mathematical_only" => ensure!(
                    !theorem.not_applicable_reason.trim().is_empty()
                        && theorem.decoder_members.is_empty(),
                    "mathematical theorem requires explicit circuit/decoder non-applicability"
                ),
                "conditional_terminal_fixture" | "conditional_coherence_fixture" => ensure!(
                    theorem.not_applicable_reason.is_empty() && !theorem.decoder_members.is_empty(),
                    "empirical binding requires decoders"
                ),
                _ => bail!("unsupported execution domain"),
            }
            for member in &theorem.decoder_members {
                ensure!(
                    self.decoders
                        .iter()
                        .any(|decoder| &decoder.member == member),
                    "unresolved theorem decoder"
                );
            }
        }
        let required_sources = [
            "proofs/verified/C881_GF2CubicMinDegree.v",
            "proofs/theories/SedenionFoldTransport.v",
            "proofs/theories/FoldAverageDescent.v",
            "proofs/theories/NullityTwelveQuadraticLocus.v",
            "proofs/verified/C014_AnnihilatorDim4.v",
            "proofs/theories/TerminalChannelSeparation.v",
            "proofs/theories/TerminalChannelSeparationReal.v",
            "proofs/theories/BranchSignedCoherence.v",
            "proofs/theories/FiniteProbability.v",
            "proofs/theories/FiniteBernoulliConcentration.v",
            "proofs/theories/TerminalChannelEmpiricalCertificate.v",
        ];
        let mut expected_declarations = BTreeSet::new();
        for source in required_sources {
            let bytes = regular_bytes(root, source)?;
            for line in std::str::from_utf8(&bytes)?.lines() {
                let line = line.trim_start();
                for prefix in ["Theorem ", "Lemma ", "Corollary "] {
                    if let Some(tail) = line.strip_prefix(prefix) {
                        let declaration: String = tail
                            .chars()
                            .take_while(|character| {
                                character.is_ascii_alphanumeric() || *character == '_'
                            })
                            .collect();
                        ensure!(!declaration.is_empty(), "unsupported declaration syntax");
                        expected_declarations.insert((source.to_owned(), declaration));
                    }
                }
            }
        }
        let actual_declarations: BTreeSet<_> = self
            .theorems
            .iter()
            .map(|theorem| (theorem.source.clone(), theorem.declaration.clone()))
            .collect();
        ensure!(
            actual_declarations == expected_declarations,
            "theorem declaration denominator mismatch"
        );
        let mut means = BTreeMap::new();
        for decoder in &self.decoders {
            ensure!(
                !means.contains_key(&decoder.member),
                "duplicate decoded member"
            );
            ensure!(
                decoder.bit_order == "little_endian_c0_rightmost",
                "bit order changed"
            );
            let expected_width = match decoder.recipe {
                DecoderRecipe::ProbabilityZero => 1,
                DecoderRecipe::TerminalBitOne => 2,
                DecoderRecipe::BranchSignedParity => 4,
            };
            ensure!(decoder.width == expected_width, "decoder width changed");
            let (basis, formula, normalization) = match decoder.recipe {
                DecoderRecipe::ProbabilityZero => (
                    "computational_c0",
                    "p0=count(c0=0)/total",
                    "aggregate_eight_replica_mean",
                ),
                DecoderRecipe::TerminalBitOne => (
                    "terminal_c1_first_c0",
                    "p1=count(c1=1)/shots",
                    "single_replica_mean",
                ),
                DecoderRecipe::BranchSignedParity => (
                    "b0_c0_a_c1_b_c2_spectator_c3;X=H;Y=Sdg_then_H",
                    "S=(-1)^(b0+a+b);C=(Sxx+Syy+i*(Sxy-Syx))/4",
                    "single_replica_signed_mean_then_quarter",
                ),
            };
            ensure!(
                decoder.basis_convention == basis,
                "decoder basis convention changed"
            );
            ensure!(
                decoder.observable_formula == formula,
                "decoder observable formula changed"
            );
            ensure!(
                decoder.normalization == normalization,
                "decoder normalization changed"
            );
            ensure!(
                decoder.shots_per_replica
                    == if decoder.recipe == DecoderRecipe::TerminalBitOne {
                        8192
                    } else {
                        2048
                    },
                "shot count changed"
            );
            let record = json(
                assets
                    .get(decoder.record.as_str())
                    .context("record absent from asset inventory")?,
            )?;
            let qpy = assets
                .get(decoder.qpy.as_str())
                .context("QPY absent from asset inventory")?;
            ensure!(qpy.starts_with(b"QISKIT"), "QPY magic mismatch");
            ensure!(
                Path::new(&decoder.record).parent() == Path::new(&decoder.qpy).parent(),
                "record/QPY run mismatch"
            );
            ensure!(
                Path::new(&decoder.raw).starts_with(
                    Path::new(&decoder.record)
                        .parent()
                        .context("record parent missing")?
                        .join("raw")
                ),
                "raw PUB run mismatch"
            );
            let raw = json(
                assets
                    .get(decoder.raw.as_str())
                    .context("raw PUB absent from asset inventory")?,
            )?;
            ensure!(
                raw["pub_name"].as_str() == Some(&decoder.pub_name),
                "raw PUB name mismatch"
            );
            let pubs = record["execution_pubs"]
                .as_array()
                .context("record execution PUBs missing")?;
            let matches: Vec<_> = pubs
                .iter()
                .filter(|pub_record| pub_record["name"].as_str() == Some(&decoder.pub_name))
                .collect();
            ensure!(matches.len() == 1, "record PUB must resolve uniquely");
            let components = matches[0]["components"]
                .as_array()
                .context("record components missing")?;
            let components: Vec<_> = components
                .iter()
                .filter(|component| component["member"].as_str() == Some(&decoder.member))
                .collect();
            ensure!(components.len() == 1, "record member must resolve uniquely");
            ensure!(
                components[0]["registers_by_replica"]
                    == serde_json::to_value(&decoder.registers_by_replica)?,
                "record decoder register mapping mismatch"
            );
            let mut registers = BTreeSet::new();
            let mut numerator = 0_i64;
            let mut denominator = 0;
            ensure!(
                !decoder.registers_by_replica.is_empty(),
                "decoder replicas missing"
            );
            for replica in &decoder.registers_by_replica {
                ensure!(
                    replica.len() == 1,
                    "one joint register required per replica"
                );
                ensure!(registers.insert(&replica[0]), "duplicate register replica");
                let register = &raw["registers"][&replica[0]];
                ensure!(
                    register["num_bits"].as_u64() == Some(decoder.width as u64),
                    "raw register width mismatch"
                );
                ensure!(
                    register["num_shots"].as_u64() == Some(decoder.shots_per_replica as u64),
                    "raw register shots mismatch"
                );
                let bitstrings = register["bitstrings"]
                    .as_array()
                    .context("raw bitstrings missing")?;
                ensure!(
                    bitstrings.len() == decoder.shots_per_replica,
                    "raw bitstring shot count mismatch"
                );
                for bitstring in bitstrings {
                    let bits = bitstring.as_str().context("bitstring must be text")?;
                    ensure!(
                        bits.len() == decoder.width
                            && bits.bytes().all(|byte| byte == b'0' || byte == b'1'),
                        "invalid bitstring width or alphabet"
                    );
                    numerator += match decoder.recipe {
                        DecoderRecipe::ProbabilityZero => i64::from(bits == "0"),
                        DecoderRecipe::TerminalBitOne => i64::from(bits.as_bytes()[0] == b'1'),
                        DecoderRecipe::BranchSignedParity => {
                            if bits
                                .bytes()
                                .rev()
                                .take(3)
                                .filter(|byte| *byte == b'1')
                                .count()
                                % 2
                                == 0
                            {
                                1
                            } else {
                                -1
                            }
                        }
                    };
                    denominator += 1;
                }
            }
            ensure!(
                numerator == decoder.numerator && denominator == decoder.denominator,
                "reconstructed observable mismatch: {}",
                decoder.member
            );
            means.insert(decoder.member.clone(), (numerator, denominator));
        }
        for (member, expected) in [
            ("design_b_dark_1_10_4_15", 2979),
            ("design_b_bright_1_10_4_15", 13573),
        ] {
            ensure!(
                means.get(member) == Some(&(expected, 16384)),
                "fringe aggregate fixture mismatch"
            );
        }
        let analysis_path = self
            .assets
            .iter()
            .find(|asset| asset.path.ends_with("/coherence-analysis.json"))
            .context("coherence analysis missing")?;
        let analysis = json(&assets[analysis_path.path.as_str()])?;
        let mut signed_coherence = BTreeMap::new();
        for context in ["immediate", "matched_idle", "measure_reset"] {
            let value = |basis: &str| -> Result<f64> {
                let (numerator, denominator) = means
                    .get(&format!("coherence_{context}_{basis}"))
                    .context("coherence basis missing")?;
                Ok(*numerator as f64 / *denominator as f64)
            };
            let real = (value("xx")? + value("yy")?) / 4.;
            let imaginary = (value("xy")? - value("yx")?) / 4.;
            ensure!(
                analysis["signed_coherence"][context]["re"].as_f64() == Some(real)
                    && analysis["signed_coherence"][context]["im"].as_f64() == Some(imaginary),
                "signed coherence reconstruction mismatch"
            );
            signed_coherence.insert(context.to_string(), [real, imaginary]);
        }
        let terminal_record_path = self
            .assets
            .iter()
            .find(|asset| {
                asset
                    .path
                    .ends_with("/2026-10-12T055624.091217Z/record.json")
            })
            .context("terminal record missing")?;
        let terminal_record = json(&assets[terminal_record_path.path.as_str()])?;
        let mut covered_means = Vec::new();
        for pub_record in terminal_record["execution_pubs"]
            .as_array()
            .context("terminal execution PUBs missing")?
        {
            let pub_name = pub_record["name"]
                .as_str()
                .context("terminal PUB name missing")?;
            for component in pub_record["components"]
                .as_array()
                .context("terminal components missing")?
            {
                let member = component["member"]
                    .as_str()
                    .context("terminal member missing")?;
                for data_source in [MeanSource::Hardware, MeanSource::Replay] {
                    covered_means.push(CoveredMean {
                        member: member.to_owned(),
                        pub_name: pub_name.to_owned(),
                        data_source,
                    });
                }
            }
        }
        ensure!(
            covered_means.len() == 32 && covered_means.iter().collect::<BTreeSet<_>>().len() == 32,
            "terminal record coverage denominator mismatch"
        );
        let selected_test_means: Vec<_> = [
            (
                0,
                "hardware_first",
                "qpe_no_feed_forward_s1",
                "ibm_kingston_dynamic_pub_10",
                MeanSource::Hardware,
            ),
            (
                1,
                "hardware_second",
                "qpe_no_feed_forward_s3",
                "ibm_kingston_dynamic_pub_12",
                MeanSource::Hardware,
            ),
            (
                2,
                "replay_first",
                "qpe_no_feed_forward_s1",
                "ibm_kingston_dynamic_pub_10",
                MeanSource::Replay,
            ),
            (
                3,
                "replay_second",
                "qpe_no_feed_forward_s3",
                "ibm_kingston_dynamic_pub_12",
                MeanSource::Replay,
            ),
        ]
        .into_iter()
        .map(
            |(theorem_index, role, member, pub_name, data_source)| SelectedTestMean {
                theorem_index,
                role: role.to_owned(),
                mean: CoveredMean {
                    member: member.to_owned(),
                    pub_name: pub_name.to_owned(),
                    data_source,
                },
            },
        )
        .collect();
        let mut ordered_means: Vec<_> = selected_test_means
            .iter()
            .map(|selected| selected.mean.clone())
            .collect();
        covered_means.retain(|mean| !ordered_means.contains(mean));
        ordered_means.extend(covered_means);
        let covered_means = ordered_means;
        ensure!(
            covered_means.len() == 32,
            "terminal selected means absent from recorded family"
        );
        ensure!(
            self.terminal.covered_means == covered_means,
            "terminal covered means denominator mismatch"
        );
        ensure!(
            self.terminal.selected_test_means == selected_test_means
                && selected_test_means
                    .iter()
                    .all(|selected| covered_means.get(selected.theorem_index)
                        == Some(&selected.mean)),
            "terminal selected theorem mean indices mismatch"
        );
        let expected = TerminalFixture {
            selected_test_means,
            covered_means,
            means: 32,
            alpha_numerator: 1,
            alpha_denominator: 20,
            radius_numerator: 21,
            radius_denominator: 1000,
            hardware_numerators: [2964, 4911],
            replay_numerators: [4067, 4057],
            shots: 8192,
            margin_numerator: 156109,
            margin_denominator: 1024000,
        };
        ensure!(
            self.terminal == expected,
            "terminal multiplicity/domain/fixture mismatch"
        );
        let terminal_path = self
            .assets
            .iter()
            .find(|asset| asset.path.ends_with("/terminal-channel-check.json"))
            .context("terminal analysis missing")?;
        let terminal = json(&assets[terminal_path.path.as_str()])?;
        let collect_path = self
            .assets
            .iter()
            .find(|asset| {
                asset
                    .path
                    .ends_with("/2026-10-12T055624.091217Z/collect.json")
            })
            .context("terminal replay collection missing")?;
        let collect = json(&assets[collect_path.path.as_str()])?;
        let replay_summary = &collect[1]["replayed_statistics"]["summary"];
        ensure!(
            replay_summary["qpe_no_feed_forward_s1_terminal_correct"].as_f64()
                == Some(1. - 4067. / 8192.)
                && replay_summary["qpe_no_feed_forward_s3_terminal_correct"].as_f64()
                    == Some(4057. / 8192.),
            "terminal replay collection numerator mismatch"
        );
        for (index, member) in ["qpe_no_feed_forward_s1", "qpe_no_feed_forward_s3"]
            .iter()
            .enumerate()
        {
            ensure!(
                means.get(*member) == Some(&(expected.hardware_numerators[index], 8192)),
                "terminal raw numerator mismatch"
            );
            ensure!(
                terminal["replay_probability_one"][index].as_f64()
                    == Some(expected.replay_numerators[index] as f64 / 8192.),
                "terminal replay numerator mismatch"
            );
        }
        let margin_numerator = (4911_i64 - 2964 - (4067 - 4057)) * 125 - 84 * 1024;
        ensure!(
            margin_numerator == expected.margin_numerator && margin_numerator > 0,
            "exact terminal margin mismatch"
        );
        Ok(QuantumBindingReport {
            verified_assets: assets.len(),
            verified_theorem_sources: required_sources.len(),
            verified_theorem_declarations: self.theorems.len(),
            decoded_members: means.len(),
            signed_coherence,
            terminal_margin: [margin_numerator, 1024000],
            physical_premises: self.semantic_boundary.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn root() -> std::path::PathBuf {
        let start = std::env::var_os("GOROROBA_REPO_ROOT")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| std::env::current_dir().expect("current directory"));
        start
            .ancestors()
            .find(|candidate| {
                candidate
                    .join("proofs/evidence/quantum_observables/bindings.json")
                    .is_file()
            })
            .expect("running checkout with binding manifest")
            .to_path_buf()
    }
    fn fixture() -> QuantumBindingManifest {
        QuantumBindingManifest::load(
            &root().join("proofs/evidence/quantum_observables/bindings.json"),
        )
        .expect("manifest")
    }
    #[test]
    fn retained_observables_reconstruct_exactly() {
        let report = fixture().validate(&root()).expect("valid frozen fixture");
        assert_eq!(report.decoded_members, 16);
        assert_eq!(report.terminal_margin, [156109, 1024000]);
        assert_eq!(
            report.signed_coherence["immediate"],
            [0.413330078125, -0.006103515625]
        );
    }
    #[test]
    fn contract_mutations_reach_specific_rejections() {
        let original = fixture();
        original
            .validate(&root())
            .expect("baseline reaches all validators");
        type ManifestMutation = Box<dyn Fn(&mut QuantumBindingManifest)>;
        let mutations: Vec<(&str, ManifestMutation)> = vec![
            (
                "theorem execution domain",
                Box::new(|manifest| {
                    manifest.theorems[0].execution = "conditional_terminal_fixture".into();
                    manifest.theorems[0].decoder_members = vec!["qpe_no_feed_forward_s1".into()];
                }),
            ),
            (
                "theorem execution domain",
                Box::new(|manifest| {
                    let theorem = manifest
                        .theorems
                        .iter_mut()
                        .find(|theorem| theorem.source.ends_with("BranchSignedCoherence.v"))
                        .expect("coherence theorem");
                    theorem.execution = "mathematical_only".into();
                    theorem.decoder_members.clear();
                    theorem.not_applicable_reason = "false reclassification".into();
                }),
            ),
            (
                "theorem premise set",
                Box::new(|manifest| {
                    manifest.theorems[0].premises[0] = "unrestricted premise".into();
                }),
            ),
            (
                "theorem premise set",
                Box::new(|manifest| {
                    let theorem = manifest
                        .theorems
                        .iter_mut()
                        .find(|theorem| theorem.source.ends_with("BranchSignedCoherence.v"))
                        .expect("coherence theorem");
                    theorem.premises.pop();
                }),
            ),
            (
                "terminal selected theorem mean indices",
                Box::new(|manifest| {
                    manifest.terminal.selected_test_means.swap(0, 2);
                }),
            ),
            (
                "theorem declaration denominator",
                Box::new(|manifest| {
                    manifest.theorems.pop();
                }),
            ),
            (
                "terminal covered means denominator",
                Box::new(|manifest| {
                    manifest.terminal.covered_means.pop();
                }),
            ),
            (
                "terminal covered means denominator",
                Box::new(|manifest| {
                    manifest.terminal.covered_means[1] = manifest.terminal.covered_means[0].clone();
                }),
            ),
            (
                "decoder observable formula",
                Box::new(|manifest| {
                    manifest.decoders[0].observable_formula = "p1".into();
                }),
            ),
            (
                "decoder normalization",
                Box::new(|manifest| {
                    manifest.decoders[0].normalization = "divide_by_sqrt_two".into();
                }),
            ),
            (
                "basis convention",
                Box::new(|manifest| manifest.theorems[0].basis = "reversed".into()),
            ),
            (
                "normalization",
                Box::new(|manifest| manifest.theorems[0].normalization = "unitary_sqrt_two".into()),
            ),
            (
                "SHA256 mismatch",
                Box::new(|manifest| manifest.assets[1].sha256 = "0".repeat(64)),
            ),
            (
                "bit order",
                Box::new(|manifest| manifest.decoders[0].bit_order = "big_endian".into()),
            ),
            (
                "register mapping",
                Box::new(|manifest| {
                    manifest.decoders[0].registers_by_replica[0][0] = "missing".into()
                }),
            ),
            (
                "decoder width",
                Box::new(|manifest| manifest.decoders[0].width = 2),
            ),
            (
                "shot count",
                Box::new(|manifest| manifest.decoders[0].shots_per_replica = 2047),
            ),
            (
                "multiplicity/domain",
                Box::new(|manifest| manifest.terminal.means = 2),
            ),
            (
                "multiplicity/domain",
                Box::new(|manifest| manifest.terminal.alpha_denominator = 100),
            ),
            (
                "theorem execution domain",
                Box::new(|manifest| manifest.theorems[0].execution = "hardware_proved".into()),
            ),
            (
                "stale theorem declaration",
                Box::new(|manifest| manifest.theorems[0].declaration = "absent_theorem".into()),
            ),
            (
                "reconstructed observable",
                Box::new(|manifest| manifest.decoders[0].numerator += 1),
            ),
            (
                "SHA256 mismatch",
                Box::new(|manifest| manifest.theorems[0].sha256 = "0".repeat(64)),
            ),
            (
                "unsafe relative path",
                Box::new(|manifest| {
                    manifest.assets[0].source_path = "../../escape".into();
                    manifest.assets[0].path =
                        "proofs/evidence/quantum_observables/frozen/../../escape".into();
                }),
            ),
        ];
        for (expected, mutate) in mutations {
            let mut manifest = original.clone();
            mutate(&mut manifest);
            let failure = format!("{:#}", manifest.validate(&root()).expect_err(expected));
            assert!(
                failure.contains(expected),
                "expected {expected}, got {failure}"
            );
        }
    }
    #[test]
    fn unknown_manifest_fields_are_rejected() {
        let mut value = serde_json::to_value(fixture()).expect("JSON");
        value["unproved_promotion"] = true.into();
        assert!(serde_json::from_value::<QuantumBindingManifest>(value).is_err());
    }
    #[test]
    fn symlink_artifacts_are_rejected() {
        #[cfg(unix)]
        {
            let directory = std::env::temp_dir()
                .join(format!("quantum-binding-symlink-{}", std::process::id()));
            fs::create_dir_all(&directory).expect("temporary directory");
            let link = directory.join("link");
            std::os::unix::fs::symlink("/etc/hostname", &link).expect("symlink");
            let error = regular_bytes(&directory, "link").expect_err("symlink rejected");
            fs::remove_file(link).expect("remove fixture link");
            fs::remove_dir(directory).expect("remove temporary directory");
            assert!(error.to_string().contains("symlink"));
        }
    }
}
