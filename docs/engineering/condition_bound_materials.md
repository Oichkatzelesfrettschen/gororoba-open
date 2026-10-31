---
description: Material, specimen, and measurement provenance rules for condition-bound properties
last_verified: 2026-10-30
status: active
---

# Condition-bound materials

These rules apply to every material property, model, experiment, and claim in
the repository. The detailed contract is
`docs/engineering/casimir_optics_discrimination_contract.md`.

- A name or chemical formula identifies a material family, not a unique phase,
  specimen, dataset, measurement, or model.
- Use the typed chain `Material -> MaterialState -> Specimen -> Measurement ->
  QuantityValue`. Keep `ModelRun` and `DerivedValue` on separate nodes with
  explicit measured inputs.
- Assign stable IDs to material, phase or state, specimen, dataset,
  measurement, raw artifact, processing recipe, quantity, and model run.
- Record temperature, pressure, atmosphere, phase fraction, orientation,
  strain, applied fields, processing history, and time since processing when
  they affect applicability.
- Record purity and composition assays, synthesis or deposition, anneal,
  thickness, substrate, adhesion layers, grain size, texture, porosity,
  roughness, and geometry for each specimen.
- Bind every observed quantity to a unit, representation, tensor component or
  basis, conditions, applicability range, method, instrument, calibration,
  operator or facility, repeat count, uncertainty or covariance, detection
  limit, and raw artifact.
- Bind each detection limit to the quantity it constrains. A shared acquisition
  may produce quantities with different units; one measurement-level limit
  cannot stand in for all of them.
- Let each raw-artifact ID own one immutable path, source identity, locator, and
  source-byte SHA-256. Every measurement that references the ID must agree with
  that artifact metadata.
- Preserve `experimental_direct`, `experimental_fitted`, `computed`, and
  `inferred_proxy` as distinct evidence classes. A fitted value names its
  inputs, fit model and version, residual artifact, ordered parameter basis,
  and matching parameter covariance. Measurement artifact and processing-recipe
  IDs resolve to unique typed records; a nonempty unresolved ID is insufficient.
- A computed repository such as JARVIS or Materials Project remains computed.
  It cannot satisfy an experimental property requirement. An experimental
  crystal source such as COD remains separately identified.
- Represent absence as `not_measured`, `below_detection_limit`,
  `not_applicable`, `withheld`, or `unknown`. Never encode missingness as `0.0`
  or an empty string.
- Retain DOI or stable source ID, page/table/figure or source row, license,
  retrieval date, source-byte SHA-256, parser version, and transformation
  lineage. A database record also cites its underlying paper and specimen.
- Treat default lookups such as `get_material_model("gold")` as model
  selection only. They never select a physical specimen or universal response.
- Validate a model and an optical witness against the same specimen, geometry,
  constitutive model, conditions, and state history before joining them in a
  claim.
