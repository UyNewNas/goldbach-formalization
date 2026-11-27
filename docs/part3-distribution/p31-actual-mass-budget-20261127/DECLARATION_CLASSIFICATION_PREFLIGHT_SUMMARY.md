# Probe4 declaration classification preflight

Status: exact inventory reconciliation passed. This is not fixed-commit formal acceptance.

Corrected source catalog SHA256: `3a35b309959e8bdcf73e555c157ddd708279dbe6905fe26255ca59d899052fb3`.
Probe4 environment inventory SHA256: `bd15ada81ac2bcdc5f1e99069a89882efbd84c13ce813aac7f3f6bed8f9610de`.
Normalized exact-inventory SHA256: `e6a9cfea71016d0c8c4ce341ef63a01dbaf6a8a5038bf80dfead3c22474e3822`.

## Counts by actual defining module

| Module | Recovered source | New source | Generated equation | Generated proof | Generated simp/congruence | Environment total |
|---|---:|---:|---:|---:|---:|---:|
| `ImbalancedChen.Part3ActualModeCoefficientNormsCore` | 32 | 0 | 7 | 2 | 3 | 44 |
| `ImbalancedChen.Part3ActualHardTailLabelBudget` | 2 | 2 | 4 | 0 | 0 | 8 |
| `ImbalancedChen.Part3ActualLabelBudgetCardinality` | 3 | 4 | 1 | 3 | 0 | 11 |
| `ImbalancedChen.Part3ActualModeSmoothMassTail` | 0 | 5 | 0 | 0 | 0 | 5 |
| **Total** | **37** | **11** | **12** | **5** | **3** | **68** |

All 48 source declarations match exactly once. All 20 remaining declarations are generated auxiliaries, and none is counted as an additional new source proof. No source declaration is missing; no environment entry is unexplained. Module assignment uses the compiler `module` field throughout.

## Four exact private-name mappings

| Source name | Compiler environment name |
|---|---|
| `ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_branch_eq` | `_private.ImbalancedChen.Part3ActualModeCoefficientNormsCore.0.ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_branch_eq` |
| `ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_rootT_eq` | `_private.ImbalancedChen.Part3ActualModeCoefficientNormsCore.0.ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.norm_rootT_eq` |
| `ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.baseCarrier_original_window` | `_private.ImbalancedChen.Part3ActualModeCoefficientNormsCore.0.ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.baseCarrier_original_window` |
| `ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.original_innerMultiplier_norm_le` | `_private.ImbalancedChen.Part3ActualModeCoefficientNormsCore.0.ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.original_innerMultiplier_norm_le` |

All four are recovered source theorems defined by `ImbalancedChen.Part3ActualModeCoefficientNormsCore`; they are not generated auxiliaries.

## Metadata correction and generated ownership

`P3TwoLogMixed22SourceOnly.period_pos` remains `source_kind=instance`, `local_instance=true`, and `origin=recovered`. Its corrected catalog `kind=theorem` agrees with the compiler because its type is `Fact (0 < (32 : Real) - (-32))`. This changes source metadata only and leaves the count at one recovered declaration.

The 12 generated equations were checked against their actual equality types. The five generated proof auxiliaries are arithmetic or numeral elaboration subproofs. Two generated simp auxiliaries encode `(0 <= 1) = True`; the third is `rootT.congr_simp`, proving equality under equal inputs.

In particular, `rawCarrier.eq_1`, `weight.eq_1`, and `finiteInnerCarrier.eq_1` are actually defined by the raw-label module in this environment, and `poissonNonzeroFrequencyWindow.eq_1` by the cardinality module. Their parent definitions are imported; their namespaces do not move these generated declarations to another module.

## Allowed axioms

The observed union is exactly `Classical.choice`, `Quot.sound`, and `propext`. Every declaration has only a subset of these axioms. No other axiom occurs.

## Frozen current source hashes

| Module | SHA256 |
|---|---|
| `ImbalancedChen.Part3ActualModeCoefficientNormsCore` | `f962b424fecdbd1e4542c61daeefa6abfcf6fe884a7c9860fc1f2ab6c4274365` |
| `ImbalancedChen.Part3ActualHardTailLabelBudget` | `3e2c1759b1bdf777681c1262b78a4f82a99e5eefe8b9803f2a76fb762bb1fc1e` |
| `ImbalancedChen.Part3ActualLabelBudgetCardinality` | `5c8e7cc495566acdf6ec67c2abda1865fc5b9b229ccec493e772010688e20f4e` |
| `ImbalancedChen.Part3ActualModeSmoothMassTail` | `2226799a29adfd54fb0f763cb73bb18123ff04a00722c98bebdec4245c7ccd14` |

Every current source is byte-identical to the corresponding probe4 source snapshot and matches the frozen hash in the probe report. No Lean source was edited during classification.

The later fixed-commit formal gate must independently reproduce the exact 68-declaration inventory, including defining modules, types, universes and axiom dependencies.
