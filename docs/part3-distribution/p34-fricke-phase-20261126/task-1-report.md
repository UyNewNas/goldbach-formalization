# Task 1 — original cusp-one and Fricke phase source preparation

**Status: DONE.** Fresh compilation, kernel replay and complete declaration auditing passed on published source `e84cfd0ee77bb6be687c1f511d666eb478a17737`. The final section gives the receipt and accepted scope. Earlier sections preserve source preparation and failed diagnostics in order.

- Local prepared source `69ee840ffee9a260ae0cf5ce81e48b5809ee0635`, tree `803e117a20acee4e636f18925b5a4f567b8c138b`, parent `bd0f67f2d84c7b5f753b61f2bdbdf7501f014f47`, branch `codex/p34-kernel-20261125`.
- Evidence correction `9872d10f948abf23a49e7b81e1fb23045376bd8e`, tree `45c60943be0a7ca72b2957d4036b41e0ec1404f9`, is the local publication candidate. The only change from the prepared source commit is the explicit declaration count paragraph of `NEXT_ENDPOINT_AUDIT.md` (+1/-1). `git diff --check` and `git diff --cached --check` passed for this docs-only correction.
- Changed `ImbalancedChen/Part3ActualFrickeCuspPhase.lean`, `verification/verify_p34_fricke_phase.py`, `verification/P34FrickePhaseAudit.lean`, and `docs/part3-distribution/p34-fricke-phase-20261126/SOURCE_INTAKE.json`. The committed delta comprises four files, 337 insertions and 5 deletions. The source intake identifies all ten source files by full hashes and Git blobs and records the four owners' original source declaration names and kinds.

## Identity and scope checks

- All four original owners' starting bytes match donor `fa22a56829ee880404516a36d498ce27dcb32f92`, the full hashes in `NEXT_ENDPOINT_AUDIT.md`, and the historical `PUBLISHED_EXACT_CURRENT_BYTES` import records. The Fricke normalizer, general cusp width, and unit-period normalization are still byte-identical to those donor files.
- The terminal starts at `5bedd570c27e4741bec288e39d4d47369640b161` (7,578 bytes; SHA-256 `4b9366fc9d44c9713634747797d6a429e6e11a62a723d91e56468e53ee2a2b74`). The installed blob is exactly `8b47c8a7f053af911e13009e2a2676f9968f572c` (8,053 bytes; SHA-256 `749882d348253efdfb33387299a30653f0484b0810eeac84a761c2433609fddf`), both on disk at the archive path and as a donor Git object. Byte equality holds after concatenating the exact nine-line archived header and the original body with five substitutions of `AddCircle.fourier` with `_root_.fourier`. The `AddCircle.haarAddCircle` occurrences and historical comments remain intact. Registry declaration names, kinds and nine-line offsets match. This is the documented pinned-API namespace repair.
- The four original files contain 72 explicit source declarations, 18 definitions and 54 theorems in counts of 22, 16, 19, and 15. The original `NEXT_ENDPOINT_AUDIT.md` count of 71 corresponds to the public source declarations. The local evidence correction records both counts. The additional declaration is the existing private theorem `upperTriangular_signed_translation` in `Part3Gamma0GeneralCuspWidth.lean` at line 106. The source intake records it and leaves compiled inventory counting to the full gate.
- All six reused provider files exactly match the source blobs and `source_sha256` entries of the packet receipt at `145be87ff0a88914b607baa2a330bc88105a08d6`. That receipt has 101 compiler records in these six modules. All 44 distinct previously bound files surveyed across seven P3.4 `PASSED` reports, and the seven receipt files themselves, are unchanged from the edit base. Some historical reports bound older revisions of shared verifiers and one source path, and those historical bindings are preserved at their original source heads. All shared verifier, lexer, import-scope regression and package configuration bytes are unchanged from the edit base.
- The entry point uses baseline `da576de2c91df467d1865baee9c1b1b84ddc529b` and binds both itself and `SOURCE_INTAKE.json`. Its ordered owners match both the imports and owner array of `P34FrickePhaseAudit.lean`. A separate source check verified the exact ten-module transitive project-import closure of the terminal and topologically ordered direct imports. The auditor body matches `P34CuspPacketAudit.lean` when the two module lists are normalized. The defining-module inventory, serialized-constant cross-check, transitive-axiom allowlist and type-truncation guard are the existing mechanisms. Lean-resolved import scope and replay remain part of the cloud gate.

## Source-only verification and self-review

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 69ee840ffee9a260ae0cf5ce81e48b5809ee0635 --output-dir .lake/p34-fricke-phase-source-check --source-only
git diff --check bd0f67f2d84c7b5f753b61f2bdbdf7501f014f47 HEAD
```

Both commands exited zero. The gate reported `SOURCE_ONLY_NOT_COMPILED`, 10 modules, 19 source bindings, and exit code zero for `head`, `working-tree`, and `baseline-ancestor`. The tracked worktree was clean. The staged diff also passed `git diff --cached --check`. No Lean process or cloud job ran during source preparation.

I reviewed the exact terminal diff and the unchanged original owners against the chart/phase audit for frozen manuscript lines 951–962. The unchanged definitions retain literal Fricke action, the square-root and reciprocal-square-root scaling factors, and the width-normalized cusp-one chart. The endpoints retain actual Gamma0 invariance, positive level and height, signed integer frequencies, the positive exponential `Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ))`, and the explicit normalized-Haar premise of the integrable form. The resulting claim concerns fixed-height circle Fourier coefficients. DI/Whittaker spectral normalization, ABL dilation, full P3.4, and historical D20 remain open.

## Pending gate inspection

The coordinator will provide the exact local-to-published source mapping and complete cloud receipt. Review the ten strict compiles and bundled replays, Lean-resolved imports, all declaring-module records including private/generated declarations, exact earlier six-provider inventory equality, permitted transitive axioms, source/object binding and the actual terminal elaborated types. Preserve any failing diagnostic before applying a further repair. Acceptance remains pending at this stage.

## First published run and normalizer repair

The local publication candidate tree `45c60943be0a7ca72b2957d4036b41e0ec1404f9` was published as source `71f508c71cf925c48c55565e9e0f3ad7ccc611cf`. The initial attachment failed before Lean with `ENOSPC`. Cloud attempt 02 entered the gate at the exact published head, used Lean `4.33.0-rc1` at compiler commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, and strictly compiled all six reused providers. `Part3FrickeNormalizer-strict` exited 1. The complete failed receipt and log are in `/workspace/library-files/p34-evidence-staging/continuation-20261126/cloud-attempt-02/verification/`. The strict log SHA-256 is `3ca3e5d30396c0a5c6e1f82fdefa6fe8d72ca490c78874ed668ee293d06e9c41`, and the report SHA-256 is `abfe33a041de0df815ae45b194c748c8ae4e593778b87a4fa6f12d24c2857b5b`. Cloud task `d28229cec7a84a56a20f6183d09c3834` produced these records.

I compared the failed module with its original donor bytes and the pinned Mathlib source at `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. The expression and elaboration failures were:

| Failed declaration | Exact diagnostic location and cause | Proof change |
| --- | --- | --- |
| `frickeSL_inv_coe` | Line 91, four unsolved entries of the underlying matrix inverse. Line 93, unused `SL2_inv_expl`. The result type annotation at the inverse resolves the operand into the matrix ring. | Expand `Matrix.inv_def`, use the existing determinant-one identity, and compute `Matrix.adjugate_fin_two_of`. The inverse statement retains its original text and elaboration target. |
| `fricke_conjugation_matrix_formula` | Lines 99 and 101, the displayed-matrix simp lemma is unused for the arbitrary middle matrix, and row-vector products survive scalar normalization. | Expand `Matrix.mul_apply` and `Fin.sum_univ_two` before scalar simplification, denominator cancellation and ring normalization. |
| `frickeSL_conjugate_gamma0` | Line 117, the matrix inverse in the proposed `change` is not definitionally the underlying adjugate of an SL inverse. | Change to explicit SL subtype values, bridge the displayed matrix inverse using determinant one, and simplify the integer-to-real entries. The original division proof and conjugation formula remain the inputs. |
| `frickeSL_normalizes_realGamma0` | Line 159, `rw` cannot see through the applications of the image and range lambdas. | Expose the two beta-reduced applications, then apply the existing conjugation and involutivity equations. |
| `frickeSL_square` | Lines 162 and 166, entrywise simp unfolds constructors but leaves their product coercion and reports unused matrix simplifiers. | Pass to the underlying matrices first, expand the two-by-two product and identity, and simplify the four scalar entries. |
| `frickeSL_action_involutive` | Line 175, `rw` cannot see the action inside the unapplied involution lambdas. | Expose the two nested genuine actions before the original `mul_smul` and square rewrite. |

The frozen 1106 appendix SHA-256 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548` matches the selected source. Lines 951–962 still describe the width-normalized chart with `sqrt(z)` and `1/sqrt(z)`, and the geometric cusp phase. The normalizer's literal square-root matrix, exact integral conjugate, Gamma0 conditions and hyperbolic action remain original. The fixed-height Fourier and normalized Haar scope remains as above. No omitted manuscript derivation or substantive gap was identified by these diagnostics.

The candidate is `ac605cd1394845884447af3552c8b9d139ca66c9`, tree `927c28eeb3a6ec7615540501c6a3afbe2be4f846`, parent `71f508c71cf925c48c55565e9e0f3ad7ccc611cf`. Two files changed (+79/-13). Normalizer blob `ab1dfbdfcdb6046489dfb7e91496b4024436e770` has 9,484 bytes and SHA-256 `0014ecd9be8645d9ce4ea60c06c0cacb6811a1f28d7752206e8a70e4a65e656c`. `SOURCE_INTAKE.json` keeps the terminal's archived substitution separate from this compiler-driven repair. Byte comparison of all original named declarations found the same 15 theorem statements and 7 complete definition bodies, with edits confined to the six diagnosed proofs. The imports, other proof bodies, prior accepted providers, gate and auditor are unchanged.

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head ac605cd1394845884447af3552c8b9d139ca66c9 --output-dir .lake/p34-fricke-phase-normalizer-source-check --source-only
git diff --check 71f508c71cf925c48c55565e9e0f3ad7ccc611cf HEAD
```

Both commands exited zero. The clean gate reported `SOURCE_ONLY_NOT_COMPILED` with 10 modules and 19 bindings. Only the normalizer and its intake hashes differ from the initial source-only receipt. The candidate awaits the coordinator's focused four-owner probe and complete ten-module gate.

## Read-only preparation for downstream diagnostics

The candidate remained `ac605cd1394845884447af3552c8b9d139ca66c9`. I read the three downstream owners and the pinned Mathlib sources, without changing source or invoking Lean.

- `Part3Gamma0GeneralCuspUnitPeriod.lean` has two concrete namespace mismatches. Line 123 uses `UpperHalfPlane.SL_neg_smul`, which pinned `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` declares under `ModularGroup` at line 469. Lines 130 and 173 use `ModularGroup.modular_T_zpow_smul`, which the same Mathlib file declares under `UpperHalfPlane` at line 310. The accepted `Part3ActualCuspFourierSection.lean:53` uses the latter correct qualification. `ModularGroup.coe_T_zpow_smul_eq` at owner line 179 is already correctly qualified, as shown by `Mathlib/NumberTheory/Modular.lean:308`.
- `Part3Gamma0GeneralCuspWidth.lean:32` and `Part3Gamma0GeneralCuspUnitPeriod.lean:44–45` apply `Matrix.mul_fin_two` to products with an arbitrary matrix factor. Pinned `Matrix/Notation.lean:479` matches two displayed `!!` matrices. The failed normalizer diagnostic exhibited the related surviving `vecMul` form when only one factor was displayed. The packet-accepted `Part3Gamma0ActualCusps.lean:56–63` and `Part3ActualCuspWidthNormalization.lean:51–73` are nearby references for exposing SL values and literal matrices. The latter also covers the same diagonal conjugation appearing at unit-period owner lines 57–68.
- `Part3ActualFrickeCuspPhase.lean:39–41` combines SL coercion, a mapped integral literal, and a two-by-two product. If strict simp leaves a coerced product or map, pinned `SpecialLinearGroup.lean:154` and `:225–231` distinguish the value of the SL product from the mapped matrix entries. The signed phase proof at lines 113–116 refers to the correct root Fourier API after the archive repair. The packet-accepted `Part3CuspTranslationFourierPhase.lean:79–85` supplies a nearby explicit `fourier_coe_apply` and exponential-argument example if the signed expression itself fails. No downstream compiler result has yet been inferred from these source observations.

## Static pinned Mathlib namespace repair

Candidate `9e5814191032347e43b688c16e3d7aa464bd139a`, tree `1ce60b383abef26d5a6d41b848d524cd8338b3f5`, applies the three concrete namespace substitutions described above. The only Lean changes are the qualifiers at the original lines 123, 130, and 173. Byte comparison verifies the statements, definitions and other proof bodies. The unit-period file now has blob `f66b0978e5226b619ce1bf37b88b9e1484395cbe`, 10,778 bytes, and SHA-256 `9574a65ad68ee46d79c49c1c28f6cbea33747af22e84c23eb3526a7e1e59f6ab`.

`SOURCE_INTAKE.json` records this static API evidence separately from the compiler-driven normalizer repair and the archived Fourier repair. At pinned Mathlib commit `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` has blob `64c4be3caf4e8a6668eb3e5bd4d0b444942f70e9` and SHA-256 `afcdc0da1807f69632a3cf4a93d3276b2a403ae41de7d06578d337dca4177d6e`. Its namespace and declaration lines establish `ModularGroup.SL_neg_smul` at line 469 and `UpperHalfPlane.modular_T_zpow_smul` at line 310. The intake also corrects the earlier MCP task ID to `d28229cec7a84a56a20f6183d09c3834`.

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 9e5814191032347e43b688c16e3d7aa464bd139a --output-dir .lake/p34-fricke-phase-unit-api-source-check --source-only
git diff --check ac605cd1394845884447af3552c8b9d139ca66c9 HEAD
```

Both commands exited zero. The clean source-only run checked 10 modules and 19 source bindings, with changes from the prior candidate confined to unit-period source and intake metadata. The queued focused probe remains bound to `ac605cd1394845884447af3552c8b9d139ca66c9`. This namespace repair awaits Lean verification on a candidate containing it.

## Focused probe 01 and follow-up normalizer repair

Focused cloud task `9c63c77836b6420eb76e2feda7327c8a` used candidate `ac605cd1394845884447af3552c8b9d139ca66c9` and verified all six reused object hashes against the accepted packet receipt. `Part3FrickeNormalizer-strict` exited 1, and the diagnostic assigned no acceptance credit. The source-bound receipt and complete log are archived under `/workspace/library-files/p34-evidence-staging/continuation-20261126/focused-01/`. The evidence ZIP SHA-256 is `ff8a430cd005c72e0e5945ad3d5b2afa59ef63da9df8e38be1af3cf850d9c848`, the report SHA-256 is `728e0984e040c8ced11fea42bfcd188489da5834502a0cdadcf9d2f2e768c849`, and the strict log SHA-256 is `7545c62c370ddb497a5786f23915dcd1b0ff1499d9c4623a33be0418b1a63a9d`.

The elapsed simplification in the real matrix formula cleared all scalar goals before its trailing `ring`, triggering the unreachable-tactic diagnostic at line 103. The conjugation failed at line 108 with four RHS entries of `realSL ⟨!![…], …⟩` still present, leaving the integer quotient-cast equality unused at line 128. The candidate removes the unreachable tactic and exposes the directly cast integer entry in each of the four cases. The diagonal cases use the existing local entry identity. The off-diagonal cases use the existing square identity and exact quotient-cast equality, with the appropriate signed cast and division rewrites. These are two expression-level proof changes within the same literal Fricke matrix and original Gamma0 argument. All 15 original theorem statements and seven definition bodies match the original donor text byte for byte.

Candidate `09dec38e29c7b61e6a346d003a599753f4c036d0`, tree `ce08295a0db9a2928304708e21aec7248b860f67`, retains the three static unit-period namespace fixes. The normalizer blob is `57786c0d011924bd81bb2531b4e11a35491e6a54` (9,849 bytes, SHA-256 `947c7625baddb363a94095ce31d7744ec9d87d11b7ee633f3305a3aa678a1d7d`). `SOURCE_INTAKE.json` separately records the failed focused snapshot, the receipt and diagnostic hashes, and the repair. These are the only two source bindings that changed from candidate `9e5814191032347e43b688c16e3d7aa464bd139a`.

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 09dec38e29c7b61e6a346d003a599753f4c036d0 --output-dir .lake/p34-fricke-phase-focused01-repair-source-check --source-only
git diff --check 9e5814191032347e43b688c16e3d7aa464bd139a HEAD
```

Both commands exited zero. `SOURCE_ONLY_NOT_COMPILED` covered the clean exact head, 10 modules and 19 source bindings. The next focused probe and complete fresh gate remain pending.

## Focused probe 02 and normalizer/width repair

Focused cloud task `e424d2f6431d445e80728bba28649f69` used exact candidate `09dec38e29c7b61e6a346d003a599753f4c036d0`, verified reused objects, and returned `DIAGNOSTIC_FAILED` after independent strict runs of the normalizer and general cusp width. Both strict commands exited 1. The evidence at `/workspace/library-files/p34-evidence-staging/continuation-20261126/focused-02/` includes the 5,530-byte ZIP (SHA-256 `e67454b4d321c477f4013ca07c2d97b996fc87b41a86fc4911df1c309d7cbf36`), report (SHA-256 `9abd2280a718190de0255da8fffc410c3002846033d8cdfcddefcd3dfbd83a04`), and exact logs `Part3FrickeNormalizer-strict.log` (SHA-256 `fbabc56ca00ba0fa0e50bdd9b246f5dec4ff5300e71f26ab632898dedb733e5c`) and `Part3Gamma0GeneralCuspWidth-strict.log` (SHA-256 `3fe379c0307af5b0da03fd235bea621c021817d3a0eb90e8ae45badcfa9cd988`).

- **Matrix projection elaboration.** The normalizer's log contains the two off-diagonal goals at lines 131 and 133. The RHS-only change exposed the integer cast, but the LHS still had the literal `!!` matrix applied to Fin indices under identity lambdas. Both scalar sides are now exposed in the same `change`, before the existing cast and square rewrites. The original statements and matrix entries remain verbatim.
- **Notation scope.** General cusp width's line 18 opened an unavailable `UpperHalfPlane` scope, and line 91 could not parse `∞`. Pinned `Mathlib/Topology/Compactification/OnePoint/Basic.lean:71` declares the notation in `OnePoint`. The accepted direct provider `Part3Gamma0ActualCusps` opens that scope and uses the same projective `mapGL` action and `smul_infty_eq_self_iff`. Opening `OnePoint` and dropping the unavailable scope resolves the source dependency at the notation level. Imports stayed byte-identical. The genuine cusp fixing statement and its proof body stayed byte-identical.
- **Matrix formula and signed coercion.** Width lines 31–32 simplified an SL constructor and left the coercion of the group product. The patch rewrites `SL2_inv_expl` and exposes the underlying product in the same manner as the accepted cusp-one special case, then applies the existing translation formula and expands the two-entry sums for the general integral matrix. Line 151 had simplified through matrix inverse and negation before matching the existing signed conjugation theorem. The patch rewrites the central-sign equality in the divisibility premise and exposes the negative SL entry before applying the original conjugation formula.
- **Arithmetic lemma application.** Width lines 155–156 reduced to `N / N = 1`. The patch uses `Nat.div_self hN` from pinned Lean's `Init/Data/Nat/Div/Basic.lean:443`, with the positive level premise already present.

The 1106 appendix SHA-256 and lines 952–962 were rechecked. These repairs concern the original signed matrix and width calculations that supply the chart with `sqrt(z)` and `1/sqrt(z)`. All source definitions and declaration statements match the original donor bytes across the 22 normalizer and 16 width declarations. This round changed only the proof of `frickeSL_conjugate_gamma0` in the normalizer. The three changed width proof bodies are `conjugated_translation_c`, `gamma0_cusp_stabilizer_classification`, and `cuspWidth_infinity`. The unit-period namespace fixes remain in place. No omitted mathematical step was identified in these diagnostics.

Candidate `103ed489f488043b1dd855b9d2ddd8b4890b7967`, tree `68cf1088e15a063ac1dd55d5306eab5947ab0f6d`, records the exact diagnosis and distinction between notation, scalar matrix calculation, and arithmetic simplification in `SOURCE_INTAKE.json`. Only the normalizer, width and intake bindings changed from the prior candidate.

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 103ed489f488043b1dd855b9d2ddd8b4890b7967 --output-dir .lake/p34-fricke-phase-focused02-repair-source-check --source-only
git diff --check 09dec38e29c7b61e6a346d003a599753f4c036d0 HEAD
```

Both commands exited zero. `SOURCE_ONLY_NOT_COMPILED` covered the clean exact head, 10 modules and 19 source bindings. The focused and complete Lean gates remain pending.

## Focused probe 03 and projective cusp-action cast repair

Focused task `026c1c76b3da41d4a76263c6df267eea` ran exact source `103ed489f488043b1dd855b9d2ddd8b4890b7967`. The strict Fricke normalizer stage exited zero. The general cusp width stage exited 1 with one unsolved projective action goal, and the diagnostic receipt carried no acceptance credit. The evidence in `/workspace/library-files/p34-evidence-staging/continuation-20261126/focused-03/` includes ZIP SHA-256 `0d485b55dde9988a91878b8c4cf36c59ad75dcd8c0d4b7befa39aa7be5a09c97`, report SHA-256 `55beb5e59fdcfc23500b8d9e69cb43e388eb3455f262207fb06ffbccc0695e65`, and width strict log SHA-256 `24f720acdd86c45020a938fbb823bb804287fd3018aaf208a19f9dafcea0ec37`.

The original `fixesIntegralCusp_iff_actual_action` uses `OnePoint ℝ` and `mapGL ℝ` on a matrix in `SL(2, ℤ)`. Strict Lean reported the failure at line 100. Ordinary simplification had split `mapGL` over the product and inverse, leaving the equality condition for the product of real matrices on one side and the integer SL adjugate product on the other. The repair first applies `OnePoint.smul_infty_eq_self_iff`, then exposes the GL matrix coefficient and uses `mapGL_coe_matrix` and `Matrix.map_apply` while the integer conjugate is intact. `algebraMap_int_eq` and `Int.cast_eq_zero` reduce the remaining goal to the same exact integral zero test. The actual projective point, group morphism, gamma conjugate and fixed-cusp assertion are the originals. This is a cast and rewrite-order issue in one existing proof body.

Candidate `3d06b15e93a497803edfa9a54b9c6bcbe4b8d788`, tree `5086f03b6b693ab5fc35a42c65c543b132cf1bcd`, changes only width and source intake. The width file is 8,711 bytes, blob `39190b2d0700e1805c2274bddf4412efbc1fa633`, SHA-256 `1d64b852af3e1f82ae41f23d52f28e87ff190ee2d0e360430d4514f1179bce5a`. All 16 original declaration signatures and both definition bodies match the original donor bytes. The normalizer remains byte-identical to the probe's successful strict result. The width normalization scope and terminal archived Fourier substitution remain as prepared.

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 3d06b15e93a497803edfa9a54b9c6bcbe4b8d788 --output-dir .lake/p34-fricke-phase-focused03-repair-source-check --source-only
git diff --check 103ed489f488043b1dd855b9d2ddd8b4890b7967 HEAD
```

Both commands exited zero. The exact clean source reported `SOURCE_ONLY_NOT_COMPILED` for 10 modules and 19 bindings, with only width and intake hashes changed. The coordinator will publish the candidate and run the fresh full gate.

## Published cloud attempt 03 and direct cast reduction

Local candidate `3d06b15e93a497803edfa9a54b9c6bcbe4b8d788` and published head `9ab1aa96da0b6be512f3040110748a5afb69c4c2` have identical tree `5086f03b6b693ab5fc35a42c65c543b132cf1bcd`. A P1 attempt stopped at its pre-existing dirty goldbach dependency guard before project compilation. P3 full task `7782ec5138d84f5688626c22ab89789b` passed its pin and dependency cleanliness guards, then strictly compiled the six reused providers and the normalizer. Width's strict stage exited 1 at line 103, column 26. Exact receipt and log are under `/workspace/library-files/p34-evidence-staging/continuation-20261126/cloud-attempt-03/verification/`. Their SHA-256 values are `8ccbd04fe6d4bbb0c2c33a26a9b5c4822c068675f8480739cf4e5834c4be22c9` and `393f7d7f45890c0b8de2aba6e8efd4dc817735f37a36db9561b9450224dc561a`. The 22,445-byte evidence ZIP SHA-256 is `7f9ecece33e1abf1a7f30a1b65eb93b855f47879795c66bb6e2af2155f9b2e4f`.

The projective infinity rewrite succeeded, and the failed `Matrix.map_apply` rewrite was presented with a coerced `SpecialLinearGroup.map (algebraMap ℤ ℝ)` application. Its inferred subtype was not available at `rw`'s implicit transparency level. The follow-up keeps the exact conjugate and uses a single explicit `change` to its lower-left integer coefficient cast to `ℝ`. Pinned `GeneralLinearGroup/Defs.lean:277–280`, `SpecialLinearGroup.lean:225–231`, and `Algebra/Algebra/Basic.lean:297–305` implement this definitional equality. `Int.cast_eq_zero` proves the resulting iff. The exact original projective statement, hypotheses, and definitions still match the donor bytes. The normalizer, unit period, and terminal sources are byte-identical to published head `9ab1aa96da0b6be512f3040110748a5afb69c4c2`.

Candidate `2924ba4efbe3dd9f9243d6e11c8dcca5a2a9baa8`, tree `f9941cc5b40c61155b2eec1ccfcfdb765178f9e6`, changes one proof body and its source intake record. Width blob `60d6f54aaa478748f8faeb173801eb5bf4bc2041` has 8,658 bytes and SHA-256 `272f162c3c4de1cce82be965edf363729ceda2172958bc1ecf14028b3083db63`.

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 2924ba4efbe3dd9f9243d6e11c8dcca5a2a9baa8 --output-dir .lake/p34-fricke-phase-cloud03-repair-source-check --source-only
git diff --check 9ab1aa96da0b6be512f3040110748a5afb69c4c2 HEAD
```

Both commands exited zero. The clean source-only receipt binds the exact candidate across 10 modules and 19 source files. The coordinator will run the remaining strict diagnostics and final gate.

## Focused probe 04 and unit-period expression repairs

Focused cloud task `c0a06e3a01494572b68ed83331583801` bound exact candidate `2924ba4efbe3dd9f9243d6e11c8dcca5a2a9baa8`. General cusp width strict compilation exited zero. The unit-period strict run exited 1, and the terminal was blocked on it. The diagnostic receipt assigned no acceptance credit. The preserved evidence in `/workspace/library-files/p34-evidence-staging/continuation-20261126/focused-04/` includes the 5,680-byte `receipt.zip` (SHA-256 `58d1f263fb984484e4941dff88c02417b5deaeab80254e1a2e8b42d056c2da4e`), report (SHA-256 `e18bd8bb41d905e1aff804241d182e677c52671a14ccda2e6a79556592602f46`) and strict unit-period log (SHA-256 `6830a2a4ee3f7e74899fec7efdbd791cdce309cafe8b5385f7da007f958d6bfd`).

- The scaling entry calculation at 43–45 left a coerced SL product. The proof now exposes the matrix product, expands the two scalar summands, and simplifies the genuine integral cast. At 51 and 54, `simp` unfolded `cuspOneMatrix` before its width theorem could match. The width theorem now rewrites before the constructor is exposed.
- The diagonal transport at 65–68 left the inverse, mapped translation, and matrix products opaque to scalar arithmetic. The proof now uses the literal SL inverse, projects both translated matrices, and applies the same two-by-two calculation as the packet-accepted `Part3ActualCuspWidthNormalization.lean:51–73`. Its existing nonzero square-root and exact square identities supply the scalar algebra.
- The linter at 136 flagged unnecessary `simpa` for a local real-coordinate statement already exactly supplied by `UpperHalfPlane.vadd_re`. At 150, the expected cancellation left nested inverse actions; `MulAction.injective` now cancels the same action directly.
- At 165 and 171, broad simplification converted the integer translation power before applying its matrix theorem. The proof now applies `congrArg` to its exact lower-left entry. At 177 and 179, the named complex-coercion lemma is unavailable through the original imports. The patch instead uses `UpperHalfPlane.modular_T_zpow_smul` and the already-accepted horizontal calculation in `Part3ActualCuspFourierSection.lean:45–55`. Imports remain unchanged.

I rechecked frozen 1106 appendix lines 951–962 and SHA-256 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`. The original normalization preserves the two displayed square-root factors and the genuine width-normalized action. These are matrix projection, rewrite order, API availability under the original imports, and strict warning issues. The repairs introduce no new premise or manuscript derivation. All 19 original declaration signatures and five full definition bodies match the donor bytes. The source changes are confined to seven diagnosed proof bodies and the separately preserved namespace fixes.

Candidate `d4315e95c3423aa50c7265baf81d8348705e09f7`, tree `27318570e38dbbcad6240ab505124edc0f2087ec`, binds the new unit-period source as blob `7bd050461b6634838008f6b9652a94bab7dde10a` (11,234 bytes, SHA-256 `bf277621d9a24a06d7f091623a10d6c9f369ce136b222ae93c5970f588b1313b`). `SOURCE_INTAKE.json` records each exact diagnostic and repair. The three other owner files match the focused snapshot byte for byte.

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head d4315e95c3423aa50c7265baf81d8348705e09f7 --output-dir .lake/p34-fricke-phase-focused04-repair-source-check --source-only
git diff --check 2924ba4efbe3dd9f9243d6e11c8dcca5a2a9baa8 HEAD
```

Both commands exited zero. The clean source-only result binds all 10 modules and 19 source paths. Only unit period and intake differ from the previous candidate. Cloud verification of the unit-period repair and the full ten-module gate remain pending.

## Focused probe 05 and terminal proof repair

Focused task `302e9411bca74e56aa9bde8009cff848` ran exact candidate `d4315e95c3423aa50c7265baf81d8348705e09f7` in 14.282 seconds. Unit period passed strict compilation. The terminal strict run exited 1 with one unsolved matrix equality and strict unused-simplifier errors. The preserved diagnostic under `/workspace/library-files/p34-evidence-staging/continuation-20261126/focused-05/` has ZIP SHA-256 `c9c1f5ec002f8db0dd937b298ebd32c0f82d784c2a48d11a69c1cdab401c52b0` (4,857 bytes), report SHA-256 `ae03df1ccb2ac50eaab1b91b41d8a0a9bb24d2868a61b1025e612187d25ba07c`, and terminal strict log SHA-256 `74538530700baa484abec957ea5a63d54acc8c247603d1c3607d0e1c522b50e1`. This focused receipt assigns no acceptance credit.

Lines 38 and 41 showed an underlying matrix goal with the RHS still a coerced product of the mapped integral translation and `frickeSL`. The repair exposes the two SL values explicitly, casts the pinned literal translation entries, then uses `Matrix.mul_fin_two` on the two displayed matrices. This preserves both square-root factors and the original cusp-one scaling chain in frozen 1106 lines 951–962. Line 116 reported that `_root_.fourier_coe_apply` was an unused simp argument. Removing that argument preserves the same signed Fourier character calculation. These are a matrix-coercion elaboration issue and a strict linter issue. The actual fixed-height coefficients, positive levels and heights, signed frequencies, Gamma0 invariance and normalized-Haar premise are the originals.

The archived repair still matches the exact donor body plus 9-line header and 5 substitutions. The active terminal then differs from that archive in precisely two proof bodies. All 15 declaration signatures and four full definition bodies are byte-identical to the archived repair. The header, original comments, imports, other proof bodies, and nine other owner files are unchanged. `SOURCE_INTAKE.json` preserves the archival installation identity and independently records the compiler-driven proof delta and its evidence hashes.

Candidate `22dd5cbc1aec9a8a25e1e424ec1ee60f3c8a04bf`, tree `3a475b982f0b2f446b2f19c4732c57251e3874c4`, has terminal blob `16a47b7ff1546baca8dfa6373f706909d162e796` (8,239 bytes, SHA-256 `1a45a4c86e3f17404e1edbf989c7891e6af5cf04a342596be90c2c1a1a29fae2`).

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 22dd5cbc1aec9a8a25e1e424ec1ee60f3c8a04bf --output-dir .lake/p34-fricke-phase-focused05-repair-source-check --source-only
git diff --check d4315e95c3423aa50c7265baf81d8348705e09f7 HEAD
```

Both commands exited zero. The exact clean source-only run checked 10 modules and 19 bindings. The terminal and its source intake are the only changed bindings. The next focused probe and complete fresh gate remain pending.

## Focused probe 06 and unreachable-tactic repair

Focused task `e3c74017ce9541119cee07f23570405b` used candidate `22dd5cbc1aec9a8a25e1e424ec1ee60f3c8a04bf` and completed in 5.698 seconds. It verified nine reused objects, and the terminal strict stage reported exactly one diagnostic at line 121, column 39. The previous matrix change produced no further diagnostic. The retained receipt `/workspace/library-files/p34-evidence-staging/continuation-20261126/focused-06/receipt.zip` is 3,767 bytes, SHA-256 `1c2328f25fdcb7b0260891678646c050a9782881c2076fc5ece8767ca7954627`. The report SHA-256 is `a460392ecd505428b31e562415f3e11d8d4630cc09b37b4b9bb44f55be417498`, and the terminal strict log SHA-256 is `781d5839545be53a4e60f610164e995ce72f83dee0d8c0f565d13b768bb18278`. The focused run exited 1 and assigned no acceptance credit.

The preceding `simp` already closed the signed Fourier character goal. The sole Lean delta deletes the unreachable trailing `ring` from `fourier_cuspShift_int`. This is a strict warning repair. All statements, definitions, and other proof text are byte-identical to the previous candidate. The archived namespace repair retains its original bytes. Candidate `5b5e87c022bdaf188ac548b79df33487b0e3f74f`, tree `068c9cb77a4ced2f736faa9a1fd724ac43f77e6e`, binds the active terminal as blob `e11d9a0e41659a76b1502014633da50a5155fabd` (8,230 bytes, SHA-256 `ecbce4b51fac6f743c2319ee1c9e3a984ef044d41c406eff794f8080aa4cfa62`).

```sh
python3 -B verification/verify_p34_fricke_phase.py --expected-head 5b5e87c022bdaf188ac548b79df33487b0e3f74f --output-dir .lake/p34-fricke-phase-focused06-repair-source-check --source-only
git diff --check 22dd5cbc1aec9a8a25e1e424ec1ee60f3c8a04bf HEAD
```

Both commands exited zero. The clean source-only check binds 10 modules and 19 sources. Only the terminal and intake changed. This candidate awaits the next strict probe and complete fresh acceptance gate.

## Focused probe 07 review and publication mapping

Local repaired source `5b5e87c022bdaf188ac548b79df33487b0e3f74f` maps to published source `e84cfd0ee77bb6be687c1f511d666eb478a17737`, both with tree `068c9cb77a4ced2f736faa9a1fd724ac43f77e6e`. The published parent is `9ab1aa96da0b6be512f3040110748a5afb69c4c2`. The 6,178-byte local repair lineage bundle has SHA-256 `8ea308471eb3c20876ddd72def83c5d8082b92a8f9e753b063182c602a2323bf`. Directly hashing all 19 listed source paths at the published Git object verified each focused hash.

Focused task `fe582d4685e64859be14d9a226ae0214` completed in 97.789 seconds with `DIAGNOSTIC_PASSED_NOT_ACCEPTANCE`. It authenticated nine prior project objects, strictly compiled and replayed the terminal, and audited the ten owners. Its 80,903-byte ZIP has SHA-256 `137f3749dedf7727f8f9795427713f01c997455bff33ee9b8938951645862114`. The report SHA-256 is `df538668a709e6473a45a349eb7dd9edf70c4e88c9d673792e4922fae9e26ceb`, and the declaration JSON SHA-256 is `bd645a01fbd6e9e884f1693c0aaf2ce1e3e6d7ed73044fe91604970d3de42954`. All ZIP entries matched the extracted byte streams and passed ZIP integrity checks. The parsed audit log matches all 234 declaration records in order.

The packet ZIP and its manifest bind all 167 packet records at `145be87ff0a88914b607baa2a330bc88105a08d6`. The packet declarations JSON SHA-256 is `11bfb43acdbd6e759f99bfbd418f0420dea93cd2c8ee71ba5c619e0478c5feeb`. Filtering both inventories by the same six providers yields all 101 same records in the same order, with exact equality of full name, defining module, kind, universe parameters, printed type, and ordered transitive axiom list. All six source and object hashes also match.

| Module suffix | Focused records | Explicit original declarations for the four new owners |
| --- | ---: | ---: |
| `Part3CuspPhaseCore` | 7 | |
| `Part3Gamma0ActualCusps` | 11 | |
| `Part3CuspScalingMatrices` | 15 | |
| `Part3ActualCuspWidthNormalization` | 20 | |
| `Part3CuspTranslationFourierPhase` | 10 | |
| `Part3ActualCuspFourierSection` | 38 | |
| `Part3FrickeNormalizer` | 40 | 22 |
| `Part3Gamma0GeneralCuspWidth` | 29 | 16 |
| `Part3Gamma0GeneralCuspUnitPeriod` | 46 | 19 |
| `Part3ActualFrickeCuspPhase` | 18 | 15 |

The four new owners have 133 compiler records, comprising 18 definitions and 115 theorems. Each of the 72 explicit original source declarations appears with its original owner and kind, including private `upperTriangular_signed_translation`. The additional 61 records are generated. All 234 declarations have unique names and complete printed types and contain only the allowed transitive axioms. In this focused audit, 175 records use all three axioms, 37 only `propext`, one `propext` and `Quot.sound`, and 21 use none. The exact union is `propext`, `Classical.choice`, and `Quot.sound`.

The full printed type of `original_cuspOneScaling_eq_fricke` binds the original `normalizedScaling N hN cuspOneMatrix` to the real cast of integral `T` times the literal `frickeSL N hN`, followed by `translationSL`. The printed `normalizedScaling_entries` shows each square-root multiplication and reciprocal-square-root division. The terminal `sigmaOne_fourierCoeff_fricke_phase` quantifies positive natural level, genuine `Gamma0 N` invariance of `F : UpperHalfPlane → Complex`, positive real height, and signed `n : Int`. It uses the genuine unit-period `fourierCoeff`, and the RHS multiplies the actual Fricke Fourier coefficient by `Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ))`. The generated `frickeFourierCoeff.eq_1` binds that coefficient to `fourierCoeff` of the literal Fricke section at the same height. The printed `integrable_sigmaOne_and_phase` retains its `frickeSection` integrability premise and `sigmaOneSection` integrability conclusion under `AddCircle.haarAddCircle` at period one, alongside the same Fourier identity.

The focused receipt and these read-only checks identify the terminal scope. Whole P3.4 and historical D20 remain incomplete, and the manuscript's DI/Whittaker spectral coefficients remain a separate obligation. The fresh 10-owner gate at published source `e84cfd0ee77bb6be687c1f511d666eb478a17737`, task `301f744322e04ab3930207ce04fb2fe1`, still awaits completion and review.

## Fresh ten-owner gate acceptance

Cloud task `301f744322e04ab3930207ce04fb2fe1` ran the shared verifier with the Fricke entry point in 238.635 seconds on published source `e84cfd0ee77bb6be687c1f511d666eb478a17737`, tree `068c9cb77a4ced2f736faa9a1fd724ac43f77e6e`. The exact local repaired commit is `5b5e87c022bdaf188ac548b79df33487b0e3f74f` with the same full tree. The isolated checkout `/workspace/p34-fricke-accepted-20261126` started clean with zero project objects and ended clean on the same head and tree with ten project objects. All 61 stages exited zero. The 10 strict compiles used `-t0 -j1 -M6000 -DwarningAsError=true`; the 10 bundled `leanchecker --verbose` replays name their exact modules. All 11 package pins and cleanliness logs match the bound manifest. The three import-scope regressions passed and the recorded Lean-resolved dependencies use only locked external roots or project objects freshly built earlier in this run. The auditor resolves all ten project objects. The receipt covers this project closure and binds the pinned external dependencies.

The preserved archive in `/workspace/library-files/p34-evidence-staging/continuation-20261126/fresh-full/receipt.zip` has 76 members. ZIP integrity and exact member equality against the extracted records were verified. The evidence identities are:

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `receipt.zip` | 138,095 | `f79a382a6e38841fcd363e032c112b734d5b548168777541e72e5b7283363008` |
| `verification/report.json` | 35,878 | `ee0f48254a402e1ce4a7de2aaca17edd0d720fec4d747c8d0e3478d545334674` |
| `verification/declarations.json` | 1,069,753 | `bd645a01fbd6e9e884f1693c0aaf2ce1e3e6d7ed73044fe91604970d3de42954` |
| `verification/theorem-types.txt` | 943,143 | `3aeeebf03506d22446780d617868e560bb593d214a69914bd2b3bdfc6557e3a2` |
| `provenance/worktree-provenance.json` | 2,000 | `23ae832ab49aaf65355a0d65c91f5d5b4a7a7ecbe5fc148975ea2019e91cde3e` |

I checked the command in each stage log, the exact 19 source bindings by rehashing the published Git bytes, and the ten freshly emitted object hashes. The complete fresh inventory and ten object hashes equal the earlier focused receipt. The 234 fresh records match the serialized audit log in order, and the 194 full theorem strings and axiom lists reconstructed from the inventory match `theorem-types.txt` exactly. Each record has a unique name, the correct owner and kind, a complete compiler type and only allowed transitive axioms. The whole union is `Classical.choice`, `Quot.sound` and `propext`. The six prior providers contribute 101 records identical to the accepted packet archive at `145be87ff0a88914b607baa2a330bc88105a08d6`, including every name, owner, kind, universe parameter, type and ordered axiom list. Their six source hashes and six object hashes also match that archive. The four first-accepted owners contribute 133 records (72 explicit original declarations, including the private theorem, and 61 generated records). There are 194 theorem records and 40 definitions across the ten-owner run.

The full receipt's terminal record types are byte-identical to the exact types inspected under focused probe 07. `original_cuspOneScaling_eq_fricke` binds the actual chart to integral `T`, literal Fricke, and the right-hand translation. `normalizedScaling_entries` retains the square-root and reciprocal-square-root factors. `sigmaOne_fourierCoeff_fricke_phase` quantifies positive level, genuine Gamma0 invariance, positive height, and a signed integer frequency. Its conclusion is the original unit-circle Fourier coefficient identity with phase `Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ))`. `integrable_sigmaOne_and_phase` retains the normalized Haar integrability premise and transfers integrability alongside that exact identity. The generated coefficient equation binds the Fricke coefficient to the unit-circle coefficient of the actual Fricke section. The scope is the fixed-height cusp-one and literal Fricke chart/phase interface. DI/Whittaker normalization, ABL dilation, full P3.4, and historical D20 remain open.

No bound source, intake, dependency pin, or shared validation file was changed in this final receipt review. The prepared source and recorded accepted types are ready for the independent review and coordinator publication closeout.
