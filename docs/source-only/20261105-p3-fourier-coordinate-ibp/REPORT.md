# P3.6 — actual coordinate Fourier IBP, same original 2S and physical frequency

**State:** SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED. P3.6 remains YELLOW.

## Recovery and provenance

- Branch: `chatgpt/p3-internal-original-w-20261105`.
- Checked starting HEAD: `e1cbe7a78d3b1c044445983b33e1e14884ff4659`.
- Prior handoff: `docs/source-only/20261105-p3-fourier-real-complex/REPORT.md`.
- New Lean proof-body commit: `4ea1520f4685277690c70e80b080cc684c69f595`.
- New proof blob: `692a2a14fc87c09dbd6fe7f71c30fe70d7e9abb8`.
- Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F) and `paper/source/manuscript-body.tex`.
- Pinned Mathlib dependency (unchanged): `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Root and packet-level `AGENTS.md` paths were queried and returned GitHub NOT_FOUND. No hidden constraints were inferred. The previous packet's REPORT, REGISTRY, EXTERNAL_INPUTS and the real proof source were read; so were the earlier point/Frechet, signed-square, Fourier derivative and finite D bridge implementations.

## Genuine manuscript-internal increment

The last handoff had a TRUE complex-valued Frechet Fourier derivative identity, a separate exact ordered doubled-list signed-square identity, and the original mixed/Frechet bridge. This packet composes these actual results and eliminates the **Fourier-identity-shaped hypothesis** `CoordinateFourierIBP` from the resulting pointwise (F) candidate on its explicit analytic domain.

`frechet_phase_eq_signed_square` uses the literal Mathlib Fourier multiplier `(-(2*pi*I))^n` and the literal `(-innerSL Real)` factors, evaluated against actual standard coordinate directions. The finite product is rewritten into the very same `doubled S` list (no merged repeats); `doubled_wave_finset` then pays exactly one negative sign per chosen coordinate:

```
phase^(2*|S|) * product_j (-inner(eta,e_(doubled S)_j))
  = (-1)^|S| * product_(i in S) (2*pi*eta_i)^2.
```

`actual_mixed_fourier_signed` instantiates this identity into the real-linear complexified actual mixed derivative Fourier theorem of the prior packet, retaining the actual Point d chart pullback and original mixed variable order.

`actual_coordinate_fourierIBP` then pays the previous `CoordinateFourierIBP` interface directly. The additional multiplication by `(-1)^|S|` cancels exactly; the empty subset identifies the undifferentiated genuine Fourier chart. Its hypotheses are **ordinary finite-order ContDiff and integrability of actual iterated Frechet derivatives for every S**. No Fourier identity or PP estimate is an assumption.

Consequently `actual_mixed_physical_product_bound` and `actual_mixed_physical_decay` consume the old `actual_chart_D_pointwise` and `physical_product_decay` without any `hcoord` parameter. They pay the Euclidean Fourier-space derivative D as a genuine integral sum. This **does not** identify that D with the independent Point d `originalWD` integral, and does not establish admissibility of every physical `W_T`.

## Checks, trust boundary and source-only risks

- GitHub HEAD was checked twice to be the previous exact commit before writing; no concurrent branch writer was observed at those checks.
- GitHub contents write returned the new proof commit `4ea1520f4685277690c70e80b080cc684c69f595`; subsequent readback returned the exact 175-line proof file and blob above.
- Source escape-token scan: 0 matches; delimiter stack scan: balanced.
- Independent finite JS algebra regression: 441/441 cases for d=0..5, all subsets, seven frequency assignments each; 186 odd-cardinality negative-sign controls. This checks the complex-phase square identity on finite samples, **not Lean elaboration or analysis**.
- Pinned Mathlib APIs used by predecessor files were reviewed in their earlier packets. The additional `Fin.prod_univ_fun_getElem` interface was found in publicly documented Mathlib; its **exact pinned version has not been independently confirmed**, and the two scalar-action rewrites and current formal code remain compile-unverified.
- **NOT RUN:** Lean, Lake, kernel replay, CI, full transitive axiom audit, Codex, heavy numerical producer. A static source candidate cannot be promoted green.

## Remaining obligations, exact next entrance

1. Static review/repair of `frechet_phase_eq_signed_square` and `actual_coordinate_fourierIBP` against the pinned Mathlib API. No compilation was performed by this task; all five declarations remain candidate proof bodies.
2. Prove original `Point d` product measure equals the transformed EuclideanSpace Fourier Haar measure with its exact normalization; connect the Euclidean `derivativeD` to `originalWD`.
3. Show the **actual** original physical `W_T` sources satisfy the needed `ContDiff` and integral derivative conditions with **uniform** logarithmic budgets in both T and m(N); do not extrapolate fixed smoothing.
4. Prove normalized Fourier L1, Fubini and quantitative H-box tail (including 2π factors); only then feed a true ε into the same-ρ signed complete-modulus error ledger.
5. Pay complete arithmetic modulus mass including exact complete product T separately; finish causal/whole-box, all HB source words, empty Gamma mothers, high rank/enhanced branches and same-ρ PP assembly.

`EXTERNAL_INPUTS.json` retains only registered medium analytic estimate (M), with version, premises, conclusion and call site; it is not implemented or axiomatized here. No excluded 87-domain changes, production modules, toolchain upgrade, PR, CI or manuscript edits were performed.

## Successor SOURCE_ONLY increment — physical Fourier-space volume and actual D (2026-11-06 UTC)

- **Verified baseline**: `5a30c2aacd02d0e27e294594bc03033f4e2dbba1`. This was identical to the task branch HEAD before the new source was written; no competing branch writer was observed at the checks.
- **New proof-body commit**: `3a673aee966a8f7d4704620081876b3e8c83e4a9` (`[skip ci]`).
- **New source**: `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierPhysicalMeasureD.lean`, 166 lines, exact Git blob `45ea10cb340435ae125f51fa5f8b756db20818ad`.
- **Audit-target updates**: `VERIFY.lean`, Git blob `533011048b451b4e662ce86607885d619d441587`, with imports before checks; no Lean execution.
- **Paper pin unchanged**: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt`, §4 (F), in conjunction with §§1–3 for the original labelled source.
- **Mathlib pin unchanged**: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### Actual mathematical work

The original `Point d = Fin d → ℝ` and Fourier `EuclideanSpace ℝ (Fin d)` do **not** require a guessed Jacobian: the pinned source declares `PiLp.volume_preserving_ofLp` in `Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`; the pinned `EuclideanSpace.equiv` is `PiLp.continuousLinearEquiv 2` with coercion exactly `WithLp.ofLp`. The pinned `MeasurePreserving.integral_comp` transfers Bochner integrals with this continuous linear equivalence as measurable embedding. All three exact dependency declarations were directly inspected in the pinned source.

New `chart_measure_preserving`, `integral_chart`, `mixed_L1_chart` and `actual_derivativeD_eq_pointD` compose the actual **old** `mixed (doubled S)` integrands and their complex-cast norms, with no new surrogate derivative. In particular, for every real original chart weight `w` (no W-class or target PP assumption):

```
derivativeD d (actualMixedFamily w)
  = Σ S : Finset (Fin d), ∫ p : Point d, |mixed (doubled S) w p|
```

`originalWD_eq_actual_derivativeD` specializes this equality to the genuine original `withOriginalW` HB profile and its existing `originalWD` ledger, **without changing any source labels, dyadic group products, complete product, physical modulus or rho**.

`exists_physicalW_fourier_product_polylog` then composes the previous integrated physical original-W theorem with the actual Fourier-space pointwise numerator. On the explicitly stated original physical `PhysicalIntegratedClass` and genuine finite-order `ContDiff`/integrability assumptions (not automatically discharged for every W_T), it yields:

```
physicalDenom (physicalFrequency eta) * ‖𝓕 (actualMixedFamily w ∅) eta‖
  ≤ C * A * (log N)^(E + B*(2*d)).
```

The constant `C` precedes `N`, labelled `W_T`, grouping and m in the inherited quantifier order. It is the physical source and full mixed-L1 bound, **not** a claimed Fourier L1/H tail or full PP theorem.

### Verification boundary

- Pinned Mathlib `PiLp.volume_preserving_ofLp`, `EuclideanSpace.equiv` and `MeasurePreserving.integral_comp` source definitions were read; this is API-source inspection, **not** typechecking.
- New proof file read back from GitHub with blob `45ea10cb340435ae125f51fa5f8b756db20818ad`; banned proof escapes 0; delimiter balance passed in a lexical JS scan.
- Independent SymPy exact polynomial/coordinate-isometry/real-to-complex norm finite regression: **1,111 / 1,111** for d=0..3; this is not a proof of the measure statement.
- **NOT RUN**: Lean, Lake, CI, kernel replay, dependent theorem elaboration, full axiom audit, Codex, heavy producer. The new declarations remain **SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED**, and no node becomes green.
- `EXTERNAL_INPUTS.json` is unchanged: (M) is registered by exact manuscript version/hypotheses/call site, not implemented, used as an axiom, or required to prove this measure lemma.
- No changes to the fixed manuscript, production proof, toolchain or lockfile, the excluded full87 dynamic-parent node, PRs or any other automation branch.

### Real next entry

1. Review elaboration-sensitive uses of the exact pinned `MeasurePreserving.integral_comp` and `PiLp.volume_preserving_ofLp` signatures without triggering compilation here; correct the candidate if the explicit source shows a mismatch.
2. Prove the admitted **physical** `W_T` families' `ContDiff` and integrated mixed Euler derivative bounds uniformly in T and the growing HB length m(N); do not replace this obligation by a target-equivalent structure field.
3. From the now normalized `D`, prove true Fourier `L1` and `H`-box tail with fixed `2π` factors and Fubini. Then feed an actual epsilon to the already defined same-rho signed full-modulus ledger, pay the complete modulus mass and product=T exception separately.
4. Remaining causal/whole-box, complete HB sources, empty Gamma mothers, high-rank/enhanced and full original PP assembly are still internal, not external inputs.


## Successor SOURCE_ONLY increment — exact one-axis Cauchy Fourier normalization (2026-11-06 UTC)

- **Actual checked baseline:** `941e23c967d9e0efcfdb456e3f88b253705088fd`; branch `chatgpt/p3-internal-original-w-20261105`.
- **Source commit:** `2fce316742e82b9654261ec3ad42367c3a87c24d` with `[skip ci]`; proof SHA-1 Git blob `d688ecf5bca8b2cadb1fdb668070b6f11ac6dc3a`.
- **Source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierCauchyAxis.lean`, 85 lines.
- **Manuscript pin:** `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4, formula (F), lines 153–171.
- **Mathlib pin:** `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` (unchanged).

### New actual mathematical work

This packet derives exact elementary ONE-COORDINATE Fourier kernel integrals rather than assuming the full Fourier tail. Let `k(x)=(1+x²)⁻¹`. Pinned Mathlib `integrable_inv_one_add_sq`, `integral_univ_inv_one_add_sq` and `Measure.integral_comp_mul_left` yield source candidate proof bodies for

```
∫_{ℝ} k(x) dx = π
∫_{ℝ} k(2π η) dη = 1/2.
```

The second equality fixes an easy-to-miss normalization: the manuscript integrates physical frequencies with `dξ/(2π)^m`, whereas Mathlib's Fourier integral is in `η`. Each separated `η`-coordinate carries exactly one half of the Cauchy mass, not π or one.

Using the pinned `integral_Iic_inv_one_add_sq`, `integral_Ioi_inv_one_add_sq` and `Real.arctan_neg`, the actual physical-frequency left/right tail mass is

```
∫_{x≤-H} k(x) dx + ∫_{x>H} k(x) dx
  = 2 * (π/2 - arctan(H)).
```

The source also proves its nonnegativity and antitonicity in H (as candidates). It does not replace the separated tails with an integral over a union for negative H; the later H-box cutoff uses H>0.

### Source inspection, tests and risk boundary

- This run **read** the predecessor `REPORT.md`, `REGISTRY.json`, `EXTERNAL_INPUTS.json`, `P3FourierCoordinateIBP.lean`, `P3FourierPhysicalMeasureD.lean`, `VERIFY.lean`, earlier Fourier D and inversion sources, fixed manuscript §4 (F), and pinned Mathlib source.
- Pinned APIs directly read: `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean` (integrability, full and half-line integral identities), `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean` (exact scalar change-of-variables). The pinned arctangent file contains `Real.arctan_neg`, `Real.arctan_le_arctan_iff` and the π/2 inequality.
- Static source escape-token scan returned 0; source delimiters were inspected. Independent finite Simpson quadrature for H in {0, .25, .75, 1, 2, 5, 20} agrees within 0.003334 for physical integrals truncated to ±600; scaled η integral truncated to ±100 agrees within 0.000507. Errors are dominated by intentional finite tails. These are finite sanity checks, not an analytic or Lean verification.
- **NOT RUN:** Lean, Lake, kernel replay, CI, full transitive dependency audit, Codex, heavy producer. Every new declaration remains SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED.
- `EXTERNAL_INPUTS.json` unchanged: only the previously registered restricted medium estimate (M) is recorded; this entire Fourier-kernel step is manuscript-internal. No replacement research assumptions, target-equivalent field or distribution estimate were introduced.
- Did not change production source, manuscript, other task branches, toolchain, full87 excluded node, CI, or PRs.

### Exact next source entry

1. Use the actual finite-dimensional product volume chart plus pinned product/Fubini lemmas to lift the proved-in-source one-axis `1/2` mass to a genuine `(1/2)^d` Fourier `L1` majorant for the original `derivativeD`, including d=0.
2. Establish `2*(π/2-arctan H) ≤ 2/H` for H>0 from the pinned `Real.arctan_inv_of_pos` and a genuine arctangent upper bound. **That upper bound was not found by name in the pinned release and is NOT silently assumed here.**
3. Prove the H-box union, exact `2π` change-of-variable and Fubini tail estimate, with a common threshold uniform in HB length m(N). Only then insert the actual epsilon into the same-rho signed physical modulus ledger, including complete product = T.
4. Still internal and open: actual W_T ContDiff and primitive integral norms for every original geometry label, causal/whole-box licenses, all HB source families, empty Gamma mothers, high-rank and enhanced PP and final same-rho assembly.

**Status:** P3.6 YELLOW. One-axis exact integral candidate BLUE only. No GREEN nodes.

**Post-readback static repair:** Reordered the new `VERIFY.lean` import ahead of all `#check` commands; the prior appended import was structurally misplaced. No compilation or kernel check was performed.


## Successor SOURCE_ONLY increment — pinned elementary H⁻¹ physical Fourier-axis tail (2026-11-06 UTC)

- **Baseline HEAD**: `684c16f7e6791e5e7af901ad924f3fb9194425d5`; **new proof commit**: `0566b44f1c5ee96ba579e3818625c7b3eb8e603a` (`[skip ci]`), source: `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierCauchyTail.lean`, Git blob: `4f5a310b653aacd8c9ffe174d510c6c3b8b1fd8c`.
- **Pin**: manuscript `9731290e8f53cffda44129906cde6a965eaa869b` §4 (F), physical Fourier convention `xi=2*pi*eta`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. External registry (M) unchanged.
- **Genuine proof-body content**: The pinned `Trigonometric/Bounds.lean` contains `Real.le_tan` while its `Real.arctan_le_self` shortcut does not yet exist. Applying `Real.le_tan` to `Real.arctan x`, and using `Real.tan_arctan`, proves `Real.arctan x <= x` for `x>=0` without importing a future API. Then `Real.arctan_inv_of_pos` and the previous exact pair-tail integral establish `axisPairTail H <= 2/H` for `H>0`. Nonnegative real `D` gives `D*axisPairTail H <= 2D/H`; a concrete `2D <= eps*H` yields the epsilon spend. These are one-dimensional manuscript-internal candidate proofs, not an assumed truncation bound.
- **Declarations**: `P3FourierCauchyTail.arctan_le_self_nonneg`, `axisPairTail_le_two_div`, `axisPairTail_L1_budget`, `axisPairTail_spend`.
- **Direct pinned-source evidence**: Read `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` (contains `Real.le_tan` at line 214), `Arctan.lean` (`Real.arctan_nonneg`, `Real.arctan_inv_of_pos`), and the exact previous `P3FourierCauchyAxis.lean`. Import order and signatures are candidates until Lean elaboration.
- **Static and independent checks**: forbidden-source escape-token scan 0; lexical delimiter balance PASS; 14 positive-H values checked against `pi-2*atan(H) = 2*atan(1/H) <= 2/H`, 70 one-axis budget and 210 cutoff numeric cases. Floating model checks do not certify Lean analysis.
- **NOT RUN**: Lean/Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. No green status.
- **Open internal**: genuine finite-dimensional product-volume/Fubini separation and normalized Fourier L1; H-box union and *uniform* original W_T derivative budgets; same-rho full physical modulus arithmetic mass including exact complete product T; causal, HB all sources, empty Gamma, high-rank/enhanced assembly. The new one-axis 1/H inequality does **not** imply mD/H without Fubini and does not pay arithmetic discrepancy.
- **Scope unchanged**: no fixed-manuscript, toolchain, production, excluded full87, other-task-branch, PR or CI edit. External (M) remains registered only.

## Successor SOURCE_ONLY increment — separated finite-axis Fourier H-box algebra (2026-11-06 UTC)

- **Actual baseline HEAD**: `7baca9bab7d2001873a2cb718e236ecd2db8c318`; **confirmed pushed source commit**: `687ef58dbac0813ca38a02de9b2dc441acf167af` (`[skip ci]`).
- **Proof**: `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierBoxTailAlgebra.lean`, 140 lines, Git blob `eaf46b6c3eaa107cf821d17b4632074b4777720e`. `VERIFY.lean` blob `230fcde42e079260be9c754ef0d5126362e99da5`. Full manuscript pin `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F), lines 153–171; fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- **Scope of new Lean proof bodies**: `pow_gap_le_linear` proves `a^d-b^d ≤ d(a-b)` when `0≤b≤a≤1`, by genuine finite induction (including `d=0`). `normalizedAxisRemoved_bounds` uses the previously derived exact arctangent tail to show that `t(H) = axisPairTail(H)/(2π)` is between 0 and 1/2 for nonnegative H. `normalizedAxisRemoved_le_inv` uses the previous real inequality `axisPairTail(H)≤2/H` and `π≥1` to pay `t(H)≤1/H`.
- **New nontrivial finite-dimensional inequality**: `separatedBoxMassLoss d H = (1/2)^d - (1/2-t(H))^d ≤ d/H` for `H>0`. The two final theorems pay a nonnegative actual derivative budget `D` and an explicit `dD≤εH` scalar cutoff. This controls the *separated product of exact one-axis masses*, **NOT YET** the genuine Fourier integral over the `EuclideanSpace` complement of the original H-box.
- **Independent checks**: Source forbidden-proof-escape token scan 0; lexical delimiters balanced; 250 numerical checks (d=0..24, 10 strictly positive H values) all respected nonnegative removed mass and `separatedBoxMassLoss≤d/H`. Finite tests do not establish the Lean theorem or any Fubini identity. Source and `VERIFY` read back from GitHub with exact registered Git blobs. Baseline HEAD checked before ref write, ref fast-forward confirmed; no concurrent branch change observed.
- **NOT RUN**: Lean, Lake, kernel replay, CI, full transitive axiom audit, Codex or heavy numerical producer. **SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED**. No green nodes.
- **No expanded assumptions**: No `CoordinateFourierIBP` or Fourier-tail-shaped premise, no additional research input, no new declaration of classical distribution results. `EXTERNAL_INPUTS.json` unchanged, Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; (M) remains record-only and not implemented. No modifications to manuscript, master, production, full87 excluded node, other tasks, PRs or toolchain.
- **Precise remaining chain**: Prove actual finite-dimensional product-volume/Fubini equality with `(1/2)^d` and complement `(1/2)^d-(1/2-t(H))^d` (including all change-of-variable factors). Only then apply the above scalar result to the actual Fourier `L1`/H-box integral, then absolute same-rho complete-modulus error with `b=T` term separately; independently verify actual full `W_T` family smoothness, integrable mixed derivatives and uniform m(N), causal/whole-box licensing, HB word coverage, empty Gamma mothers and high-rank/enhanced PP.

**Pinned-source import correction (same round):** Directly inspected `leanprover-community/mathlib4@e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, `Mathlib/Analysis/Real/Pi/Bounds.lean` (Git blob `86147be4daf2ed3b598f0aed9ff73822336f0e2a`), confirming `Real.pi_gt_three`. Added an **explicit import** so this inequality does not depend on unverified transitive imports. Also verified the four imported tactic file paths exist at that Mathlib pin. Corrected proof source blob `7e8dfe342b5c34b94031732fdca97f4e16490870`; no Lean elaboration performed.

## Successor SOURCE_ONLY increment — actual finite-volume Fubini and Fourier L1 (2026-11-06 UTC)

- **Verified previous HEAD:** `d77c3f949cc9128d7a7c896a011339d1064f9b02`; **pushed source commit:** `01873f973d9419214735d18b2f55615e757154ba` (`[skip ci]`).
- **Branch:** `chatgpt/p3-internal-original-w-20261105`; same packet and unique handoff record.
- **Added source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierProductFubini.lean`, 157 lines; Git blob `b29c12f9c4ee8f4543132577409e2c038c76ad6d`; `VERIFY.lean` 55 lines, Git blob `8b8d441633b9c4942edb0c5912c6be9c3338f6ef`.
- **Fixed manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4, formula (F), lines 153–171; linked to `paper/source/manuscript-body.tex`.
- **Fixed Mathlib:** `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` (unchanged). Directly read `Mathlib/MeasureTheory/Integral/Pi.lean`, including `Integrable.fintype_prod` and `integral_fintype_prod_volume_eq_pow`; `Mathlib/MeasureTheory/Constructions/Pi.lean`, identifying Point volume with finite `Measure.pi`; `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`, including the exact nonzero scalar integrability transformation `integrable_comp_mul_left_iff` and real integral scaling; and `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`, including `Integrable.mono_nonneg`. API names and context inspected at pin; Lean elaboration NOT RUN.

### Genuine internal mathematical work

Let `Point d = Fin d → ℝ`, `FourierSpace d = EuclideanSpace ℝ (Fin d)`, and `k(η)=1/(1+(2π η)^2)`. The new source constructs `pointKernel d p = ∏ i, k(p i)`, not a surrogate Fourier transform. Using the real `volume` product measure and a pinned finite-dimensional Fubini theorem, it gives source-candidate statements for `Integrable (pointKernel d)` and

```
∫ p : Point d, pointKernel d p = (1/2)^d.
```

Using the *previously implemented* actual measure-preserving `chartEquiv d`, it transfers this equality to the real `EuclideanSpace` Fourier measure and integrability. The exact algebra identifies the integrand with `(physicalDenom (physicalFrequency η))⁻¹` (including d=0), not a radial denominator. Hence the new `physical_inverse_denom_mass` expresses a genuine multi-axis integral identity, not the previous scalar-only separated mass.

`actual_derivativeD_nonneg` reuses the original ordered doubled mixed-derivative integrals. `actual_fourier_L1_bound` then consumes the prior `actual_mixed_physical_decay`, actual `derivativeD`, product integrability, and ordinary `AEStronglyMeasurable` of the Fourier norm, to obtain the candidate genuine L1 bound:

```
∫ η : FourierSpace d, ‖𝓕 (actualMixedFamily w ∅) η‖
  ≤ derivativeD d (actualMixedFamily w) * (1/2)^d.
```

Premises are the **previous literal 2S finite-order ContDiff and iterated Frechet derivative integrability** plus ordinary Fourier-norm measurability. The latter remains an explicit manuscript-internal analytic condition, not a Fourier majorant/PP conclusion; proving it automatically from the admitted source is still open. The actual W_T family is NOT universally admitted by this proof.

### Checks and exact trust boundary

- New source forbidden proof escapes: 0; lexical delimiter-balance: PASS.
- Independent finite trapezoid check over η∈[-25,25] gave axis mass 0.49797360361801285 and d=0..5 6/6 separated product checks, maximal absolute error 0.00202639638198715 against exact (1/2)^d; finite cutoff explains the nonzero error. This is a **numerical sanity check only**.
- GitHub tree commit created from exact verified prior HEAD and pushed using non-force ref update with exact expected SHA. Source and VERIFY Git blob IDs returned directly by GitHub.
- **NOT RUN:** Lean/Lake, kernel replay, CI, full transitive axiom audit, Codex, heavy producer. All new declarations remain SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED, with no green status.
- `EXTERNAL_INPUTS.json` unchanged, Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. Restricted medium (M) remains **record-only**, not implemented or added as a new axiom. No manuscript, production proof, toolchain/lock, excluded full87 node, PR, other branch or external board changes.

### Exact next internal entrance

1. Pay `AEStronglyMeasurable` of the actual Fourier norm from genuine prior `k=0` integrability and the pinned continuity/Fourier transform API, without assuming the desired L1 bound.
2. Prove the genuine one-axis *restricted* integral `∫_{|2π η|≤H} k(η) = 1/2 - t(H)` at fixed H>0, then genuine finite-dimensional `Set.pi` product integral, complement/set-additivity, and combine with `separatedBoxMassLoss_le_dim_div`. The above full-volume Fubini does NOT prove the H-box tail by itself.
3. Quantify `W_T` ContDiff and mixed integrated budgets across all original labelled HB sources, T and m(N), then feed the true finite Fourier epsilon to the complete signed same-rho physical modulus sum. Still independently pay full arithmetic mass, b=T exception, causal whole-box licences, all HB mother words (empty Gamma), high rank/enhanced and final PP assembly.

**Status:** P3.6 YELLOW. New finite-volume Fubini + explicit-premise Fourier L1 proof bodies BLUE only; zero GREEN.


## Successor SOURCE_ONLY increment — original Fourier-norm measurability from genuine zero-order L1 (2026-11-06 UTC)

- **Exact recovered predecessor HEAD:** `91e457cae21d7d69816d145ab3d65640d9c58499` on `chatgpt/p3-internal-original-w-20261105`.
- **Confirmed pushed proof/VERIFY commit:** `7a259379fc28b28f48f01d197da0c196a18c3443` (`[skip ci]`); source `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierAutomaticMeasurability.lean`, 78 text lines, Git blob `fb7c65efaad78a75258ed841aa25f101523a41bc`; VERIFY Git blob `df34ed18d0e249d9faea9f1f6f5e4baa1e5b65cf`.
- **Fixed source pins:** manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F), and `paper/source/manuscript-body.tex`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### Real internal theorem candidate

The predecessor `actual_fourier_L1_bound` genuinely integrated the physical product Cauchy kernel over `EuclideanSpace ℝ (Fin d)`, but separately assumed `AEStronglyMeasurable` of the norm of the actual Fourier transform. This round derives **that property from the pre-existing ordinary L1 integrability** instead of assuming it or proving any target-shaped Fourier bound.

1. `actual_mixed_empty_eq_chart` identifies `actualMixedFamily w ∅` with `complexChartLift w` by unfolding the original `mixed (doubled ∅)`. All original coordinates, labels and multiplicities remain unchanged.
2. `fourier_continuous_of_integrable` specializes the ACTUAL PINNED `VectorFourier.fourierIntegral_continuous`, with `Real.continuous_fourierChar` and `(innerSL ℝ).continuous₂`, to the same real Euclidean Fourier-space Haar volume; its only assumption is `Integrable f`.
3. `actual_fourier_norm_aestronglyMeasurable` obtains ordinary Fourier-norm a.e. strong measurability via `Continuous.norm`, after rewriting the original zero derivative.
4. `actual_fourier_L1_no_meas` invokes `hintegrable ∅ 0` to obtain integrability of `complexChartLift w` and consumes the previous `actual_fourier_L1_bound` **without** its independently stated Fourier measurability premise. The conditional source conclusion stays
   `∫ η, ‖𝓕 (actualMixedFamily w ∅) η‖ ≤ derivativeD d (actualMixedFamily w) * (1/2)^d`.

### Checks, qualifications and next entrance

- Directly inspected the pinned `Mathlib/Analysis/Fourier/FourierTransform.lean` with the genuine `VectorFourier.fourierIntegral_continuous` signature and its direct application in `Lp.fourierTransform`; directly inspected predecessor `P3FourierProductFubini.lean`, `P3FourierRealComplex.lean`, `P3FourierFrechetIBP.lean` and `P3FourierDPointwise.lean`, and fixed manuscript §4 (F). This is API/source inspection, not typechecking.
- Initial static delimiter check found and **fixed** one extra opening parenthesis in the draft `change` expression, before any GitHub write. Final new source delimiter balance PASS; banned proof escape tokens 0; VERIFY imports precede all `#check` declarations.
- GitHub tree creation, signed-less commit and expected-SHA non-force ref update confirmed. Subsequent file readback confirmed exact new source Git blob `fb7c65efaad78a75258ed841aa25f101523a41bc` and VERIFY blob `df34ed18d0e249d9faea9f1f6f5e4baa1e5b65cf`; original `EXTERNAL_INPUTS.json` remains Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. No other files changed in the proof commit.
- The `simp` unfolding of `doubled` / `mixed` at the empty set and `simpa` on `iteratedFDeriv ℝ 0` remain **Lean elaboration-sensitive, uncompiled candidate** steps. DO NOT mark this green or treat static checks as kernel acceptance.
- **NOT RUN:** Lean, Lake, CI, kernel replay, complete transitive axiom audit, Codex, heavy producer. No new axiom or research estimate; medium (M) is still registered only. No changes to manuscript, production source, lockfile, other branches, PR, external boards, or excluded full87 node.
- **Next concrete entrance:** prove genuine one-axis restricted Fourier integral `|2π η|≤H` with exact `1/2 - normalizedAxisRemoved H` via measure splitting; then Fubini on the real `H`-box and its complement, and integrate the true Fourier majorant to obtain `dD/H`. Separately pay original `W_T` all-family uniform derivatives in `T,m(N)`, same-`rho` complete modulus mass, the exact complete product `b=T` exception, causal/all-HB/empty-Gamma/high-rank/enhanced PP obligations.

**Status:** P3.6 YELLOW; this exact limited Fourier-measurability source is BLUE only, NOT Lean-compiled or kernel-verified. No GREEN nodes.


## Successor SOURCE_ONLY increment — genuine physical H-box integral (2026-11-06 UTC)

- **Baseline:** verified GitHub HEAD \`9be88267f54ab44cf399ee62d647ad50b7f9ddb0\` on \`chatgpt/p3-internal-original-w-20261105\`. Source commit \`2450babd0a36ee43cd6a5b7b8f2cea0e9e0823a3\`, nonzero-pi tactic repair \`daeb2a674215bcc64237d7f99224899481943395\`; both \`[skip ci]\`. New source \`P3FourierRestrictedBox.lean\` (225 textual lines), exact Git blob \`5438ef47dd9fe272f7b5d6bded8f8f3d33771cc2\`.
- **Fixed sources:** manuscript \`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, \`paper/source/modules/distribution-prime-product-completion-20261010.txt\` §4 (F), lines 153–171, with no automatic master update. Mathlib fixed pin \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`. Directly inspected actual \`Measure.integral_comp_mul_left\` in Haar/NormedSpace, \`integral_add_compl\`, \`setIntegral_union\`, \`setIntegral_compl\`, \`integral_indicator\` in Bochner/Set, and finite product Fubini in Integral/Pi. No AGENTS.md was found at the repository root or relevant ancestors.
- **Actual mathematical increment (source candidate):** the *unscaled* Cauchy kernel has a true restricted set integral over \`Ioc (-H) H\`, equal to \`pi - axisPairTail H\` for \`H>=0\`. The complement is the disjoint union \`Iic (-H) ∪ Ioi H\`. Scaling by the true physical \`2*pi\` yields \`integral scaledAxisInside H = normalizedAxisInside H = 1/2 - axisPairTail H/(2*pi)\`. This preserves both endpoints and never adds an unlicensed boundary correction.
- In the original \`Point d = Fin d -> Real\`, \`pointInsideKernel\` is identified pointwise with the **indicator of the measurable physical H-box** times the previously implemented \`pointKernel\`. Actual finite Fubini gives \`∫_{pointBox} pointKernel = normalizedAxisInside(H)^d\` (also d=0). The same fixed isometric measure-preserving chart gives \`∫_{fourierBox} fourierKernel = normalizedAxisInside(H)^d\` on the genuine \`EuclideanSpace\` Fourier measure. Thus its **genuine complement set integral** is \`separatedBoxMassLoss d H\`, bounded above by \`d/H\` for H>0 via the previously proved candidate scalar inequality. This has *not* yet been multiplied by the true Fourier majorant D or applied to a truncated inversion.
- **Finite independent sanity check:** 200 cases (d=0..24, H in {0, 0.01, 0.2, 1, 2.5, 9, 50, 200}), max scalar residual \`5.551115123125783e-17\`, all checked H>0 obey nonnegative mass and d/H. This is NOT a Lebesgue theorem test or Lean verification.
- **Static checks:** source disallowed-escape scan 0; balanced parentheses/brackets/braces after comment stripping. The initial static scan rejected comment punctuation and did not write; this was corrected. A later proof-source patch explicitly uses \`field_simp [hne]\` for nonzero pi. GitHub SOURCE and module hashes checked. **NOT RUN:** Lean, Lake, CI, kernel replay, whole-axiom audit, Codex or heavy producer. All declarations remain potential elaboration-sensitive candidates and are BLUE only; no node GREEN.
- **External input boundary:** \`EXTERNAL_INPUTS.json\` unchanged (blob \`8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab\`); restricted signed medium (M) remains RECORD_ONLY, NOT_IMPLEMENTED, NOT_AXIOM. No new axioms, target-shaped hypotheses, production proof edits, manuscript edits, external board changes, other task changes or excluded full87 node changes.
- **Next exact internal entry:** use \`actual_mixed_physical_decay\` plus nonnegative \`actual_derivativeD\` and real Fourier norm measurability to dominate the genuine complement Fourier *norm* set integral by \`D*d/H\`; then connect Fourier inversion and uniform original W_T/hb families before full signed same-rho physical modulus sum, separate \`b=T\` arithmetic mass, causal licences, complete HB/empty-Gamma and high-rank/enhanced cases. SOURCE closure, compilation/kernel verification and the registered external estimate remain distinct.

## Successor SOURCE_ONLY increment — actual Fourier H-box transform-norm tail (2026-11-06 UTC)

- **Recovered exact prior HEAD:** `9187b9fc71d144c7480035a9c28751ad6e95928b`, branch `chatgpt/p3-internal-original-w-20261105`. No concurrent write was observed before the new source or each subsequent file update.
- **Actual new proof commit:** `47de2dbb951191f6295cc23d05b8e11a5cf9ca08`, message with `[skip ci]`. Source: `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierActualBoxTail.lean`, 131 nonempty-final-newline-normalized text lines, Git blob `add9965f4602db8e7f6ff8f6220ed165540b4466`.
- **Subsequent audit-target commit:** `11cbc36a6647c0d20730b5ac67d5a2a35efe32f6`; `VERIFY.lean` blob `497ee27c6e812440dd6d6085ef69e6a6aaa283c8`.
- **Structured registry commit:** `8377e294daa3413c8d128e1b868fa7520f890bfa`; `REGISTRY.json` blob `d31b9c281dcb3f4ccddf9b7cf302e1bc93a5142e`. The report itself is committed subsequently; its resulting HEAD is recorded by the GitHub write and final notification. The external registry is unchanged, Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`.
- **Pins:** Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F), lines 153–171, and `paper/source/manuscript-body.tex`. Fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### Actual mathematical proof source

The preceding run derived the **genuine restricted Euclidean H-box Cauchy kernel mass**, not the norm of the Fourier transform. This round uses the ACTUAL original test weight `w : Point d → ℝ`, its ordered `mixed (doubled S)` family and the same Fourier chart and physical 2π scale to make the missing transition. On ordinary explicitly quantified finite-order ContDiff and integrable iterated Fréchet derivatives:

1. `actual_fourier_norm_integrable`: obtain zero-order integrability from `hintegrable ∅ 0`, apply previously sourced Fourier continuity and hence `AEStronglyMeasurable` of the actual Fourier norm, then apply pinned Mathlib `Integrable.mono_nonneg` to the actual pointwise majorant `D * fourierKernel d`. This does **not** assume a Fourier estimate or measurability as a fresh premise.
2. `actual_fourier_box_tail_bound`: apply **pinned** `setIntegral_mono_on` on the actual complement `(fourierBox d H)ᶜ` with the two genuine integrable functions; pull the original derivative budget `D = derivativeD d (actualMixedFamily w)` outside using `integral_const_mul`; consume `fourierBox_complement_mass` and `separatedBoxMassLoss_budget`. The resulting genuine Fourier norm set-integral candidate is
   `∫ eta in (fourierBox d H)ᶜ, ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤ (d:ℝ) * derivativeD d (actualMixedFamily w) / H`
   for H>0, including d=0, with no artificial H^d.
3. `actual_fourier_box_tail_spend`: the explicit scalar cutoff `d*D ≤ eps*H` pays the same actual Fourier tail ≤ eps. This is not a physical modulus discrepancy estimate. The full original W_T all-family admission, quantitative m(N) uniformity, truncated inversion and arithmetic payment remain UNSOLVED.

The result is limited to the stated genuine analytic hypothesis domain. No extra sparse-fiber relative-Theta requirement, no redefined rho or modulus, no absolute-to-relative estimate, and no fixed-smoothing-to-growing-m shortcut were introduced.

### Checked source APIs and verification boundary

- Direct pinned Mathlib source read: `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` `Integrable.mono_nonneg`; `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` `setIntegral_mono_on`, whose exact signature takes two `IntegrableOn` arguments, `MeasurableSet` and pointwise set inequality; `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` `integral_const_mul`. The fixed predecessor Fourier and H-box source files were also actually read. This inspection does NOT validate Lean elaboration.
- Static forbidden proof-escape scan: 0; stripped-comment delimiter stack: PASS; new source and `VERIFY.lean` import/check placement readback confirmed. Source blob `add9965f4602db8e7f6ff8f6220ed165540b4466`.
- Independent Python scalar regression: 363 cases, d=0..32 and 11 positive H values, checking the exact normalized Cauchy mass and `D * loss ≤ d*D/H`; maximal nonzero ratio ~0.31831. This is not a Fourier/Lebesgue/Lean verification.
- **NOT RUN (per this task's restriction):** Lean, Lake, CI, kernel replay, full transitive axiom review, Codex, heavy numerical producer. All three new declarations are **SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED**; the P3.6 parent remains YELLOW; no new GREEN status.
- **External (M):** unchanged `EXTERNAL_INPUTS.json` and RECORD_ONLY_NOT_IMPLEMENTED_NOT_AXIOM; no external research theorem was re-proved or declared as an additional assumption.
- No production modules, source locks, fixed manuscript, external board, other task branches, excluded 87-domain dynamic parent, PR or CI were altered.

### Next concrete entrance

1. Connect the now genuine integrable complement Fourier norm to the **truncated Fourier inversion** of the actual original smooth geometric weight, preserving the exact character/2π normalization. Obtain the explicit supremum truncation error; do not silently assume pointwise inversion of an arbitrary L1 weight.
2. Independently discharge original **all-family** `W_T` ContDiff and integrated derivative bounds uniformly in T and growing HB m(N), then choose one common logarithmic H for all original source labels and fixed orders.
3. Only after this analytic payment feed the resulting epsilon to the same integer rho, original labelled physical moduli and coprime mean, including complete product=T arithmetic mass. Causal/whole-box, all HB words, empty Gamma mother words, high-rank/enhanced alternatives and full PP remain internal obligations.


## Successor SOURCE_ONLY increment — actual truncated Fourier inversion and same-rho finite signed source (2026-11-06 UTC)

- **Verified parent branch HEAD:** \`2de3e091df064a4b3451459f3b4b36c30664af9e\`.
- **Source/VERIFY commit:** \`a10bc7fd32236e5494e9ac55f3e7c85317d7a6ca\`, fast-forward with \`[skip ci]\`.
- **Exact candidate source:** \`docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FourierActualInversion.lean\`, finalized Git blob \`e4438b319eb72afac59330cc889bb3cac57a3d9a\` (one later explicit \`ContinuousAt\` elaboration-risk repair in handoff commit).
- **VERIFY source Git blob:** \`faa759ff323ce7e69c7f1dce11c93cfb0680f669\` with new imports preceding any #check and eight new check targets, *not executed*.
- **Pinned paper:** \`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, \`paper/source/modules/distribution-prime-product-completion-20261010.txt\` §4 (F), pp. on Fourier cutoff and full modulus mass.
- **Pinned Mathlib:** \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`.

### Genuine manuscript-internal change

This packet composes the true previous \`P3FourierActualBoxTail.actual_fourier_box_tail_bound\` with the *pre-existing actual* \`P3FourierCutoffIdentity.fourier_cutoff_error\`. The former supplies the previously missing H-box complement L1 bound; the latter already proved the inverse Fourier integral identity with the pinned exp(+2 pi i inner(eta,x)) normalization. A new theorem \`actual_fourier_integrable\` derives integrability of the original zero-order transform from the previous real-norm L1 theorem using the exact pinned \`integrable_norm_iff\`, and \`actual_zero_continuous\` uses the original S=empty finite-order ContDiff rather than assuming an inversion conclusion.

The source candidate \`actual_truncated_inverse_error\` yields for every actual Fourier-space point \`x\`:

    norm(actualMixedFamily w empty x - actualTruncatedInverse w H x)
      <= d * derivativeD d (actualMixedFamily w) / H

for H>0 and the same literal original ordered doubled-S regularity and genuine iterated-Frechet-integrability hypotheses. \`actual_zero_real\` converts the zero-order complex mixed function back to the **actual original real Point d weight** \`w (chartEquiv d x)\`. \`actual_real_truncated_inverse_error\` gives its real-part cutoff approximation error, without a target-shaped Fourier estimate premise.

The final new \`actual_same_rho_signed_cutoff\` inserts this proved-in-source geometric real-part approximation directly into the **existing** \`P3FullSignedModulusTail.signedSource_approximation\`, using the SAME \`rho\` for both sides, literal \`originalProducts\` and the original finite source. It gets the *conditional* algebraic inequality

    abs(signedSource(original real w) - signedSource(actual truncated inverse real))
      <= (d * D / H) * fullModulusMass(Q,source,rho,coefficient,T,originalProducts).

No \`htail\`, \`hF\`, independently postulated cutoff identity or new arithmetic distribution estimate is required. The right-hand \`fullModulusMass\` is the previously defined genuine complete-modulus mass, NOT shown small. This is **not** a PP proof, nor an upper bound for the T=exact-product exception.

### Scope and checks

- Direct source reads: prior exact Fourier inversion packet \`P3FourierCutoffIdentity.lean\`, current \`P3FourierActualBoxTail.lean\`, \`P3FourierAutomaticMeasurability.lean\`, original \`P3FullSignedModulusTail.lean\`, same-pinned manuscript §4, latest packet REPORT/REGISTRY/EXTERNAL_INPUTS, and pinned Mathlib \`Analysis/Fourier/Inversion.lean\`, \`Analysis/Fourier/FourierTransform.lean\`, \`MeasureTheory/Function/L1Space/Integrable.lean\`.
- Pinned APIs inspected in actual source: \`MeasureTheory.Integrable.fourierInv_fourier_eq\` (integrable f, Fourier integrable, continuity), \`Real.fourierInv_eq\`, and \`integrable_norm_iff\`. Existing cutoff error source supplies the complement Bochner-integral estimate.
- New source lexical delimiter balance PASS; 0 forbidden proof-escape tokens found (source includes no sorry/admit/new axiom/unsafe/native_decide). Independent 600 deterministic finite signed-source comparisons with signed rho, exact congruence and true coprime mean passed. The Gaussian 1D 2*pi physical truncation sanity check passed for six H values. **These are not Lean elaboration or kernel checks.**
- **NOT RUN** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex or heavy producer. Typechecking of new and all predecessor SOURCE_ONLY files is outstanding; the finite Mathlib API inspections cannot certify compilation.
- **External registry unchanged**, SHA \`8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab\`: restricted medium (M) is merely registered with pinned version, stated assumptions and intended call site. No replacement axiom, external theorem implementation, imported distribution conclusion or target-equivalent PP hypothesis.
- The fixed manuscript, production source, toolchain, user-excluded full87 parent node, PRs, other task branches and CI were untouched.

### Exact next entrance

1. Independently inspect elaboration-sensitive composition of \`actual_zero_continuous\`, \`integrable_norm_iff\`, \`actual_truncated_inverse_error\`, and its predecessor imports against the locked Mathlib; **do not mark green without actual Lean/kernel evidence**.
2. Prove admission of **every actual allowed physical W_T source** to original ContDiff and integrable derivative family with uniform quantitative bounds in N and growing m(N). Then pick a single log-power H covering the post-modulus mass, rather than treating fixed smoothing as uniform.
3. Prove \`fullModulusMass\` bound AFTER the *complete* same-rho modulus sum, separating exact complete product=T from off-diagonal so \`tau(0)\` never occurs. Preserve auxiliary vs physical levels and all labels/multiplicities. Then complete causal/whole-box, HB all source words, empty Gamma mother, high-rank/enhanced and final PP assembly.

**P3.6 remains YELLOW. This packet is BLUE only for the named candidate source scope, NOT compiled or kernel accepted.**


## Successor SOURCE_ONLY increment — full same-rho mass to a nonzero shifted divisor, exact b=T and coprime mean (2026-11-06 UTC)

- **Actual recovered task HEAD:** \`e399891eb18de3bdabd9ea41887b763e02011fe0\`, on \`chatgpt/p3-internal-original-w-20261105\`. Prior REPORT, REGISTRY, EXTERNAL_INPUTS, true Fourier inversion, original signed-source mass, physical W integration and the pinned manuscript were read. Root, docs, source-only and packet \`AGENTS.md\` queried: GitHub NOT_FOUND, no hidden instructions assumed.
- **Source/VERIFY commit (confirmed GitHub write):** \`33495bfe41cc8283f15f80c25ea31ea9325c5f1e\` (\`[skip ci]\`). **New file:** \`docs/source-only/20261105-p3-fourier-coordinate-ibp/P3FullModulusShiftedMoment.lean\`; exact Git blob \`30d9f2e9d0dea09664eedeb66c53f61fa4e3ff3f\`; \`VERIFY.lean\` blob \`796356aecfae3b723aa279d5c9f5df0394d0f98e\`.
- **Pinned paper:** \`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, \`paper/source/modules/distribution-prime-product-completion-20261010.txt\` §4 after (F), including the complete modulus sum, off-product shifted moment and separately handled b=T. **Pinned Mathlib:** \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`. The exact \`Nat.modEq_iff_dvd\` declaration was read in pinned \`Mathlib/Data/Nat/ModEq.lean\`; this is source inspection, NOT Lean elaboration.

### Concrete new manuscript-internal arithmetic reduction

This run tackles the **previously untouched complete arithmetic mass** rather than adding another Fourier wrapper. It reads the real predecessor \`fullModulusMass\`, \`kernelMass\`, \`exactCoprimeTest\`, \`signedSource\`, and the existing \`fullModulusMass_split\`. The new \`kernelMass_eq_shifted\` identifies the ORIGINAL congruence test with integer divisibility:
\`b % q = T % q\` iff \`(q:ℤ) ∣ (T:ℤ) - (b:ℤ)\`; no physical/auxiliary level replacement.

For original source tuples with full original group product **b≠T**, \`off_shift_ne_zero\` makes the integer shift provably nonzero. The off-diagonal full mass is exactly the sum of (i) the same signed-rho ABSOLUTE modulus weights against the genuine shifted divisor indicator; and (ii) the **exact** coprime mean, not an unrestricted one. The second term is then bounded by \`offCoefficientMass * meanRhoMass\`, using only \`|coeff|\` nonnegativity and the original totient denominator.

For **b=T** and the manuscript's original admissible \`(q,T)=1\`, \`exact_kernel_mass\` yields exactly \`1+1/phi(q)\`. \`exact_mass_factor\` therefore factors the complete exact-T mass as \`exactCoefficientMass * exactRhoMass\` with the q-sum preserved. In particular this is NEVER included in a shifted-divisor moment at zero.

Combined \`full_mass_le_shifted_and_exact\` gives the explicit candidate inequality:

\`\`\`
fullModulusMass(Q,source,rho,coefficient,T,originalProducts)
  <= exactCoefficientMass(source,coefficient,T,originalProducts)*exactRhoMass(Q,rho)
     + offShiftedResidueMass(Q,source,rho,coefficient,T,originalProducts)
     + offCoefficientMass(source,coefficient,T,originalProducts)*meanRhoMass(Q,rho).
\`\`\`

**The arithmetic estimates on these three factors are NOT proved:** in particular neither the near-linear shifted divisor moment, nor the fixed-power b=T exceptional coefficient bound, nor a uniform mean-rho summatory bound. This is an authentic finite signed-modulus/specific-complete-product reduction, *not* a PP or Fourier family completion. It also does not falsely make \`rho\` nonnegative or alter any labels, multiplicities, coprimality tests or the full product.

### Checks, limitations and next actual work

- SOURCE_ONLY syntactic delimiter check PASSED, forbidden proof escapes 0. \`VERIFY.lean\` imports all candidate targets before \`#check\`; it was NOT executed. Source and VERIFY blob SHA confirmed via GitHub readback.
- Independent deterministic Python finite exact-arithmetic regression: **800/800** cases (four HB group lengths including zero, five target values, 40 source/rho samples), testing exact full mass = exact-T + shifted-off + exact off mean, and the mean upper bound; maximum floating residual \`5.684341886080802e-14\`. This DOES NOT verify the Lean proof or its arithmetic API typing.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. Everything new remains \`SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED\`; no GREEN evidence.
- \`EXTERNAL_INPUTS.json\` unchanged (Git blob \`8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab\`); (M) only registered, not implemented or axiomatized. No manuscript, production source, toolchain/locks, other automation, excluded full 87-domain, external board, PR or CI changes.

**Exact next entrance:** prove the *actual* all-source off-shift weighted divisor moment, independent b=T coefficient power bound and mean-rho factor bound, then combine them with the existing genuine \`dD/H\` same-rho cutoff. Independently prove physical \`W_T\` all-family \`ContDiff\` and iterated Fréchet integrability with uniform m(N), and choose a single H only after the arithmetic mass has been paid. Causal/whole-box, all HB source words, empty Gamma, high-rank/enhanced and overall PP remain open.

**Status:** P3.6 YELLOW. The new exact arithmetic reduction is BLUE only within its named SOURCE_ONLY scope; neither source closure nor compilation/kernel acceptance is claimed.


## Successor SOURCE_ONLY increment — genuine nonzero-shift divisor support and finite original-rho moment (2026-11-06 UTC)

- **Actual recovered baseline:** `8497fedb53e1df9df9193882ff2e0f562fc9f4c3`, branch `chatgpt/p3-internal-original-w-20261105`; this was the exact current HEAD at this round's first comparison (ahead 0, behind 0). No concurrent branch writer was observed in the branch checks.
- **Genuine new source commit:** `08a7bf16d6df5a549010fec1ceed4d66b3ad0054` with `[skip ci]`, source `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ShiftedDivisorFiniteMoment.lean` (223 text lines), Git blob `3f869e42d2b9c9ea3d15d85db1ed2e00946122c8`.
- **VERIFY commit:** `a7df2ff247eeb3d9952948f6a215366b6231978c`, Git blob `83ae30cddef3985af019ec24e4021f5484cf9df8`; all new imports precede #checks. **Not executed.**
- **REGISTRY commits:** `e9bfbd858266be0cc9dccf10600a29f2fa2b024d`, followed by a precise API-evidence correction `887a87ea53dcf02dd622c8ae7fb25f1b44fc01d1`; REGISTRY Git blob `ea077eeec03895f5d2e5037c32d3d6d9704b6934`. The only external register remains unchanged at Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`.
- **Fixed paper:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4, after formula (F), actual complete-modulus sum and nonzero shift divisor moment. **Mathlib pin:** `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### New actual mathematical step (strictly manuscript-internal)

The predecessor `P3FullModulusShiftedMoment` already separated exact full product `b=T` from the off-product `b≠T`, but its remaining off-modulus congruence was a free sum over all original physical moduli `Q`. This round proves-in-source the following finite arithmetic transformation, with the **same original rho**, **same labelled tuples**, **same complete original product** and a genuinely **nonzero signed integer shift** `T-b`:

```
sum_(q in Q) |rho(q)| * 1_(q divides (T-b))
  = sum_(q in Q intersection divisors(natAbs(T-b))) |rho(q)|
          (b != T).
```

The new `shiftAbs_ne_zero` and `shiftedResidueKernel_eq_divisors` are explicit: `q=0` cannot divide a nonzero shift; `Nat.divisors` therefore gives exactly the actual nonzero shift's natural divisors, without ever applying a divisor function to zero. `off_shifted_eq_restricted_divisor` uses only finite sum commutation and retains the real original coefficients.

The new upper bounds are **two separate valid comparisons**:

```
offShiftedResidueMass
 <= sum_(original off tuples t) |coefficient(t)|
        * sum_(q divides |T-product(t)|) |rho(q)|;
```

and **only if** a separate explicit pointwise `|rho(q)| <= R` holds on the actual `Q`:

```
offShiftedResidueMass
 <= R * sum_(original off tuples t) |coefficient(t)| * tau(|T-product(t)|).
```

The latter does **not** assert that the unrestricted rho-weighted divisor sum is itself bounded by `R*tau`: `R` is known only on `Q`, not outside it. The implementation bounds the *restricted* sum before using the cardinality of the divisor set. This distinction was caught by the independent finite regression: an overstrong comparison was rejected in an initial test formulation, then removed; all final tested identities/inequalities are the ones actually sourced.

Finally `full_mass_le_divisor_moment` composes the new off-shift bound with the unchanged predecessor's exact `b=T` coefficient mass and the exact coprime-mean mass:

```
fullModulusMass <= exactCoefficientMass*exactRhoMass
                  + weighted_nonzero_shift_divisor_moment
                  + offCoefficientMass*meanRhoMass.
```

This is **NOT** a claimed `O(T log^E T)` or `O(T/log^A T)` result. The actual HB coefficient majorant, near-linear mixed shifted moment, actual original rho bound, and independently the `b=T` exceptional source coefficient power saving all remain **UNPROVED**. Nor is uniform original `W_T` smoothness, the common `H` choice or PP assembly paid. No relative-to-fibre Theta requirement was added.

### Executed checks, explicit nonverification and next entry

- Actual remote reads: exact branch HEAD and predecessor REPORT/REGISTRY/EXTERNAL_INPUTS, `P3FullModulusShiftedMoment.lean`, prior Fourier inversion, pinned manuscript §§1–4 and fixed `Mathlib/NumberTheory/Divisors.lean` declaring `Nat.mem_divisors : q∈n.divisors ↔ q∣n ∧ n≠0`. Root/docs/source-only/packet AGENTS paths returned NOT_FOUND. The exact pinned `Int.natAbs_dvd_natAbs` location was **not** independently identified; its use is a source candidate and an elaboration risk.
- New file GitHub readback: exact 223-line content, SHA `3f869e42d2b9c9ea3d15d85db1ed2e00946122c8`. Static escaped-proof-token scan **0**; stripped-comment bracket/brace/parenthesis stack **PASS**. `VERIFY.lean` readback matched and imports precede check commands.
- Deterministic JS **1,000/1,000** finite exact-integer regressions, across original product group lengths 0–4, targets {1,2,5,12,31}, signed rho and signed coefficient samples, including `q=0`. Checked exact off-ramification support, restricted ≤ unrestricted rho-weighted divisor sum, and independently restricted ≤ pointwise-`R` times `tau`. No attempt to interpret these finite checks as an asymptotic theorem or Lean verification.
- **NOT RUN:** Lean, Lake, CI, kernel replay, complete axiom audit, Codex or heavy numerical producer. The 10 new names are SOURCE_ONLY candidate declarations and no part of this packet is certified green. No new axiom, untrusted computation or external input implementation was added.
- `EXTERNAL_INPUTS.json`: fixed medium estimate (M) remains **RECORD_ONLY_NOT_IMPLEMENTED_NOT_AXIOM** with exact original pin and premises. All new steps above are internal, not reclassified as external.
- Untouched: pinned manuscript, production modules, other tasks, toolchain and lockfiles, excluded actual dynamic parent/full 87-domain node, PRs, external board and CI.

**Next concrete entrance:** obtain genuine original HB all-source coefficient divisor-power bounds, then a near-linear `sum_b tau(b)^R tau(|T-b|)^S` estimate in the fixed complete scales with the strict exponent cap. Discharge the original physical `rho` weights (pointwise or appropriate weighted divisor-class) from the real coefficient compiler—not from a target-shaped premise. Bound the exact `b=T` source term independently and bound the true mean-rho sum. Separately prove uniform `W_T` Fréchet/ContDiff and original mixed-L1 derivative budget for growing `m(N)`; select a common log-power `H` only after these have true quantitative bounds. Complete causal/whole-box, all HB sources, empty Gamma mother words, high rank/enhanced and the original same-rho PP assembly.

**Status:** P3.6 YELLOW; this limited finite divisor bridge is BLUE SOURCE_ONLY, **UNCOMPILED / KERNEL_UNVERIFIED**.


## Successor SOURCE_ONLY increment — one-marked HB actual log and finite divisor-power convolution (2026-11-06 UTC)

- **Verified baseline:** `9d6b65169a5fbfe6569eccd8ef183c188655d4a9` was the actual P3.6 branch HEAD before this iteration. The branch HEAD was rechecked before each write; no observed concurrent writer.
- **New proof source:** `P3HBOrderedFactorMajorant.lean`, 279 lines, read back with Git blob `75ecbbb7924de7ad72f53b9e95bcd170a4fcecf2`. Initial creation commit `f1611c62bb89db2d0763a0726fa5e17c5e1e9973` and literal-Real.log extension `d6eda491aa1e42b875476f9fbaf6a52c73ecdace`; both carry `[skip ci]`.
- **Audit entry:** `VERIFY.lean` updated in `16a988336688ed62f9d5d0dc18a25b54d3deec72` and `ca4fb3e22a41579db264512d45c43006195c2b3f`; 11 new `#check` targets are present, all imports precede checks; **VERIFY WAS NOT EXECUTED**. Final VERIFY Git blob `9717ddfc2ea1da5ea665fbb3a5d57d425be1f232`.
- **Registry commit:** `9838c7475859b79789f2268c210acd7f12a2fb87`; REGISTRY Git blob `1e0df1cfccfe1789e693efaeed6c4e2fc5cbbcaf`. The **only** external registry remains unchanged: `EXTERNAL_INPUTS.json` Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`.
- **Pinned manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, module `paper/source/modules/distribution-prime-product-completion-20261010.txt` §2 (exact HB log slot, one-bounded factors and complete products), §4 (nonzero-shift mixed divisor moment after the *complete* physical modulus sum); `paper/source/manuscript-body.tex` prime-products subsection. **Fixed Mathlib:** `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### Genuine internal mathematical step

The predecessor converted **actual off-product signed-rho congruence mass** to a nonzero integer-shift divisor moment, but did not yet pay even the **primitive HB convolution coefficient power**. This iteration supplies a direct elementary finite counting and real-log argument (candidate Lean proof bodies), without postulating a mixed moment theorem.

For `n≠0` the new `orderedFactorTuples g n` enumerates **every distinct ordered g-tuple of natural numbers** whose complete product is `n`. Each coordinate divides `n`, so its finite divisor-box inclusion is an equality. The actual card is bounded from the fixed-library finite function product cardinality by

```
  #orderedFactorTuples(g,n) <= tau(n)^g.
```

This conservatively uses exponent `g`, **not** a purported unproved `g-1` improvement.

Take arbitrary literal **one-bounded** slot factors `|a_j(u)|≤1` and **one specifically marked HB log slot**. The new source first bounds the corresponding ordered convolution by `L*tau(n)^g` under a fibre-only log bound; then importantly removes any impossible **global** uniform log hypothesis when the log slot is the *actual* `Real.log(u)`. On `n≠0`, the marked coordinate is a positive divisor of the complete product, so `0≤log(u)≤log(n)`; hence the candidate theorem establishes

```
 sum_(ordered p: prod_j p_j=n) |log(p_marked)*prod_j a_j(p_j)|
    <= log(n)*tau(n)^g.
```

This has the **original ordered HB variable count and exactly one log**, without replacing the complete product by auxiliary variables or erasing zero-dimensional support. For a finite set of actual nonzero, nonexceptional complete products satisfying `log(n)≤L`, a final new candidate yields

```
 sum_(n in ns, n!=0, n!=T) HBMarkedMass(n)*tau(|T-n|)
   <= L * sum_(n in ns, n!=0, n!=T) tau(n)^g*tau(|T-n|).
```

Thus **the elementary factor-counting and one-log payment** are now explicit. The actual mixed divisor moment on the right is **NOT** bounded by this file: the near-linear bound at the retained strict `kappa` cap remains genuinely internal. No `tau(0)` term enters the sum. The source enumerates DISTINCT ordered integer tuples; the actual original **labelled** HB source has additional combinatorial labels, factorial normalizations, per-chart rough filters and scalar restoration. Those are not presumed already attached, and neither the actual global bound for the original `rho`, exact `b=T` payment nor the precise HB coefficient compiler is claimed here.

### Evidence and limits

- Direct GitHub reads this iteration: exact branch HEAD, predecessor REPORT/REGISTRY/EXTERNAL_INPUTS and true preceding `P3ShiftedDivisorFiniteMoment.lean` and `P3FullModulusShiftedMoment.lean`; fixed manuscript §§1–4 and manuscript-body.tex. The repository root `AGENTS.md` returned NOT_FOUND, consistent with the earlier reported packet checks; no hidden constraints were invented.
- Fixed library source examined: `Nat.mem_divisors`, `Fintype.mem_piFinset`, `Fintype.card_piFinset_const`, `Finset.prod_le_prod`, `Finset.abs_prod`, `Real.log_le_log`, `Real.log_nonneg` and `Real.log_natCast_nonneg`. The candidate `Finset.dvd_prod_of_mem` use is known from fixed-library source usage but the exact elaborated application has **not** been tested. **No Lean typecheck was performed.**
- Readback and source static audit: 0 forbidden proof-escape tokens outside comments; lexical delimiter matching PASS; all 11 new `#check` names located and imports remain before checks.
- Independent deterministic finite arithmetic regression: **2,360/2,360** cases for ordered g=1..4, n=1..48, one marked genuine `log(u)`, bounded trigonometric slot factors and several nonzero shifts. All satisfied the stated finite coefficient/divisor inequalities; 40 exact `n=T` instances were explicitly excluded. This is a numeric and finite sanity check, **not** an asymptotic proof nor Lean/kernel acceptance.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. No new axioms, sorry, admit, target-equivalent assumption, new analytic input implementation, or green nodes.
- No write to the fixed manuscript, production proof, toolchain/lockfile, other task branches, PRs, excluded full87 dynamic-parent node, external dashboard, or CI.

### Next actual mathematical entrance

Connect the **actual original labelled HB coefficient compiler** to this distinct ordered integer-factor fibre: pay its label multiplicities, dyadic rectangles, the single original marked log slot, original rough conditions and finite scalar restoration without conflating unit log with an empty Gamma mother word. Use the fixed complete-product scale to supply the local `log(n)≤L` uniformly in increasing `m(N)`. Only then reduce the actual full source to the **near-linear mixed shifted moment** with the stated strict exponent cap and complete-product `b=T` excluded. Separately discharge the original same-rho weighted modulus and exact coprime mean mass, `b=T` exceptional coefficient power bound, physical `W_T` Fréchet/ContDiff admission, causal/whole-box licence, full HB family, empty Gamma mother payment and high rank/enhanced branches. Do not reclassify any of these as external.

**Status:** P3.6 YELLOW; this narrowly named HB finite coefficient source is BLUE **SOURCE_ONLY**, UNCOMPILED/KERNEL_UNVERIFIED. The registered classical estimate (M) remains **RECORD_ONLY_NOT_IMPLEMENTED_NOT_AXIOM**.


## Successor SOURCE_ONLY increment — literal order-three HB word mass (2026-11-06 UTC)

- **Actual recovered branch HEAD:** `392903b689be738bdd43bdc59a964bb6bbccadfb`, same task branch `chatgpt/p3-internal-original-w-20261105`; no concurrent writer observed before the leased ref update. This round extends, rather than replaces, the prior `P3HBOrderedFactorMajorant` source and verified its saved report, registry and external register.
- **Actual source+VERIFY commit:** `c90b2edebcfbd872e0e7d60cb3d69df3689243d4` (`[skip ci]`), confirmed GitHub branch ref update and independent source readback. New `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3HBLiteralWordMajorant.lean` Git blob `22c38377e453bd6c82684c457c70088baa4a5320` (194 lines); `VERIFY.lean` Git blob `701fbfb85793e5bf13681078997fb522346e2d85`. The ten named definitions and proof candidates are registered as audit targets, **not executed**.
- **Fixed manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, §2 exact order-three `(HB)` and §4 post-(F) moment. **Fixed Mathlib:** `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Reused actual `ImbalancedChen/P5LiteralHeathBrownOccurrenceWords.lean`, not a fabricated word source. Pinned Möbius source `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean` was read for `moebius_eq_or`.

### Genuine mathematical increment and precise limitation

The prior `P3HBOrderedFactorMajorant` allowed arbitrary one-bounded factor functions and one marked logarithm, but did **not** yet connect an actual HB word. Here `hbPrefix` is literally `muTrunc(y)` repeated `j+1` times then the true zeta one-slot repeated `j` times, for `j=0,1,2`; the word ends in exactly one `ArithmeticFunction.log`. The source derives, rather than presupposes, that the truncated Möbius values and zeta slots have absolute value at most one, using the original real cutoff and `moebius_eq_or`.

An inductive `bounded_prefix_log_product` shows that for **positive complete product** `n`, every original ordered HB tuple `ps` has
`|tupleWeight(hbWord(y,j),ps)| <= log(n)`.
Consequently the true literal HB coefficient's absolute ordered-fibre mass satisfies
`literalHBAbsMass(y,j,n) <= log(n) * card(factorTuples(2*(j+1),n))`.
The final three-term mass keeps the original absolute `binom(3,j+1)` weights, exactly `3,3,1`, rather than resetting the scalar or assuming a future PP bound.

This is a real original-HB-source connection. **It is not a labelled-prime compiler or near-linear shifted-moment payment.** In particular the List-based `factorTuples` cardinal has **not** yet been transported to the earlier `Fin`-indexed `tau(n)^g` bound; full original labels, per-label factorials, rough filters, exact b=T exception, source multiplicities and uniform m(N) remain open. The unit log slot contributes zero when its argument is one, but this is not an empty Gamma mother word.

### Checks and next exact entrance

- Source blob and VERIFY blob were read back with exact matching Git SHAs; ten named check targets present and import precedes first `#check`. Forbidden proof escapes 0; the complete source lexical bracket scan passed. Pinned Mathlib Möbius definition and values were directly inspected.
- Independent Python exact integer-factor recursion/real-log test: **61,960 checks**, four real cutoff values and nonzero n through 90, all three actual HB lengths; **zero failures**; maximum observed ratio of true three-term absolute mass to stated cardinal-log upper bound was 0.2916666666666667. This tests only finite arithmetic, not Lean typing or the kernel.
- **NOT RUN by instruction:** Lean, Lake, CI, kernel replay, full axiom audit, Codex, heavy numerical producers. This source is **SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED**; no green status earned. Other historical candidate sources remain uncompiled.
- `EXTERNAL_INPUTS.json` unchanged at Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; external (M) is **record only**, neither implemented nor promoted to an axiom. No production files, manuscript, toolchain, PR, other task, externally excluded 87-domain node or board touched.

**Next precise work:** prove List-to-Fin ordered HB factor-tuple cardinal transport retaining repeated occurrence count, apply the real `tau(n)^{2(j+1)}` bound to the true `3,3,1` source; then map the actual interval labels, original factorial normalization, rough projectors and full product into the same physical rho. Independently pay the fixed-order near-linear mixed shift moment, b=T exception, original rho mean and W_T uniform analytic admission before a common H and PP assembly. **Overall P3.6 remains YELLOW.**

## Successor SOURCE_ONLY increment — literal HB List-to-Fin positional cardinal bridge (2026-11-06 UTC)

- **Actual predecessor branch HEAD:** `c1b34c471154dbce31da8de333f226b9540a47b4` on `chatgpt/p3-internal-original-w-20261105`. GitHub head was read before writing and checked again immediately before the initial file creation. No same-branch concurrent writer was observed at the checked points.
- **New genuine Lean candidate file:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3HBLiteralFiniteBridge.lean` (168 lines), Git blob `b603da50b9a2b00dbb86eea86d0ad8f8ba321f1a`; committed as `f2ba54af1cdbaee8788219fa3a8c664e1177288c` with `[skip ci]`.
- **Audit source:** `VERIFY.lean`, Git blob `d6fc97c85c02f525e2d34f0b623de4dc23533057`, six additional `#check` targets, commit `970de1b57d293df8a467c5014bb5d39740256932` with `[skip ci]`.
- **Registry update:** `REGISTRY.json`, Git blob `e7f62d44c77492bf66fa0513ffd06f23476b7036`, commit `75cbe5276d887c117304891b9c07b8277cfc4c86` with `[skip ci]`. **Only** the present P3.6 task files were written.
- **Pinned manuscript remains** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`: `paper/source/modules/distribution-prime-product-completion-20261010.txt` §2 actual order-three HB and §4 post-Fourier arithmetic moment; `paper/source/manuscript-body.tex` original-prime-product subsection. Pinned Mathlib remains `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- `EXTERNAL_INPUTS.json` unchanged, exact Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. Classical restricted signed medium estimate (M) remains **RECORD_ONLY_NOT_IMPLEMENTED_NOT_AXIOM**. No substitute axioms or target-equivalent structures were added.

### Real mathematical advance, with quantifiers and scope

The predecessor genuinely used the exact `P5LiteralHeathBrownOccurrenceWords` original order-three words (with `muTrunc`, original zeta unit slots, one logarithm, and absolute scalar magnitudes `3,3,1`), but its `factorTuples(g,n) : Finset (List ℕ)` coefficient bound stopped at an unquantified List cardinality. This iteration connects the exact literal List fibre to the **already existing** `P3HBOrderedFactorMajorant.orderedFactorTuples(g,n) : Finset (Fin g → ℕ)`.

For every `n != 0`, `factorTuples_spec` supplies each List's exact length `g` and positive **complete** product `n`. The positional map `ps.get : Fin ps.length → ℕ`, with `List.ofFn_get` and pinned `Fin.prod_ofFn`, is shown to belong to the genuine previous `orderedFactorTuples` by its *existing* `mem_orderedFactorTuples_iff` (not by a new cycle or manufactured membership certificate). Hence

```
  card(factorTuples(g,n))
    <= card(orderedFactorTuples(g,n))
    <= tau(n)^g.
```

This is positional: equal *values* at different original slots are still separate occurrences and ordered tuples are not replaced by unordered multisets. It also does not equate a unit log slot to an empty Gamma mother word.

The next two theorems feed that bound into the **actual** order-three HB primitive words, proving source-only candidates

```
  literalHBAbsMass(y,j,n) <= log(n) * tau(n)^(2*(j+1)),
  sum_(j=0..2) binom(3,j+1)*literalHBAbsMass(y,j,n)
     <= log(n)*sum_(j=0..2) binom(3,j+1)*tau(n)^(2*(j+1)).
```

Thus the ORIGINAL absolute signs and the genuinely fixed orders `2,4,6` are retained; the coefficient magnitudes remain exactly `3,3,1`. On a finite admitted family of **nonzero n != T** with `log(n)<=L`, the sixth candidate proves the corresponding upper bound of its **actual** finite shifted `tau(|T-n|)` moment by `L` times the displayed fixed-order mixed moment. The RHS is *not* shown to be near-linear; there is no bound on the full arithmetic modulus mass and no `tau(0)` term.

The step is properly upstream of restoring original prime labels, factorial normalizations, rough projectors, dyadic rectangles, high-rank/enhanced branches and complete product scales. It cannot be treated as the entire original labelled PP source nor as a full same-integer-`rho` PP theorem.

### Evidence, limitations, handoff

- Direct read before write: task branch HEAD, current REPORT/REGISTRY/EXTERNAL_INPUTS, actual old List and Fin factor proofs, actual `ImbalancedChen/P5LiteralHeathBrownOccurrenceWords.lean`, pinned manuscript module §2 and §4 and `manuscript-body.tex`. Root/docs/source-only/present packet `AGENTS.md` checked and returned NOT_FOUND.
- Fixed Mathlib source (exact pinned commit) directly inspected for `List.ofFn_get` (`Mathlib/Data/List/OfFn.lean`) and `Fin.prod_ofFn` (`Mathlib/Algebra/BigOperators/Fin.lean`). Source inspection is NOT a Lean elaboration check. The previous `orderedFactorTuples_card_le_tau_pow` remains uncompiled, so the new proof depends on an UNVERIFIED predecessor.
- New source GitHub readback matched `b603da50b9a2b00dbb86eea86d0ad8f8ba321f1a`; six `VERIFY` checks were included after imports. Static token scan of new Lean proof (comments excluded): 0 banned escape tokens; lexical delimiter scan PASS.
- Independent Python finite exact positional-factor tests: **640/640**, `g=0..6`, `n=1..80`, checking distinct ordered factor occurrences, product identity and the `tau(n)^g` cardinal bound. Additional original literal HB and shifted-moment tests: **756/756**, real cutoffs `y=3,6,10,15`, `n=1..48`, target `T=5,19,37`, with **12 exact `n=T` exceptions excluded**. The observed largest original HB mass / divisor-power bound ratio was about `0.05645`; zero finite failures. These tests certify neither Lean typing nor the infinite/asymptotic number-theory estimate.
- **NOT RUN by explicit scope:** Lean/Lake, CI, kernel replay, dependent theorem elaboration, complete transitive axiom audit, Codex, heavy producers. Thus all six new declarations remain `SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED`; no node becomes green.
- No writes to production code, manuscript, dependency lock, other branches/tasks, PRs, external board, excluded actual full-87 dynamic-parent/current-history node or CI.

**Next exact internal entrance:** restore original prime-label multiplicities and their factorial normalizations and the true rough projectors to the now positional HB integer fibres. Preserve the physical complete products and mean with the same integer rho, then prove the still-unpaid near-linear mixed shifted divisor moment under the original strict kappa cap. Independently pay `b=T`, the original weighted rho/totient mean, uniform smooth `W_T` family with increasing `m(N)`, causal/whole-box, all HB words, empty Gamma mothers, high-rank and enhanced branches. No new external input may stand in for these obligations.

**Status:** P3.6 YELLOW. This explicitly limited List-to-Fin, genuine `3,3,1` HB coefficient divisor-power and nonzero-shift reduction is BLUE *source-only*, UNCOMPILED / KERNEL_UNVERIFIED. External (M) is merely registered.


## Successor SOURCE_ONLY increment — exact strict rough-mask transfer of original HB coefficient mass (2026-11-06 UTC)

- **Actual recovered baseline:** `85c1a887485d4e87a5166b5a5233e54c9214e365`, branch `chatgpt/p3-internal-original-w-20261105`. The branch and its predecessor REPORT, REGISTRY, EXTERNAL_INPUTS and actual List-to-Fin/HB proof files were read, along with the real rough-HB word and strict rough-slot source.
- **New pushed proof commit:** `da397e44cf5625714694efefd64ea82a51fa6d53` (`[skip ci]`). New proof: `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3HBRoughLiteralMoment.lean`, 177 source lines, Git blob `00be23db72d86c9fc476e9ebf9dc004d881b6a5e`; ten named definitions/theorem candidates. Fixed manuscript `9731290e8f53cffda44129906cde6a965eaa869b`, completion module §2 exact rough HB and §4 (F), unchanged. Fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- **Mathematical step:** Reuse *actual* `P5ActualRoughHeathBrownWords.actual_word_mask`, not a new artificial rough predicate. Every ordered HB tuple in `factorTuples(2*(j+1),n)` has the *same complete integer product n*, so its complex rough weight is the literal real HB weight multiplied by `roughOneSlot(z,n)`. Taking complex norms and summing gives the exact source-only candidate identity
  `roughLiteralHBAbsMass(z,y,j,n) = norm(roughOneSlot(z,n))*literalHBAbsMass(y,j,n)`
  for z>=0, including units and repeated occurrences. The same identity holds for the original absolute 3,3,1 three-term mass. Under the genuine strict coprimality dictionary the mass vanishes on any n divisible by a prime p<=z (including the endpoint p=z).
- **Nontrivial quantitative transfer:** the existing *literal* fixed exponent 2,4,6 bounds yield
  `roughThreeTermMass(z,y,n) <= log(n)*sum_(j=0..2) choose(3,j+1)*tau(n)^(2(j+1))`
  for n!=0. On the real admitted finite domain n!=0,T and log(n)<=L, the complete-product shifted tau moment is controlled by L times the **same still-unestimated** fixed-order mixed divisor moment. No tau(0) is evaluated; no claim of a near-linear shifted asymptotic or complete arithmetic discrepancy payment is made.
- **Direct source/API inspections:** read `ImbalancedChen/P5ActualRoughHeathBrownWords.lean` and `ImbalancedChen/Part3RoughSlotCharacterLift.lean` exact strict mask and its norm bound; checked fixed Mathlib source for `norm_real` in `Mathlib/Analysis/Complex/Basic.lean`. These are source inspections, not elaboration.
- **Finite independent regression:** 8,160 exact mask/absolute-fibre numerical checks and 724 disallowed-product zero checks over z={0,2,3,5,7}, y={2,3,5,11}, n=1..68 and j=0,1,2, all passed. The finite test is not Lean verification or a proof of an asymptotic estimate. Static banned-token count 0 and lexical delimiter scan balanced.
- **Validation omitted by instruction:** Lean/Lake, CI, kernel replay, full dependency/axiom audit, Codex and heavy producers were not run. The existing `VERIFY.lean` targets are audit targets only. **Important staging limitation:** the P3 SOURCE_ONLY files currently live under `docs/source-only`; their `ImbalancedChen.P3*` import paths are not present as installed `ImbalancedChen/` Lean modules in the Git tree, so a future independent import-staging step will be needed for an actual Lean run. This run did not alter production or toolchain to mask that gap. **No green nodes.**
- **External boundary:** `EXTERNAL_INPUTS.json` unchanged at blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; research (M) remains registered only, not implemented or axiomatized.
- **Still open:** original prime labels, repeated-label factorials, dyadic/rough source tensor matching, the real b=T exception, near-linear shifted mixed moment under strict kappa, same rho modulus and exact mean, uniform W_T admission, common H, causal/whole-box, HB full source, empty Gamma mothers, high-rank/enhanced and final PP assembly. The excluded full-87 dynamic-parent task remains untouched.

**Status:** P3.6 YELLOW. The exact rough-mask transfer for the literal HB coefficient is BLUE within this explicit SOURCE_ONLY scope; uncompiled, unverified by kernel. No other branches, manuscript, PR, dashboard, CI or production files were changed.


## Successor SOURCE_ONLY increment — original fine-prime-label three-gamma tensor (2026-11-06)

- **Checked baseline HEAD:** `07bedd44f34919f7ebc65313bb1be2b7efbcebe6`, branch `chatgpt/p3-internal-original-w-20261105`. This followed the actual rough HB literal moment packet; the old de582e6 was NOT replayed.
- **New proof-body commit:** `c26fded296795219aeda082b180f6aa274e1e15b`, message contains `[skip ci]`.
- **New proof source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualFineLabelThreeGammaTensor.lean`, 180 textual lines, Git blob `af0d123ff793b3c1e857f4149ddc99f8bca63f04`.
- **Audit import/check commit:** `c0235ac5dc41c5c7a81f20d48124168185f70013`; `VERIFY.lean` Git blob `866ea2f3355177cbaa7cab7d4dbd4c7958480944`. Registry update commit `e992226e6a29487ae14b3cc0d9951ea47b99b106`.
- **Pins held:** manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §3 (T) and §4 (F); pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### Genuine internal mathematical increment

This packet targets the **actual prime-label side** of the PP tensor, rather than double-counting prime labels and HB factors as independent original primes. It uses the real `actualPrimeSlotBox`, `actualPrimeLabelBlocksWord`, original `actualPrimeLabelBlocksFactorial`, and the previously implemented `P5ActualNormalizedPrimeLabelCoefficient.gamma`.

For three already-fixed original group block lists `g₁,g₂,g₃`, write `M_j = ∏_I m_(I,j)!` and let `M_all` be the original full-label factorial. If and only if the concrete original labelled slot word is a positional permutation of the concatenated three group words, the new `actual_label_three_gamma_tensor` candidate expresses the ORIGINAL signed raw full-prime-vector sum as the true three gamma convolution with scalar

```
  c * (M₁ * M₂ * M₃ / M_all)
```

where `c` remains the same signed source scalar, each group gamma is its **original** repeated-label normalized complete-product coefficient, and every product-value fibre is retained. The identity is algebraic even when label prime sets overlap; it does **not** identify source fibres with a whole box, assert a new relative coefficient bound or silently insert a total-slot factorial.

The additional `fine_gamma_mem_Icc` and `fine_three_gamma_product_abs_le_one` candidates instantiate the original *actual disjoint half-open fine intervals* `actualPrimeFineLabelFinset N τ` (not an arbitrary invented box) and the proved `gamma_mem_Icc`. The necessary hypotheses are `N≥1`, `τ≥0` and **distinct label indices within each group**; no one-bounded coefficient is taken as a premise. A product of three gamma values is at most one, but the **sum over full-product collisions is NOT thereby one-bounded**. The latter must be handled by the original family/compiler.

This is separate from the previous literal 3,3,1 rough HB source on the *prime* side. The exact same-integer `rho` modulus family, its group partition dictionary and physical levels have **not** yet been identified with these abstract but original-type tensors. No full PP or arithmetic error is claimed.

### Checks, nonchecks and source risks

- Directly read the current predecessor rough HB proof source, prior `REPORT.md`, `REGISTRY.json`, `EXTERNAL_INPUTS.json`, prior literal List/Fin bridge, actual source `ActualFrozenSlotCoefficientRegrouping.lean` including its precise `actualPrimeTuple_sum_by_product` and `actualPrimeSlotBox_product_sum_append`, `ActualPrimeMultiLabelNormalization.lean`, `ActualPrimeDisjointLabelProducts.lean`, `P5ActualNormalizedPrimeLabelCoefficient.lean`, and fixed manuscript §3 (T).
- The new source read back with the exact Git blob above; static source forbidden-escape scan returned **0**, lexical parenthesis/bracket balance **PASS**. Four `#check` names were placed after imports and are not executed.
- Independent Python finite regression: **1,467 / 1,467** actual integer product-count/factorial cases, including 1,017 with repeated prime labels, using signed scalar c and multiple overlapping prime supports. Max numerical residual `7.11e-15`. This checks finite algebra, NOT Lean elaboration or kernel correctness.
- Remaining source-level elaboration risks: nested `simp_rw [actualPrimeTuple_sum_by_product, Finset.mul_sum]`, exact implicit `List.Perm` rewrite, `field_simp` on four nonzero factorials, and the precise threefold `Finset.mul_sum` normalization. They require eventual controlled Lean typechecking.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy numerical producer. No new green status. Existing SOURCE_ONLY import-location staging constraint remains.
- `EXTERNAL_INPUTS.json` Git blob is still `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; (M) remains **record only, not implemented, not added as an axiom**. No fixed manuscript, production, lockfile, excluded full87 dynamic parent, other task or external board was changed.

### Precise next entrance

1. Discharge the actual fixed whole-box **original labelled slot permutation** into its three group lists in the retained physical source and rank domains, rather than treating the algebraic `hperm` as proved for all original PP families.
2. Restore this true factorial tensor in the actual integer `rho` physical-modulus coefficient compiler, retaining the exact coprime mean, level separation, signed scalar, original labels and multiplicities. Do not add gamma factors to HB words as if they were independent prime slots.
3. Independently establish the strictly scoped mixed nonzero-shift near-linear divisor moment, full product `b=T` payment, `rho` mean-weight bound, actual growing-`m(N)` `W_T` Fourier derivative admission and the common logarithmic H; causal/whole-box, empty Gamma mothers, high-rank and enhanced branches remain internal.
4. The existing excluded complete-87-domain dynamic-parent node is outside this task and was not touched.

**Status:** P3.6 **YELLOW** overall; newly limited finite normalized prime-label tensor **BLUE, SOURCE_ONLY**, not Lean-compiled or kernel-verified.


## P3.6 SOURCE_ONLY successor — actual frozen block-occurrence fine-label partition (2026-11-06)

**Actual recovery and commits.** From verified HEAD 17bb6a05fd924f7b2c3af0706b51d443a1a1f906 on branch chatgpt/p3-internal-original-w-20261105. Read previous REPORT, REGISTRY, EXTERNAL_INPUTS, VERIFY, previous gamma tensor, real frozen selected-pair slot allocator, original factorial/normalized gamma producer and fixed manuscript 9731290e8f53cffda44129906cde6a965eaa869b (§3 (T)). Root and directory AGENTS.md paths returned 404; none was treated as read. Source commit fcb3f661ef44d6970b385ba896351e9d9cfb85eb, VERIFY commit 4db0757bf116b60ca45abe6d9e17a984bbf6ee40 and REGISTRY commit 6f374e81eb55c0d01a1b001019dbd06bb6f203c1; all [skip ci]. The REPORT's own final commit SHA is the GitHub HEAD containing this section (no self-referential SHA written).

**New proof.** File P3ActualFrozenFineLabelPartition.lean, 115 lines, blob 7c235ac43ccf7b54cc18e527f5310374271acad2. Four SOURCE_ONLY candidates: frozen_block_words_perm, frozen_block_group_labels_pairwise, actual_frozen_fine_label_tensor, actual_frozen_gamma_product_abs_le_one. VERIFY blob 95651f1042fd4c166c636179b407ebe23f552a5a and REGISTRY blob 4d94e7dbacd745edfc6293084897b59694d91bc3. External-input JSON remains blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab.

**Derived mathematical scope.** Apply the actual fixed whole-box actualFrozenSelectedPairSlots algorithm to complete prime-label BLOCK occurrences, each consisting of one original (label,multiplicity) pair. Its proved frozen permutation of the three group block lists expands by List.Perm.flatMap to a permutation of EVERY actual repeated-label prime slot. Thus the previous normalized three-gamma tensor's hperm is derived (not supplied by the caller) for this block-preserving source class, with the original full-label factorial M_all, the three correct group factorials M_j, signed c, full integer products and ordered fibres all retained. If distinct labels occur in the original block list, group pairwise distinctness is inherited from its genuine partition; the actual disjoint half-open fine-label theorem then gives three one-bounded gamma factors without a caller one-bound assumption.

**Necessary limitation.** The genuine physical PP source allocator may act on INDIVIDUAL prime occurrences and split a repeated-label block. This packet DOES NOT prove its whole-box partition preserves full blocks or give the occurrence-to-block regrouping dictionary (which may require extra multinomial restoring coefficients). It does not identify all true rho coefficients, their physical levels, the signed coprime mean or complete PP error. Do not treat it as source-wide closure or as (M).

**Checks.** GitHub source blob read back; forbidden proof escape scan 0; delimiter scan PASS. Independently tested 450 finite normalized tensor examples, including original block multiplicities 1–2, 3–6 distinct labels, signed external scalar and arbitrary block partitions; max floating residual 1.7763568394002505e-15. These finite checks do NOT validate the actual frozen capacity decisions, prime-interval arithmetic, Lean typing or asymptotics. List.Perm.flatMap, List.Pairwise.perm and List.pairwise_append were inspected in public library docs only, not verified at exact Mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1. NO Lean, Lake, CI, kernel replay, axiom audit, Codex or heavy producer run, per task. The SOURCE_ONLY import-path staging limitation remains.

**Next.** Resolve actual physical original slot partition to repeated-label block dictionary (including split-block multinomial counts where necessary), connect to SAME integer rho and exact coprime mean. Remain unpaid: shifted mixed moment under strict kappa, full product b=T exception, original rho/totient mean, uniform geometric W_T with growing m(N), common Fourier H, causal/whole-box permission, all HB source coverage, empty Gamma mothers, high-rank/enhanced. External (M) remains register-only, not an axiom or implementation. No production, manuscript, lockfiles, excluded full-87 node, PR, main branch, other task or dashboard touched.

**Status:** P3.6 YELLOW overall; block-preserving frozen fine-label adapter BLUE SOURCE_ONLY, uncompiled and kernel unverified; no new GREEN.


## P3.6 SOURCE_ONLY successor — split repeated fine-label occurrences and multinomial recovery (2026-11-06)

**Actual restored baseline:** `f122193068a02db5b6dce7fc2528a7540ae8de2b` on `chatgpt/p3-internal-original-w-20261105`. Before editing, read the HEAD comparison, this REPORT/REGISTRY/EXTERNAL_INPUTS, previous frozen-block source, the original signed three-gamma tensor, the actual `ActualFrozenSelectedPairSlots` allocator, original per-label factorial source and pinned manuscript `9731290e8f53cffda44129906cde6a965eaa869b` at §3 (T). `AGENTS.md` at root, `docs/source-only` and the packet path returned NOT_FOUND, not treated as accessible instructions. No changes in branch HEAD before this round. Fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` inspected for `Nat.factorial_mul_factorial_dvd_factorial_add` and list permutation/count source.

**New proof and GitHub objects:** `P3ActualSplitLabelMultinomial.lean`, 213 physical source lines (214 if counting the final empty split line); blob `8705232f2eede05e6c797a5fc39c62fe3b996690`, source commit `002357c0bcb914266c69e6dd67725a1d33957c2e`; VERIFY commit `a6de79a175625ee87db75daa8bae883fb4e1a902`, blob `08571f3e38b3e00eb7c6db414f6ac2d8ea5f458f`; REGISTRY commit `944e8a3217c1af348eaf6d00c01f3ad6871fa429`, blob `f5bb7c8620719b24b94682bd4e3d3b0d06bf9569`. All messages include `[skip ci]`. This REPORT's own HEAD is the commit containing this paragraph; no self-referential commit claim is inserted.

**New finite mathematical content:** For each original distinct label block `(i,m_i)` and a genuinely three-way occurrence allocation `m_i=m_(i,0)+m_(i,1)+m_(i,2)`, define each group block list with the **same original label** but its own actual occurrence count. The `split_blocks_word_perm` candidate inductively permutes the original fully repeated slot word into the three group words, using an explicit three-segment permutation instead of an unproved caller hperm. Its proof does not require the original allocator to preserve entire repeated-label blocks; zero-count group blocks contribute a harmless `0! = 1`. For every label, pinned factorial divisibility gives `m_(i,0)! m_(i,1)! m_(i,2)! <= m_i!`, and the induction `split_factorial_le` gives the correct **global** `M_0 M_1 M_2 <= M_all`. Therefore the restoring scalar `M_0 M_1 M_2/M_all` is in `[0,1]` (independent of external signed c).

Using exactly the previous `actual_label_three_gamma_tensor`, `actual_split_three_gamma_tensor` now gives the signed, complete ordered-full-product fibre identity with the ORIGINAL `c/M_all` and group `M_j`, even when one repeated label is split across multiple groups. This is the missing split-block multinomial correction, not a new primitive input. Crucially the theorem assumes only the **finite per-label count equality** for its specified split; it does not supply the arithmetic `rho` nor prove every actual PP source has this split. The additional `frozen_occurrence_count_sum` candidate derives the actual selected-pair algorithm's exact per-label total count conservation from its existing whole-box permutation. It is **not yet** a proof that the chosen physical occurrence partition matches the particular original list of distinct label blocks; a count-to-block dictionary remains necessary. Distinct-label/group one-bounds must still be instantiated on each actual source, not assumed from the multinomial ratio.

**Checks:** GitHub new source blob readback matched the source SHA. Static proof-escape scan returned 0 and delimiter balance PASS; VERIFY has seven additional names after the new import, but was not executed. Independent exact Python tests: **1,544,760 / 1,544,760** factorial three-way splits for up to four label blocks with original multiplicities at most 4; and **1,724 / 1,724** separate finite multi-label, signed integer-product fibre normalization tests with splits, zero counts and repeated labels (max raw collision coefficient 18). These finite tests neither elaborate Lean nor prove source-family correctness/asymptotics. The predecessor gamma tensor and every new theorem remain SOURCE_ONLY and may require syntactic/API repair.

**Deliberately NOT RUN:** Lean, Lake, CI, kernel replay, Codex, full transitive axiom audit, heavy producer. Import staging for SOURCE_ONLY files under docs remains outstanding; no production code, main branch, tools/lockfiles, PRs, manuscript, external board, other task or excluded complete-87-domain dynamic parent was changed. `EXTERNAL_INPUTS.json` stayed blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; external research (M) remains **register only**, with no implementation or new axiom.

**Next exact entrance:** Prove, for the actual physical occurrence frozen allocator, the original *distinct* label-block word count identity and derive every `m_(i,j)` from each computed frozen group (not a tuple-dependent partition); then instantiate `actual_split_three_gamma_tensor` for the true physical source classes, including marked factors and same integer rho with exact coprime mean. Independently pay the nonzero-shift near-linear mixed moment under strict kappa, `b=T`, the rho/totient mean, all growing-`m(N)` original `W_T` derivatives and common `H`, causal/whole-box, all HB, empty Gamma mothers and high-rank/enhanced. No external theorem may replace these internal obligations.

**Status:** P3.6 **YELLOW** overall. The genuine arbitrary **per-label three-way split** factorial inequality and signed original gamma tensor are **BLUE, SOURCE_ONLY/UNCOMPILED/KERNEL_UNVERIFIED** within the explicit finite count-equality domain. No new GREEN.

## P3.6 SOURCE_ONLY successor — actual frozen occurrence label-count dictionary (2026-11-06)

**Confirmed parent HEAD:** `b441b1bd9a2850fc42adf682cbe4307860ea3b12`; **working branch:** `chatgpt/p3-internal-original-w-20261105`. Read the preceding REPORT/REGISTRY/EXTERNAL_INPUTS and candidate tensor/split proofs, actual frozen selected-pair slot permutation, original fine-label coefficient producer and fixed manuscript at `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §3 (T) (and §4 (F) for the remaining separate Fourier task). Checked root, docs, docs/source-only and packet AGENTS.md paths, all NOT_FOUND; no constraints were invented. No concurrent head drift in the check immediately before this record.

**Actual commits and immutable files:** New proof commit `548993251ac9609029f11a6617ffd5fe7f9a1d50` ([skip ci]), `P3ActualFrozenSlotLabelCounts.lean` 203 lines, Git blob `a16144645f211bf7aca0e2e4552ce7e76242e763`. Audit-only `VERIFY.lean` commit `220763c1496874215c765d8b16f4478e7b56f5a1`, blob `092c2ea3e538c25d510d0c96305b1eda77055f4d`, +10 unexecuted #check entries. REGISTRY commit `9fe8d4303bb4555d146c30c3d019efcfc7c8b2b7`, blob `6e42b586a5594c3bcfda950018e4ed09ed03b6e3`. This REPORT's final commit is the HEAD containing this paragraph, deliberately not self-referenced. The single `EXTERNAL_INPUTS.json` remains blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`, unchanged: (M) record only, no research implementation or axiom.

**Genuine new manuscript-internal content:** `blockLabelCount` explicitly counts original labelled block occurrences, even for repeated and zero-size blocks. `expanded_word_count` equates this to the count in the original expanded prime-slot word. `blockLabelCount_zero_of_away` and `blockLabelCount_of_pairwise_mem` show that when the original block labels are distinct, a block `(i,m)` contributes *exactly m* occurrences of label i in the whole original word. `actualFrozenSplitSize` computes the three per-label group counts from the ACTUAL `actualFrozenSelectedPairSlots` output — not a caller-chosen group assignment. `actualFrozenSplitSize_sum` uses the existing frozen permutation and original `frozen_occurrence_count_sum`, not a new conservation axiom. With the explicit equality of the original fully expanded label word to the genuine physical frozen input `p0::p1::p2::tail`, `actual_frozen_slot_split_counts` discharges the previous finite m_i = m_(i,0)+m_(i,1)+m_(i,2) premise, even when repeated label occurrences are split between all three groups. `actual_frozen_slot_split_three_gamma_tensor` and `actual_frozen_slot_factorial_ratio_mem_Icc` then reuse the PREVIOUS signed complete-product tensor and exact original M_all denominators and M_j correction, without inventing new gamma coefficients. All are **candidate theorem proof bodies** and depend on earlier uncompiled modules.

**Scope boundary / essential missing source dictionary:** The equality `hword : actualPrimeLabelBlocksWord blocks = p0::p1::p2::tail` and distinctness of the original block labels remain explicit finite physical-source premises. The former must be *derived for each actual PP atom* from the complete original source compiler; it is not a discrepancy statement and is not yet universally discharged. This round does **not** prove each frozen output group's ordered word is a permutation of the corresponding `splitBlocks` word; one must still connect the actual output to the reconstructed per-label grouped words (and therefore their own gamma factors) before claiming fully physical three-group source identification. In particular the result does NOT reconstruct integer rho, the genuine modulus source coefficient, signed exact coprime mean, high-rank or enhanced sources.

**Checks actually performed:** GitHub readback of source and VERIFY exactly matched registered blobs; 0 forbidden proof-escape tokens and balanced lexical `[ ] ( ) { }` in new source; unexecuted VERIFY contains all 10 new names. Independent Python arithmetic sanity checks used **999** distinct-label/three-group occurrence partitions, **3859** original-block label-count checks and **999** exact integer factorial-ratio inequalities, zero failures. They check a general occurrence-partition model, NOT the actual endpoint capacity decision of the frozen allocator, Mathlib typechecking or a distribution theorem. List-count API was checked in public Mathlib documentation, but not elaborated at the exact pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; source-level `simp`, `rw`, and pairwise uses retain typecheck risk. No Lean, Lake, CI, kernel replay, transitive axioms, Codex, or heavy producer were executed, as requested. SOURCE_ONLY import path staging remains open.

**Precise next dependency:** Derive the actual original block-to-slot input equality from the physical PP source, and prove groupwise permutation between the ACTUAL `actualFrozenSelectedPairSlots` output label words and reconstructed `splitBlocks` words; then insert the *same integer rho* coefficient and exact coprime mean. Independently still unpaid: near-linear shifted tau moment under strict kappa, b=T full-product exception, rho/totient mass, uniform growing-m(N) W_T Fourier derivative class and common H, causal/whole-box licenses, all HB families, empty Gamma mother-word identification/payment, and high-rank/enhanced alternatives. Full-87 dynamic-parent excluded node, manuscript, production files, master, lockfiles, other tasks, PRs and external board were untouched.

**Status:** P3.6 YELLOW. New exact-count/frozen-split finite source scope BLUE (SOURCE_ONLY, uncompiled, kernel unverified). No new GREEN. External (M) registered only.

## P3.6 SOURCE_ONLY successor — actual frozen group words versus reconstructed label splits (2026-11-06)

**Restored verified branch HEAD:** `0e13187f55cd6a78e7b4257e017576042c4bcad5`; branch `chatgpt/p3-internal-original-w-20261105`. The source commit is `352ce496ec864d0aed9836912cb2eb5ce9a6660d` (`[skip ci]`), 178 physical lines, Git blob `00d96b1115143c1d524c78f5cd7e0aef5ddfeed9`, path `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualFrozenGroupWords.lean`. This section is appended to the task's *existing single* REPORT; the HEAD of the subsequent documentation commit is intentionally not self-referenced.

**Exact manuscript and dependency pins:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §3 (T) and §4 (F), `paper/source/manuscript-body.tex`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Read previous REPORT, REGISTRY, EXTERNAL_INPUTS, the latest proof, preceding split/count and three-gamma sources, `ImbalancedChen/ActualFrozenSelectedPairSlots.lean`, the pinned Mathlib list permutation source and the manuscript. Root, docs, docs/source-only and packet AGENTS.md all returned NOT_FOUND; nothing hidden was inferred.

**New finite proof work, not duplicated interface packaging.** The previous packet had only aggregate conservation `m_i = sum_j m_(i,j)`, which could not identify the *specific three actual frozen output words* with the group words used by the normalized gamma tensor. `splitBlocks_pairwise` shows the actual original pairwise distinct-label dictionary stays distinct after assigning real group multiplicities; `split_word_count_of_member` and `split_word_count_of_absent` give exact count control for ALL labels, including labels not present and zero-count groups. `actual_frozen_split_word_count` computes those counts from the **real** `actualFrozenSelectedPairSlots` output, using the inherited exact whole-box permutation and the original expanded-word equality. It proves equality separately at each group, not just equality of total source length. `actual_frozen_group_words_perm` then invokes the pinned `List.perm_iff_count` to produce all three actual-group/split-group word permutations, including repeated labels split between groups. No tuple-dependent allocation or deduplication is used. `actual_frozen_physical_three_product_sum` independently applies the existing exact prime-slot-box product-sum permutation and append identities to preserve the COMPLETE physical integer product through the genuine frozen groups, for arbitrary real test function H.

**Essential hypotheses and limits:** The original block labels are pairwise distinct, and `hword : actualPrimeLabelBlocksWord blocks = p0::p1::p2::tail` is still a SOURCE DICTIONARY premise. Its derivation for every original physical PP atom is NOT done. The output-word permutations only transfer product-fibre sums; fully identifying actual group `gamma` coefficients and original restoring factorials with the physical coefficient compiler, attaching the SAME integer rho and EXACT coprime mean, marked/rough/empty-Gamma sources, and paying all distribution errors remain internal tasks. The physical Fubini/Fourier budget and all scale endpoints must still be paid. No target-shaped PP premise, external research axiom or arbitrary fibrewise relative estimate is introduced.

**Checks executed:** GitHub branch HEAD checked before source write and source read back with blob `00d96b1115143c1d524c78f5cd7e0aef5ddfeed9`. Static forbidden proof escape-token scan 0; delimiter stack balanced. An independent finite JS count/permutation regression tested 1,400 original repeated-label words with fixed three-group allocations: 4,200 groupwise exact sorted-multiset comparisons and 2,800 absent-label controls (7,000/7,000 assertions, zero failures). These checks model arbitrary valid occurrence partitions, NOT the endpoint decision rules or Lean elaboration. The relevant pinned `Mathlib/Data/List/Perm/Basic.lean` uses `perm_iff_count`; this is API-source inspection, not Lean typechecking. Unexecuted VERIFY entries added before other checks; blob `dd3eb47785e556bb604ae0d1156a9e1000e7ff92`.

**Deliberately NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy numerical producer. SOURCE_ONLY module staging and proof elaboration (especially List.mem_map, pairwise, Fin 3 cases and product-box rewrites) are UNVERIFIED. This must not be promoted GREEN. `EXTERNAL_INPUTS.json` remains identical, blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`, (M) RECORD ONLY / NOT IMPLEMENTED / NOT AXIOM. No changes to manuscript, production, toolchain, excluded full87 dynamic parent, other branches, PR, main, board or CI.

**Next precise entrance:** Derive `hword` from the ACTUAL physical fine-label PP compiler rather than passing it as a source premise. Then identify normalized group gamma coefficients under the newly proved-in-source groupwise permutations with unchanged factorials, original signed marked multiplicities and SAME integer rho/coprime mean. Still unpaid: nonzero-shift near-linear mixed divisor moment under strict κ; complete product exactly T; actual rho/totient mass; fully uniform growing-m(T) geometric W_T derivatives, normalized Fourier L1 and common H; causal/whole-box, complete HB alternatives, empty Gamma mothers, high rank/enhanced. Overall P3.6 YELLOW; the listed finite word and raw-product candidate scope BLUE/UNCOMPILED/KERNEL_UNVERIFIED; no new GREEN.


## P3.6 SOURCE_ONLY successor — original frozen physical three-gamma fibre accounting (2026-11-06)

**Verified start:** `afb9440fc640582f5a640196f0ec0d3c635a70d9`, branch `chatgpt/p3-internal-original-w-20261105`. Checked and read the unique prior REPORT, REGISTRY and EXTERNAL_INPUTS, the actual last `P3ActualFrozenGroupWords.lean`, its literal split-label/count/tensor predecessors, original `ImbalancedChen/ActualFrozenSelectedPairSlots.lean`, `ActualFrozenSlotCoefficientRegrouping.lean`, `P5ActualNormalizedPrimeLabelCoefficient.lean`, the fixed manuscript and its complete-product module. Root and packet AGENTS.md queries were NOT_FOUND. The previous commit was the verified branch HEAD before source creation; no other concurrent writer was observed at those checks.

**Proof-body commit:** `d5f3cc114d3c711c4d15653db5a9b3618bd88004` ([skip ci]), path `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualFrozenPhysicalGamma.lean`, 137 physical lines, exact source Git blob `3e98ff86b4d297145eda22f5e6fb3419076e7e7f`. The separate VERIFY registration commit is `a9390865ea2baff822f2e98b5c5f715daed6443a`, blob `6f01662b92df8e3886a1d427b8ba85ac7c6a72fc`. The separate registry commit is `628898b0d315d63a89d23098266746efc7505c6e`, blob `8741f5aae5af08281f2b1b8cd38206a146f6dcd2`. This last handoff commit itself is not self-referenced; exact final HEAD must be read back after this file write.

**Actual mathematical increment, source candidate only:** the previous result gave exact physical frozen group-word permutations, but did **not** connect the actual groups' normalized weighted integer-fibre sums to the existing normalized `gamma` coefficients. The new `normalized_group_sum_of_word_perm` uses the original `actualPrimeSlotBox_product_sum_perm` plus `actualPrimeTuple_sum_by_product` to prove that, for every test function H and any position-preserving word permutation, the **literal** group sum divided by its **own original per-label factorial** equals the finite product-image `gamma`-weighted sum. No different `gamma` or one-bound hypothesis is introduced.

The new `actual_frozen_three_group_normalized_sums` applies this independently to **all three ACTUAL endpoint-frozen output words**, including groups that receive zero occurrences and repeated labels split across groups. It uses the earlier per-label reconstructed `splitBlocks` words and the real algorithm's groupwise permutations; its hypotheses are the original distinct-label block dictionary and the still-undischarged equality of the original expanded word with the frozen input `p 0 :: p 1 :: p 2 :: tail`. The actual ordered product fibres are **not** deduplicated.

The third result `actual_frozen_physical_three_gamma_tensor` combines the previous raw physical three-box product identity and the original signed three-`gamma` tensor. The left hand side now uses the **real frozen physical groups**, while the right retains the **original signed c**, the original `M_all` and exact `(M_0 M_1 M_2)/M_all`, and the full integer products with all collisions. It works for arbitrary real tests H **on the explicitly stated finite source-dictionary domain**. It is not a relative sparse-fibre estimate, arithmetic error bound, physical modulus identification or unconditional PP proof.

**Exact versions:** fixed manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §3 (T), §4 (F), and `paper/source/manuscript-body.tex`; Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged. All other source-family obligations stay on this fixed target; no auto-follow of master.

**Checks actually executed:** GitHub source readback yielded exactly the recorded blob; new source forbidden proof escape tokens 0 and lexical delimiter balance PASS; VERIFY imports precede its three newly added but UNEXECUTED `#check` entries. Independent exact-integer finite regression: 1,947 source cases, 9,735 assertions, zero failures; 1,255 cases split a repeated label between groups, 1,235 contain an empty group and 1,489 include equal complete-product fibres with multiplicity. Tests compare the full original and three-group finite product-sum, groupwise product histograms and factorial inequalities using integer arithmetic and cross-multiplied normalization. They intentionally model arbitrary valid occurrence partitions, **not** the real greedy endpoint-capacity decisions; they are not Lean verification.

**NOT RUN:** Lean/Lake, CI, kernel replay, transitive axiom audit, Codex or heavy producer. In particular the new `Finset.sum_div` rearrangement, let-bound group equalities and predecessor tensor/permutation modules all remain **elaboration-untested**. SOURCE_ONLY imports under docs have not been staged into the production Lean module tree; static/finite results do not warrant GREEN. This packet made no production, main-branch, toolchain/lock, manuscript, PR, full87 dynamic-parent, other task, or external board change.

**External boundary:** `EXTERNAL_INPUTS.json` unchanged, blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; the restricted medium analytic input (M) is REGISTERED ONLY, with no implementation or added axiom. The new finite identity uses no outside input.

**Next real entrance:** (1) derive the **actual physical PP atom-to-frozen-input hword** dictionary from the original source/compiler, rather than supplying that equality; identify the actual marked/rough labels, original c and residual-slot normalization. (2) Connect the normalized three-gamma physical tensor with the **same integer rho**, full original physical modulus family, squarefree mask, and exact coprime mean on each original source class; do not silently replace auxiliary/physical levels. (3) Separately establish the near-linear mixed shift moment with strict κ, complete product exactly T, rho/totient mass, truly uniform W_T growing-m Fourier conditions and H-tail/Fubini, causal/whole-box, all HB words, empty Gamma mothers and high-rank/enhanced alternatives. All are manuscript-internal; not new external inputs.

**Status:** P3.6 remains YELLOW. The just-described finite physical-gamma ledger is BLUE only in its explicit SOURCE_ONLY/UNCOMPILED/KERNEL_UNVERIFIED scope; no new GREEN, and full same-rho PP assembly remains open.


## P3.6 SOURCE_ONLY successor — actual sorted original fine word to physical three-gamma (2026-11-06 UTC)

**Verified baseline:** `f9a22a11a5b72fe9e80f4fedc3ae276ce590cedc`, branch `chatgpt/p3-internal-original-w-20261105`; source commit `a62a97f77cd2fbaa90a27158ef8b53c931270c98` ([skip ci]), path `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualSortedFineSourceGamma.lean`, Git blob `aa8c1457808df3a24ce25c6aabdf1c8bec6531d5`, 148 lines. Audit registration commit `9e58a70938311960e9fa0a63addf7daf6c2ea430`, VERIFY blob `3b8ca039e0d74f5eb3f470258ffed0c60bff0c5e`. Registry updated at `611075b5ec057de3ddc094bc55b7362f97e750d3` with blob `99a4990e68e594bfc330015ee3986f56c9254b8c`. The final REPORT commit follows; avoid self-referential SHA. Pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §3 (T) and §4 (F), together with `paper/source/manuscript-body.tex`. Fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**Genuine manuscript-internal increment:** The predecessor physical frozen three-`gamma` tensor still required a caller to hand in `hword` and a separate distinct-label block dictionary `blocks`. The ORIGINAL upstream `ActualPrimeFineWordMultiplicity` already computes exact run-length blocks from the genuine weakly decreasing fine-label `input = p0::p1::p2::tail`, and has source theorems `actualPrimeFineLabelBlocksOfWord_word`, `_order`, `_factorial`. The new `actual_fine_word_physical_tensor` directly derives `hword`, distinct original block labels, and the exact original `M_J=∏_I m_I!` from these fixed APIs. It then composes the actual frozen **three whole physical group boxes**, the same original complete integer product, and the previous literal normalized `gamma` tensor. No caller-chosen run-length blocks or new normalization coefficient are introduced.

The further `actual_sorted_fine_source_gamma` invokes the existing `actualPrimeFineWord_original_scalar` to start from the **literal original sorted-squarefree prime-product selector**, with original sign `c` and the genuine Mobius factor `mu(r*n)` kept inside the test function. It transports the original source to the three-group finite convolution:
`c * sum_(n in actual_sorted_products) mu(r*n) H(n) = c*(M0*M1*M2/M_J)*sum_(a,b,d) gamma0(a)gamma1(b)gamma2(d) mu(r*abd) H(abd)`.
This is an exact signed finite full-product identity **on the original weakly ordered fine-word source domain**, not an arbitrary-source PP estimate. The outside `r` is NOT the physical modulus weight `rho_T`; source coefficient identification with the SAME integer `rho_T`, physical modulus set, global squarefree mask and exact coprime mean remains unproved.

**Actual source reads:** prior unique REPORT, REGISTRY and EXTERNAL_INPUTS, `P3ActualFrozenPhysicalGamma.lean`, group-word/count/split proofs, `ActualPrimeFineWordMultiplicity.lean`, `ActualPrimeFineWordSlotRegrouping.lean`, and fixed manuscript §3–4. Root AGENTS.md was queried and returned NOT_FOUND (no hidden rule inferred). No production, fixed manuscript, toolchain, other task branch or excluded full87 node changed.

**Checks / limits:** new source was actually read back from GitHub with exact blob `aa8c1457808df3a24ce25c6aabdf1c8bec6531d5`; forbidden proof-escape tokens **0**, lexical delimiter stack **balanced**. Independent exact-integer finite regression had **1,400 source words, 4,200 assertions, 0 failures**; 1,257 repeat-label cases, 450 cases with an empty one of three groups, 950 with all three groups nonempty, 584 positive and 46 negative signed sums. It checks exact original/sorted Mobius squarefree cancellation, finite convolution under a fixed occurrence partition and `M0*M1*M2≤M_J`. It does **NOT** simulate the endpoint-capacity decisions of the actual frozen allocator and is NOT Lean elaboration. `VERIFY.lean` now registers the two new declaration names but remains unexecuted.

**NOT RUN:** Lean, Lake, CI, kernel replay, complete transitive axiom audit, Codex, heavy producer. Explicit elaboration risks remain at `simp only` on the actual local-let group source and the cross-module theorem-definitional matching. The entire predecessor chain and SOURCE_ONLY import staging are also uncompiled; this does not permit GREEN.

**Precise next entrance:** Map *every actual original PP physical atom* to the now-derived original weak fine-label word (including its real marked/rough/beta scalar), then connect the actual signed three-`gamma` source to the **same integer `rho_T`** and EXACT coprime mean. Still pending independently: original complete physical modulus/totient mass and `b=T` exception, near-linear shifted-divisor moment under strict κ, fully uniform `W_T` derivatives and Fourier H, causal whole-box admission, all HB source branches, empty Gamma mother words, enhanced/high rank. External (M) remains REGISTERED ONLY, blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; not implemented or axiomatized. No new axiom, target-equivalent hypothesis, or arbitrary relative fibre bound.

**Status:** P3.6 YELLOW. This exact original-sorted-fine-source to frozen `gamma` identification is BLUE only as SOURCE_ONLY/UNCOMPILED/KERNEL_UNVERIFIED. No new GREEN.


## SOURCE_ONLY successor — actual original labelled W and same-rho weighted fibres (2026-11-06)

- **Verified prior branch HEAD:** `01b3fff6528bfba00156aa636d15f149e50460d9`; source-only next file `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualWeightedFineSameRho.lean`, source Git blob `4259a3a0a68138834c558fbe2f8027fd80528b84` (157 physical lines). One atomic `[skip ci]` tree commit is used for source, VERIFY, REGISTRY and this unique handoff; report does not guess its own commit SHA. Pinned manuscript `9731290e8f53cffda44129906cde6a965eaa869b` §1, §3 (T), §4 (F); Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- **New mathematical need:** Prior `actual_sorted_fine_source_gamma` is an exact identity for `H(full-product)` only, whereas the original geometric W may depend on EACH LABELLED TUPLE. Treating it as product-only or dividing an arbitrary W by the raw repeated-label factorial would be wrong: one label appearing twice with primes {2,3} and W(first)=first has sorted W(3,2)=3 but raw average (W(2,3)+W(3,2))/2=5/2. This packet therefore does **not** claim weighted gamma-one-bound or all-atom admissibility.
- **Actual increment:** `weighted_sum_by_product` proves exact finite pushforward with the TRUE tuple-weighted product fibre. `weightedSortedPP_fibre` instantiates the literal `actualPrimeFineLabelSortedTuples` source and keeps original signed `c`, full Mobius `mu(r*n)`, exact integer complete products, every original modulus q and the **identical rho(q)** across the counting and exact coprime mean test. `fineKernel_literal` identifies the original exact congruence-minus-coprime-mean; no new arithmetic mask is inserted. `weightedSortedPP_exact_product` isolates the b=T slice after the complete modulus sum and factors the true `1-1/phi(q)` under `(q,T)=1`; it makes NO smallness assertion, and never uses tau(0). These are original finite algebra lemmas, not a PP discrepancy estimate.
- **Independent checks:** source blob read back; forbidden proof escapes zero; exact rational finite Python regression on 750 original strictly sorted fine-label sources, 1,500 count/mean and exact-b=T identities, zero failures, including arbitrary position-dependent W and signed rho. The raw/sorted W counterexample was checked exactly. GitHub AGENTS checks at root/docs/source-only/packet were NOT_FOUND. VERIFY #checks have been registered but NOT executed.
- **NOT RUN:** Lean/Lake, CI, kernel replay, transitive axiom audit, Codex, heavy producer. The entire SOURCE_ONLY chain including finite Fubini rewrite and `Fin 1` test normalization is elaboration-unverified. No green. `EXTERNAL_INPUTS.json` unchanged `(M)` register only; no external input implementation or new axiom, no manuscript, production, toolchain, full87, other task branch or PR change.
- **Next:** Prove Fourier-separated original labelled W identities that allow legitimate gamma normalization, and attach the actual physical atom compiler's rho_T, Q and exact coprime mean to this ledger. Independently pay the nonzero-shift mixed moment, b=T exceptional coefficient mass, rho/totient mass, uniform W_T/H, causal/all HB, empty Gamma, high-rank/enhanced and same-rho PP total.

**Status:** P3.6 YELLOW. This original labelled weighted finite-source/same-rho ledger is BLUE only in its SOURCE_ONLY, UNCOMPILED and KERNEL_UNVERIFIED scope.

## Successor SOURCE_ONLY — arbitrary original W fibre to true frozen gamma, one rho (2026-11-07 UTC)

- **Actual recovery baseline:** `439fe64cc7c734938b400c39ecb82d13f333a201` on the existing independent branch `chatgpt/p3-internal-original-w-20261105`. GitHub branch HEAD was rechecked at that SHA before writing; no concurrent writer was observed in these checks.
- **New proof file:** `P3ActualWeightedThreeGamma.lean`, 137 lines, Git blob `89001c3b232a78960088f5eec975f220e6db8167`, commit `b26f45a3412a3fade6a62a96457f1185843849dc` (`[skip ci]`). This was read back from GitHub. `VERIFY.lean` was updated in commit `bcf862bd7c3493c3a4bce8b98f91e26f34885eef`, blob `e09a4a3dc2ee1aba13a5604bf1c9fe81bc691f6f`, adding the two check targets (not executed). `REGISTRY.json` was updated in `11e910ede0b04f45826a8e7661fa43e300d5ba4c`, blob `5412150e5f0c083899be79acd194dd182d04a3d1`. This is the **same unique handoff**; no second report or duplicate project branch was created.
- **Fixed provenance:** manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §1 (exact PP kernel), §3 (original three-gamma identity T), §4 (geometric W and F); Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Root and packet AGENTS checks returned NOT_FOUND; no unwritten instruction was inferred.

### Actual mathematical step, with an explicit limitation

The previous round kept arbitrary tuple-dependent `W(ps)` and the **same rho(q)** in the exact congruence-minus-coprime mean, but its fibre ledger was still separate from the original three-gamma coefficient compiler. Earlier `actual_sorted_fine_source_gamma` applies to an `H(n)` depending only on full product. This round makes a **valid** bridge by first forming the actual sorted weight fibre

`A_W(n) = sum_(ps in original sorted fine box, prod(ps)=n) W(ps)`

and then passing `H_q(n) = A_W(n) * (1_(n=T mod q) - 1_((n,q)=1)/phi(q))` to the actual weak-word / run-length / three-frozen-gamma identity. Both results are candidate finite proofs:

1. `weighted_sorted_three_gamma_one_modulus` proves the raw signed Möbius fibre sum for **one literal q** equals the original three `gamma_i` convolution with scalar `c * M_0 M_1 M_2 / M_all`, full product `abd`, and **the unchanged `A_W(abd)`**. Neither the original slot labels nor the repeated-label factorial are silently removed.
2. `weighted_sorted_three_gamma_same_rho` composes that identity over the unchanged finite physical modulus set `Q`, multiplying each complete q-summand by the **same integer `rho(q)`** as in the exact counting and exact coprime mean. In particular it does not introduce a second mean weight, choose a new arithmetic level, merge physical and auxiliary cutoffs, or claim a relative sparse-fibre bound.

The crucial boundary: `A_W(n)` is generally **neither** one-bounded **nor** a Fourier-separated product of slot functions. This equality therefore does **NOT** turn arbitrary `W_T` into an admissible one-bounded medium gamma coefficient. Fourier factorization and within-repeated-label permutation symmetrization remain necessary and are **internal**, not external classical inputs. The concrete original compiler's `rho_T` and all its physical atom and mask data must still be identified; the equality currently retains a given single `rho`, not a proved identification of every physical source.

### Actual checks and trust boundary

- Exact branch HEAD, previous unique REPORT/REGISTRY/EXTERNAL_INPUTS and proof source, old real frozen three-gamma source, word multiplicity and sorted selector, and fixed manuscript §1–4 were read. Root/packet AGENTS checks returned NOT_FOUND.
- The new 137-line source was scanned: **0** forbidden proof-escape tokens; stripped-comment delimiter balance **PASS**. The source blob was independently read back from GitHub. The VERIFY import is before its checks. The expanded registry passed JSON parsing.
- Independent **exact rational** finite regression: **10,800 / 10,800 identities passed, 0 failed** for 900 weak descending original words of lengths 1–4, arbitrary occurrence splits among three groups, 4 q values and 3 target values, signed c and rho, external Mobius r, and **position-dependent W**. **4,174** expected identities had nonzero left sides. Tests use disjoint finite prime label boxes and do **NOT** reproduce the real frozen endpoint-capacity allocator. They establish sanity of the finite algebra only; they do not prove the Lean declarations or any asymptotic estimate.
- **NOT RUN by instruction:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, heavy numerical producer. `simpa only` alignment of local let-defined source/blocks and all upstream SOURCE_ONLY imports remain elaboration-sensitive. This work is **BLUE SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED**, not GREEN. No new theorem was assumed as a hypothesis to disguise PP.
- `EXTERNAL_INPUTS.json` remains blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; the medium estimate (M) is REGISTER ONLY, neither implemented nor asserted as an additional trusted declaration. Untouched: production proof, pinned manuscript, toolchain/lockfiles, other tasks, PR, CI, external board and excluded full87 dynamic-parent node.

**Next real entrance:** prove a true Fourier decomposition of the original geometric `W_T` which respects the **ordered within-label slots** (or an exactly justified symmetrization), with uniform mixed derivative budgets, L1/Fubini and one common H for growing m(N). Only after separability may an admitted gamma source be invoked. Identify all original physical `rho_T` atom/mask/compiler cases and pay the nonzero-shift near-linear mixed moment, complete-product=T exceptional mass, complete rho/totient mass and the causal / all-HB / empty-Gamma / enhanced branches. These obligations remain **manuscript internal**, not entries to the external-input register.

**Status:** P3.6 YELLOW; local exact weighted-fibre-to-gamma same-rho SOURCE_ONLY candidate BLUE, uncompiled; no new green.

## Successor SOURCE_ONLY — actual sorted weighted fibre injectivity (2026-11-07 UTC)

- **Read and verified baseline:** `03a741da12feb7c3ff79d784a5159afa2fccd393` on `chatgpt/p3-internal-original-w-20261105`; previous REPORT, REGISTRY, EXTERNAL_INPUTS, weighted fine-source and three-gamma candidates, original fixed-library sorted selector/product injectivity, and pinned §3 (T)/§4 (F) were inspected. Root and parent/packet AGENTS paths queried: NOT_FOUND; no hidden constraints inferred.
- **New source commit:** `4fde64144cb2a963cefadf2f529a5ffedf57b7b6` ([skip ci]), new `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualWeightedFibreInjective.lean`, Git blob `9df1e4a51e3c6c680ff111c06057de57d4d89e75`. VERIFY blob `f6ab4ba858546b45d287474b2e01cdf0733414da`; imports precede all added #check statements (not executed).
- **Real mathematical increment:** Existing `actualPrimeFineLabelSortedTuples_product_injective` gives exact singleton fibres for each original strictly descending prime tuple; thus `weightedFineFibre(N,τ,blocks,W,ps.prod)=W(ps)`. Off original product support it is zero. Consequently if the ORIGINAL tuple-dependent weight satisfies `∀ ps ∈ sorted source, |W ps|≤1`, then `∀ n, |weightedFineFibre(n)|≤1`. This closes a local one-bound gap on the *sorted* weighted pushforward; arbitrary unbounded W remains unbounded and no groupwise gamma separability follows.
- **Independent finite regression:** 2505 assertions, 0 failures, 44 nonzero-fibre cases for distinct primes [2,3,5,7,11,13], strictly decreasing lists of length 0..4 and n=0..500 with signed position-dependent W (bounded by 1). No real endpoint allocator, Fourier product, arithmetic estimate or Lean semantics simulated.
- **Unperformed:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex and heavy producer. Existing upstream modules remain SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED. The new use of `Finset.mem_image` and singleton rewrites remains elaboration-sensitive. No node becomes green.
- **Trust boundary:** This does not give a product decomposition of W across frozen groups, does not assert W_T is uniformly one-bounded after physical Fourier cutoffs, and does not bind generic rho to the full original rho_T compiler. Full-modulus/totient mean, nonzero-shift arithmetic moment, complete product=T exception, causal/whole-box, all HB words, empty Gamma, high-rank/enhanced and final PP remain manuscript-internal. Registered external (M) unchanged; no new axiom.
- **Next:** establish admissible original Fourier-separated W_T modes respecting within-label slot permutations and uniform T,m(N) L1/H tail; then identify physical rho_T and pay all modulus errors including n=T.

**Status:** P3.6 YELLOW. This precise bounded-weight sorted-fibre claim is BLUE only as SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED.

## P3.6 SOURCE_ONLY successor — bounded positional original group gamma fibres (2026-11-07)

**Recovery and immutable evidence.** Checked branch `chatgpt/p3-internal-original-w-20261105` at actual HEAD `09693403b75f732b139098fea5691f2defa74c41`, not the obsolete de582e6 recovery starting point. Read the existing unique REPORT/REGISTRY/EXTERNAL_INPUTS, last weighted original-fibre proof, frozen three-group and labelled tensor sources, fixed-library `ActualPrimeFineLabelSortedSelector`, `ActualPrimeTupleNormalization`, `ActualPrimeFineWordSlotRegrouping`, and the pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, prime-product completion §§1,3(T),4(F), with the corresponding manuscript body. Root, docs, source-only and packet `AGENTS.md` each returned GitHub NOT_FOUND. This run neither edited the manuscript nor followed master. The fixed Mathlib pin stays `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**Concrete proof body.** New `P3ActualBoundedGroupWeightGamma.lean` (137 lines) was created in commit `db846ff3d8b519888b9ad2b3dfebb26b60677b3b` and received a normalization rewrite repair in commit `25a34bbec5f97f5532fe044994aad622cc801d53`, both `[skip ci]`; final source Git blob `5b139023f9ecc021c578f2df584f431d351ed963`. The `VERIFY.lean` import and six declaration checks were registered in commit `b3a9976e330df1a290944de50ee9e813fa8c532b` (Git blob `e4130730d6d8a3c59f281d816beed0281b650d1b`); they have **not** been executed. REGISTRY record added in `6f9f9a8c855a93823133b151343db27a260cb276` (Git blob `503992d83676dde1d0fba09da4afd1e7d8ddb768`). This existing REPORT is the only P3.6 handoff record; its own enclosing Git commit is deliberately not self-referential.

**Nontrivial manuscript-internal mathematics.** An original group consists of precisely the prime-slot Cartesian box for its distinct fine-label blocks, retaining its **actual per-label factorial** `M_j=prod_I m_(I,j)!`. A separated Fourier mode can be position-dependent *within* a repeated-label group. It is false to replace its ordered tuple multiplier `v(ps)` by a function of the group product without a proof. Define
`gamma_v(n) = M_j^-1 * sum_(ps in original group box, prod(ps)=n) v(ps)`.
The candidate `weightedLabelGamma_abs_le_gamma` proves directly by the triangle inequality and literal fibre cardinality that whenever `|v(ps)|<=1` on its original ordered group box,
`|gamma_v(n)| <= gamma_unweighted(n)` **for every integer n**, including repeated-prime diagonals and outside the support. The *already present* original disjoint half-open fine-label prime theorem gives `0<=gamma_unweighted(n)<=1`; new `weightedLabelGamma_abs_le_one` therefore obtains **one-bounded positional** group coefficients. No fabricated fibrewise relative `Theta` estimate, PP error, or new structural PP assumption is introduced.

`weightedLabelGamma_sum_by_product` transports a general ordered group multiplier exactly through its group complete-product fibres, with the correct literal `M_j`, retaining all tuple multiplicities. `weightedLabelGamma_of_product_twist` identifies the **special** case `v(ps)=f(prod(ps))` with the old `gamma(n) f(n)`; this equation is not asserted for arbitrary positional weights. `weightedLabelGamma_add` gives the finite linearity required before any Fourier L1 integration. These are meaningful coefficient bounds and fibre identities for an individual group, **not yet** the actual three-group product decomposition of `W_T`.

**Independent checks / hard limits.** Before creating the file, checked the branch HEAD and absence of a same-named source; the new source was lexically scanned for forbidden proof-escape terms (**0**) and balanced delimiters (**PASS**). Independent finite arithmetic regression tested **1,200 / 1,200** inequalities with zero failures and **355** nontrivial repeated-label product-collision fibres. The test enumerated three disjoint finite prime-label alphabets, group multiplicities up to 3,3,2, and signed position-dependent rational-step weights bounded by one; it checked the real mathematical inequalities `|sum_fibre v| <= count_fibre <= M_j`, **not** Lean typing or every true frozen endpoint rule. A static repair changed `Finset.sum_div` to the inverse rewrite direction consistent with the repository's existing normalized group lemma. Public Mathlib sources show `Finset.abs_sum_le_sum_abs` in use; the exact fixed Mathlib pin was not typechecked.

**NOT RUN:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, or heavy producer. Source imports under `docs/source-only` and the new proof's elaboration remain unverified; no GREEN state follows. The resulting local coefficient theorem is **BLUE SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED**, and P3.6 remains **YELLOW**.

**Exact next entry.** Prove a faithful Fourier representation for each actual original geometric `W_T` on every true physical atom where each mode is *a product of three bounded ordered-group tuple multipliers*, retaining the frozen original slot assignment and each group factorial; then use the new genuine `gamma_v` norm bound and actual group-size/endpoint bounds. Do not replace this representation by the tautological statement that a weight is already decomposable. Establish uniform Fourier L1/Fubini, quantitative common H and growing m(N); identify every actual physical `rho_T` atom and global squarefree mask, then pay full same-rho shifted mixed moments, product=T and totient mean mass. Causal whole-box licences, all HB sources, empty Gamma mothers, high rank/enhanced and final PP assembly remain **internal**. The exact external (M) research input stays **registered only** in unchanged `EXTERNAL_INPUTS.json`, Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`, not an implemented theorem or axiom. Excluded full87 dynamic parent, production, other task branches, locks, dashboard, PRs and master were untouched.

**Status:** P3.6 YELLOW; actual fine-label group positional Fourier multiplier coefficient interface BLUE at the source-only boundary; no new GREEN.

## P3.6 SOURCE_ONLY successor — genuinely complex positional gamma and finite Fourier-mode L1 (2026-11-07 UTC)

**True continuation and provenance.** The task's independent branch `chatgpt/p3-internal-original-w-20261105` was verified at HEAD `7be37d0c16678734e74cc53dea955e3c0ac701ab`; this is the existing latest previous handoff, not the obsolete initial `de582e6`. The existing single REPORT, REGISTRY, EXTERNAL_INPUTS and actual positional real gamma source were read. Root, `docs/`, `docs/source-only/` and packet `AGENTS.md` paths were checked and returned NOT_FOUND; no invented constraints. Pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b` §3 (T), §4 (F) and actual manuscript body were inspected. Fixed Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged.

**Original mathematical increment.** The prior `weightedLabelGamma` only accepts real tuple multipliers. The genuine Fourier phase and its amplitudes are complex; treating them as real or silently discarding imaginary parts would not instantiate manuscript (F). New `P3ActualComplexPositionalGammaModes.lean` defines, for the ORIGINAL group labelled ordered prime-slot box and its actual repeated-label factorial `M_j`,

`gamma_(j,v)(n) = (1/M_j) sum_(ps in group, prod ps=n) v(ps) ∈ ℂ.`

The new `complexWeightedLabelGamma_norm_le_gamma` derives from the true complex norm triangle inequality

`‖gamma_(j,v)(n)‖ <= gamma_j(n)`

under pointwise `‖v(ps)‖<=1` on the *ordered* physical group box, with no within-label permutation invariance or product-dependent `v`. The existing original disjoint half-open prime-label theorem `fine_gamma_mem_Icc` then yields `complexWeightedLabelGamma_norm_le_one`. This controls all product fibres, including the empty fibre and repeated-prime diagonals, without a false relative-Theta claim.

The third theorem `finite_three_complex_modes_norm_le_l1` is a true **finite Fourier-mode coefficient budget** for three such labelled groups: for complex amplitudes `amp(k)`, exactly

`‖Σ_(k∈K) amp(k) gamma_(0,v0(k))(a) gamma_(1,v1(k))(b) gamma_(2,v2(k))(d)‖ <= Σ_(k∈K) ‖amp(k)‖.`

The result has no `H^m` mode-count cost and retains individual complex phases. Its premises include each group's actual distinct fine-label blocks, `N>=1`, `tau>=0` and each complex positional multiplier one-bounded on its literal box. It is not itself a representation of the actual `W_T`; nor is the finite sum an automatic continuous Fourier inversion, Fubini or uniform H-tail.

**GitHub writes (all [skip ci]).** Proof source created in `7bdd1364b3e72ad4d060c12478fdd841a4ad5f35`, followed by a proof-rewrite static repair in `68204d91a72b6467d831160ca5387eb33f3c53dd` to use `simp only [mul_assoc]` instead of ambiguous successive associative rewrites. Final source blob: `e5c5836eca7b9400295a210890f8f65563f43128`. `VERIFY.lean` import and four unexecuted check declarations were recorded in `cc394d4bf0b4d7ac0dcb6c86bac5af553ffd8d3a`, blob `62bd12ed29a2e96da29da6bd883689d23e515a1e`. The sole `REGISTRY.json` was updated, most recently in `5446d019a151a029e33893fd815d9cb8b5aea3aa`, blob `1b8b8b9cef023407759bc5fa003565df6a095287`. The encompassing report update necessarily does not contain its own future commit SHA; recover it from branch HEAD.

**Checks, limits and trust.** Initial new-source lexical ban scan reported 0 proof escape tokens and a balanced delimiter stack; the small associative rewrite did not change theorem statements. Independent Python tests: 1,950 **exact rational complex squared-norm fibre** inequalities, including 598 nontrivial repeated-label collision fibres; 650 three-complex-group product norm cases; and 1,000 finite complex-mode norm-versus-sum-of-amplitudes cases. All passed. The first exploratory finite test deliberately exposed an invalid sample generator (complex real and imaginary components bounded separately are NOT sufficient to have complex norm <=1, and overlapping label alphabets violate source hypotheses); the generator was corrected to use actual norm-one samples and pairwise-disjoint prime alphabets **before** those successful counts. These tests are sanity checks only, not Lean semantics or the real frozen endpoint algorithm.

**Explicitly NOT RUN** by task instructions: Lean, Lake, CI, kernel replay, full axiom audit, Codex, heavy producer. The precise `norm_sum_le` and complex norm/cast tactics and the entire upstream SOURCE_ONLY chain remain elaboration-sensitive; no GREEN claim or full PP theorem. `EXTERNAL_INPUTS.json` retains exactly registered outside medium estimate (M), blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; (M) is not implemented, assumed as a new axiom or invoked. No production proof, manuscript, lockfile, other tasks, PR, CI, dashboard or excluded full87 dynamic-parent node touched.

**Next genuine internal entry.** Connect the *actual* `W_T` Fourier expansion, with correct physical coordinate chart, ordered original frozen slot assignment, full original multiplicities, normalized complex three-group positional coefficients and phase, to this finite-mode bound. Prove the proper continuous L1/Fubini/common quantitative H-tail with T,m(N) uniformity rather than H^m counting or fixed-smoothing extrapolation. Independently identify every original PP physical atom's `rho_T`, global squarefree mask and exact coprime mean, and pay the nonzero-shift mixed moment, full product=T exceptional contribution, complete modulus/totient mass, causal/all HB/empty Gamma/high-rank/enhanced cases. All remain manuscript internal. **P3.6 stays YELLOW; only this local complex coefficient and finite-mode interface is BLUE SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED. No new GREEN.**
## P3.6 SOURCE_ONLY successor — complex positional mode finite-fibre transport (2026-11-07 UTC)

**Verified recovery.** Continued from actual P3.6 branch HEAD `7638cdf2342230284cae83a900b22f2d5644c53d` on `chatgpt/p3-internal-original-w-20261105`, not the obsolete `de582e6`. Read the single REPORT, REGISTRY and EXTERNAL_INPUTS at that HEAD and existing positional real/complex gamma, fineKernel, weighted same-rho source and original sorted/frozen gamma sources. Examined the pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §3 (T) and §4 (F), and `paper/source/manuscript-body.tex`. Root, `docs/`, `docs/source-only/` and packet `AGENTS.md` returned NOT_FOUND, so no unseen instructions are claimed. The independent branch ref was checked both before writing and before advancing with an expected-head non-forced lease.

**Actual proof commit:** `58545bab4355656647cef82ee12e88dc00814af9` ([skip ci]), `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualComplexModeFibreTransport.lean`, **152 source lines**, Git blob `8c484035f2eeca07005a4ccd70296e120882c0b4`. Also updates `VERIFY.lean` (blob `923dbeb947ed75105adc625f1890c8adb4b536b2`, **five additional #check declarations unexecuted**) and the unique `REGISTRY.json` (blob `b3b3e5b7608e358686c75e812e71a5e38d8390e4`). The enclosing handoff commit can be recovered as the later branch HEAD; this handoff deliberately does not predict its own SHA.

**New true finite combinatorics (candidate Lean declarations).** Previous `complexWeightedLabelGamma_norm_le_one` proves a bounded positional coefficient, but does not show a complex positional mode can be moved **through** its original product fibres or commuted with a finite Fourier sum. The five new proof candidates are:
- `complex_weighted_sum_by_product`: exact partition of an arbitrary complex weighted ordered tuple sum by full integer product, with every repeated tuple occurrence preserved;
- `complexWeightedLabelGamma_sum_by_product`: the same after dividing by the ORIGINAL per-label factorial `M_group`, not the total-slot factorial;
- `complexWeightedLabelGamma_modes`: literal finite complex Fourier amplitude sums commute with the weighted fibre, without demanding that any positional mode be invariant under within-label permutations;
- `complex_finite_modes_group_transport`: exact mode-weighted group sum equals the weighted complex-gamma sum at each complete product, with one original `M_group`;
- `complex_finite_modes_same_rho_group`: the preceding identity holds for every literal physical modulus in a finite `Q`, multiplying the **same integer rho(q)** against the unchanged `fineKernel(T,q,n)` (congruence minus exact coprime mean), with no separate artificial mean coefficient.

This is a **single original labelled group** finite identity, not the three-fold physical tensor. The original geometric `W_T` has not been shown to be a finite or continuous product of such modes, and the real PP atom compiler's `rho_T` has not been identified. In particular, there is no attempt to add a fibrewise relative-Theta target or to use norm-one gamma bounds as a substitute for the full arithmetic discrepancy. The complete-product `n=T` term is retained in `fineKernel` but its mass is **not** paid.

**Checks and their precise limits.** Independent Python exact Fraction-pair (non-floating-point complex) regression checked **1500 / 1500** finite same-q/same-rho model identities across 500 repeated/empty-label group cases and three physical q values: 0 failures, **1469 nonreal** aggregate cases and **580 repeated-label product-collision fibres**. The finite regression tests the algebra, not the true original endpoint allocator, physical PP atom compiler, Lean syntax or kernel. Source lexical delimiter check PASSED and forbidden proof escape tokens were 0; five new #check declarations were inserted after imports, not executed. Git blobs, branch ref and commit were confirmed by actual connector writes, with no forced ref update. No new axioms or source-equivalent target premises.

**NOT RUN by instruction:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, heavy producers. New and upstream declarations stay `SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED`. **No green node**; P3.6 remains **YELLOW**.

**External boundary and noninterference.** `EXTERNAL_INPUTS.json` stays the exact previous Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: outside restricted medium estimate (M) is REGISTER ONLY / NOT IMPLEMENTED / NOT AXIOM. No manuscript edit, production proof edit, toolchain/lock update, CI execution, PR/merge, parent branch update, other task, external dashboard or excluded full87 dynamic-parent work.

**Next specific internal entrance.** Upgrade this true one-group complex finite mode transport to the **three genuine frozen ordered groups** with original label/multiplicity and M_all/M_j restoration; then prove the actual physical geometry `W_T` has the required separated positional Fourier representation (not merely postulate it). Establish true continuous L1/Fubini, quantitative common H and uniformity in growing m(N), identify each actual `rho_T` physical PP atom and global squarefree mask, and pay nonzero shifted mixed divisor moments, exact n=T contribution, rho/totient modulus mass, causal/whole boxes, all HB, empty Gamma and high-rank/enhanced cases. All those are manuscript-internal. **P3.6 YELLOW; this bounded finite group transport BLUE as source-only candidate; no GREEN.**

## P3.6 SOURCE_ONLY successor — physical frozen positional COMPLEX group gamma (2026-11-07 UTC)

**Recovery.** Verified exact independent branch HEAD `451b7316cd8abc01535ab827fd7a18ee12cbaa8b` and read the previous complex-mode group transport, single REPORT, REGISTRY, EXTERNAL_INPUTS, fixed source `P5ActualNormalizedPrimeLabelCoefficient.lean`, and actual frozen label permutation and factorial proofs. Root `AGENTS.md` returned NOT_FOUND. Reviewed pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, completion §3 (T), §4 (F), and manuscript-body PP statement. No master upgrade or other task change.

**Actual mathematical fix.** Prior `complexWeightedLabelGamma` uses a reconstructed `splitBlocks` tuple word. Existing `actual_frozen_group_words_perm` permutes LABEL WORDS and preserves UNWEIGHTED full-product fibre cardinalities. It does **not** permit blindly transporting an arbitrary positional complex Fourier mode through that permutation, because the physical tuple coordinates are reordered. The new `P3ActualFrozenComplexGroupGamma.lean` therefore defines `physicalComplexLabelGamma B physicalWord splitBlocks v n` directly on the actual ordered physical group box, divided by the EXACT original group factorial `M_j`. It proves candidate finite complete-product transport, equality of unweighted fibre cardinalities under the known label-word permutation (with an indicator test), complex triangle domination by the reconstructed unweighted gamma, then norm <=1 using existing disjoint half-open fine-label gamma theorem. A final candidate instantiates this separately for **all three actual output words** of `actualFrozenSelectedPairSlots`, including groups with repeated labels or zero slots. No assertion `v(ps)=v(perm ps)` is made, and no tautological Fourier-decomposability premise is added.

**Checks and immutability.** Static forbidden-proof-escape scan 0, delimiter scan PASS; six #check declarations registered in VERIFY, **not run**. Independent Python exact Gaussian-integer model checked 720 physical-word permutations and 720 exact weighted full-product sum transports across 11,127 nonempty product fibres (7,190 with repeated-label product collisions), with zero failures; positional weights vary by ordered tuple. This tests elementary algebra/cardinality, not the actual frozen endpoint allocator nor Lean elaboration. New source and registry are in this ONE task branch; atomic commit planned with `[skip ci]` and non-forced expected-head lease, to be confirmed by GitHub before claiming success.

**Scope and outstanding.** The new physical positional coefficients are correctly bounded but their simultaneous three-group tensor and common Fourier mode representation of original `W_T` are NOT proved. Continuous Fourier L1/Fubini, quantitative common H for growing m(N), all physical PP atom rho_T dictionary/squarefree mask, complete modulus mean, mixed nonzero-shift divisor moment, product=T exception, causal/whole-box, all HB/empty Gamma and high-rank/enhanced branches remain manuscript INTERNAL. External restricted (M) stays recorded only, Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; no outside proof or axiom was introduced. Lean/Lake, CI, kernel replay, transitive axiom audit, Codex and heavy producer NOT RUN. P3.6 remains YELLOW; this narrowly specified physical group coefficient source is BLUE SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED; NO GREEN.

**GitHub readback source commit:** `9f1cae360f5a5e2d4c07b81a5c45b96ffd0d4b8a` on `chatgpt/p3-internal-original-w-20261105`, verified after non-forced expected-head update. The exact new Lean source blob is `5c38bd402571bdd3669109a4c8eaa23c053934a3`, the source contains 196 lines, and comparison with `451b7316cd8abc01535ab827fd7a18ee12cbaa8b` returned `ahead=1, behind=0`, exactly four task-related files. This source commit and its separate handoff follow-up both use `[skip ci]`; no Lean/Lake/CI/kernel work was run. The handoff follow-up deliberately does not self-reference its own commit SHA.

## P3.6 SOURCE_ONLY successor — physical three-group complex fibre tensor (2026-11-07 UTC)

**Recovery and scope.** Read branch HEAD `32bd63a65f3af905d0fdbb2afec24def5c156eab`, the previous physical complex-group proof and actual frozen/split factorial and complex fibre modules, plus this task's single REPORT, REGISTRY, EXTERNAL_INPUTS and VERIFY. Root and nested AGENTS paths returned 404. The pinned manuscript was read at `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, notably manuscript-body.tex PP lines 256–276 and completion §3 (T) / §4 (F); no master migration.

**New actual proof candidates.** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualFrozenComplexThreeTensor.lean` (Git blob `81cc90dc77cdbf92ddc3c43a57a346adc88ef547`, 268 lines) provides `complex_three_weighted_fibre`: a genuine three-stage finite Fubini pushforward of arbitrary positional **complex** ordered-tuple weights through individual full integer products. `actual_frozen_three_complex_tensor` restores the literal three actual frozen physical words and exact original per-label `M_0 M_1 M_2 / M_all` normalization; it does not permute positional v and retains repeated-label collision fibres. `actual_frozen_three_complex_same_rho` applies the same algebra to the exact physical `fineKernel T q (a*b*d)`, using the **same integer rho(q)** against the unchanged count and exact coprime mean. The last theorem has Q/rho as PARAMETERS: it does **not** identify the actual PP atom compiler or prove W_T Fourier admission or any bound.

**Independent checks.** Python exact Gaussian-integer mode weights with exact Fraction progression-minus-coprime mean checked **1800/1800** randomly generated three-group cases and **9000/9000** modulus identities (q=2,3,5,7,11): zero failures. Included 1115 multiply-colliding-fibre cases and 1071 empty-group cases. This regression tested finite algebra only, not original endpoint allocator, the kernel of Lean or full PP atom compiler. Static forbidden escape token scan 0 and balanced delimiters; three #check entries registered, NOT executed. New proof source and single handoff were saved as task-related blobs only; no CI or compilation.

**Nonconclusions.** No Lean, Lake, CI, kernel replay, transitive axiom audit, Codex or heavy producer was run. No new axiom or paper change. Actual W_T Fourier separation and its continuous L1/Fubini/H and growing m(N) quantitative budgets, all concrete physical rho_T and global squarefree masks, modulus arithmetic error and exact b=T exception, causal/whole boxes, all HB/empty Gamma and high-rank/enhanced alternatives remain INTERNAL obligations. Outside restricted (M) stays registration-only `EXTERNAL_INPUTS.json` blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; no outside theorem implemented. P3.6 YELLOW; this narrow three-fold tensor BLUE SOURCE_ONLY, no new green.

**Next specific entrance.** Start with the *actual* geometric `W_T` and prove that each finite Fourier mode on all original ordered slots equals the three positional group multipliers on literal frozen group words (with the correct original prime label dictionary, not by postulating an equivalent conclusion). Then pay continuous Fourier L1/H/m(N) and actual rho_T atom arithmetic independently.


**GitHub verified source commit:** `f7d6b3c5d7acaa813bc158125fd8a00a3d76450b`, branch `chatgpt/p3-internal-original-w-20261105`, confirmed ahead=1 / behind=0 against `32bd63a65f3af905d0fdbb2afec24def5c156eab`, exactly four changed task files. Verified proof source blob `81cc90dc77cdbf92ddc3c43a57a346adc88ef547` (268 lines). This follow-up only records actual readback provenance; both commits use `[skip ci]`. Lean/Lake/kernel still NOT RUN.

## P3.6 SOURCE_ONLY successor — finite complex modes on the three actual frozen groups (2026-11-07 UTC)

**Checked starting branch HEAD:** `c7c454431f97736b37510e6b1cdea1d557451022`.
**Pushed and read-back proof commit:** `29955a2a879405cbc8d603b1c6a59c3690636adf` ([skip ci]).
**New file:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualFrozenComplexThreeModes.lean`, 256 lines, Git blob `346410f4e8e8e805203dd40325642e6d54aeaf4d`.
**VERIFY.lean:** Git blob `e2152094d4c749937dad25d285f3c2b08f7c9316`, four new checks registered only.
**Manuscript pin:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` PP and `paper/source/modules/distribution-prime-product-completion-20261010.txt` §§3 (T), 4 (F).
**Mathlib pin:** `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; toolchain unchanged.

**Mathematical increment:** The prior source treats **one** separated complex positional multiplier on each of the three actual frozen physical ordered words. This packet proves a true **finite common-mode Fubini interchange** on all three original physical boxes, then composes the previous source-only tensor for each mode. Its four declarations are `triple_mode_sum_comm`, `finite_modes_three_sum_transport`, `actual_frozen_three_finite_modes_tensor`, and `actual_frozen_three_finite_modes_same_rho`. The original `M_0 M_1 M_2 / M_all` label-factorial correction occurs exactly once; the full integer product and repeated tuple fibres are unchanged. The literal signed integer `rho(q)` multiplies the **same** `fineKernel(T,q,n)` counting minus exact coprime mean on each side and each physical q in the parameter finite set Q. Each mode's group v_j can depend on actual ordered slot positions. No positional permutation of v_j is asserted, no artificial per-modulus mean, no product-only W, and no fibrewise relative Theta error are introduced.

This is a **constructive algebraic statement for finite separated mode sums**, not a hypothesis claiming the real original geometric `W_T` is such a sum. The true continuous Fourier representation of W_T and its actual frozen coordinate dictionary are still open. The physical modulus family and `rho_T` PP atom compiler remain uninstantiated Q/rho parameters; arithmetic error is not bounded by the exact finite identity.

**Checks actually performed:** GitHub branch HEAD checked immediately before source commit and with a non-forced expected-head ref update; source/VERIFY files read back from the pushed source commit. New source forbidden escape-token scan 0; lexical parentheses and bracket counts balanced; 4 exact registered `#check` references not executed. Independent Python Gaussian-integer/rational exact regression: 900 distinct three-group cases, 3600 same-rho full-modulus checks over q=2,3,5,7, **zero failures**, 2436 group product-fibre collision checks and 283 empty-group cases. Separate 144 exact factorial-ratio tests passed. The regression did not run Lean or simulate the actual frozen allocator; random finite algebra cannot certify the true original domain.

**NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex or heavy producer. All four new declarations and all predecessor proof candidates remain SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED; **NO GREEN**. Root and ancestor packet AGENTS paths were queried and returned NOT_FOUND; no hidden constraints claimed. No production source, manuscript, other task branch, toolchain, lock, excluded full87, PR, merge or dashboard edited.

**Outside boundary:** `EXTERNAL_INPUTS.json` stayed unchanged, Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. Restricted analytic (M) is **record-only / not implemented / not axiomatized**. This increment is manuscript internal.

**Exact next entry:** First instantiate the genuine `W_T` logarithmic positional Fourier phase into **these same literal physical frozen words**, checking original label/multiplicity dictionary and source-specific geometric smoothness; prove absolute continuous Fourier L1, Fubini and quantitative common H with growing m(N). Separately identify actual complete physical PP atoms and `rho_T`, global squarefree mask, nonzero shifted arithmetic moment, complete modulus/totient mass and product=T exception; causal whole boxes, all HB, empty Gamma and high-rank/enhanced remain internal. P3.6 overall **YELLOW**.

## P3.6 SOURCE_ONLY successor — original slot-ID phase under ACTUAL frozen assignment (2026-11-07 UTC)

**Recovery and version:** Confirmed independent P3 branch HEAD `38b9afb528e3f9125ff0638096355d2477c19a8c`; read predecessor finite three-mode source and handoff, fixed `ActualFrozenSelectedPairAssignment.lean` and `ActualFrozenSelectedPairSlots.lean`, original physical `slotLog`, Fourier inversion module, external boundary, and pinned manuscript `9731290e8f53cffda44129906cde6a965eaa869b` (§4 F, body PP 256–278). No AGENTS found in root / docs / packet ancestry.

**Actual mathematical increment:** Previous three-mode finite tensor did not establish that the original geometric logarithmic Fourier CHARACTER really separates through frozen slots. The new `P3ActualFrozenOriginalSlotPhase.lean` does this for the existing genuine `actualFrozenSelectedPairAssignment` (computed once from endpoint upper values). It defines the full positive-2π inverse character on the original `Fin n` slot IDs, proves elementary finite exponential/product splitting and independence from coordinates outside each frozen group, and uses the already proved `actualFrozenSelectedPairAssignment_fibres` to identify the factors with the *literal three physical lists of tagged original slots*. It finally specializes to the existing original `slotLog U values`. Repeated prime VALUES are permitted: only original slot IDs are required to be unique and exhaustive. In particular, no positional Fourier multiplier is transported through a label permutation.

**Checks:** Independent Python exact Fraction phase-addition and physical-word permutation regression: **2600 cases, 15600 exact/numeric assertions**, 200 empty-original-vector cases, 1490 cases with repeated prime values; zero failures. Lexical delimiter scan balanced, forbidden proof escapes 0. Six declared #checks are registered, not executed. GitHub source blob and commit will be read back after the write; this record does not claim Lean elaboration or kernel validation.

**Important boundary:** The source is only the exact per-character phase separation, NOT its identification with pinned Mathlib `𝐞` character (sign and Euclidean pairing), not true Fourier inversion of original W_T, not a finite/continuous Fourier admission for W_T, nor the connection from tagged original slots to untagged physical prime gamma tuples, the concrete rho_T physical PP atoms, actual arithmetic discrepancy, product=T, causal, all HB, empty Gamma or high-rank/enhanced. These remain INTERNAL. `EXTERNAL_INPUTS.json` remains unchanged (M record only, no new axioms). No Lean/Lake/CI/kernel, Codex or heavy producer run. No green node; P3.6 YELLOW; this strictly scoped source candidate BLUE only.

**Next entrance:** Match the positive inverse character to Mathlib's actual Fourier pairing and construct the original-slot-ID-to-three ordered prime-tuple dictionary without assuming positional permutation symmetry. Then combine the real original W_T Fourier integrand with finite-mode tensor; quantify common H for growing m(N). Independently identify Q_T/rho_T for every actual PP atom and pay its arithmetic errors.

**GitHub verification of this successor (2026-11-07 UTC):** Initial proof/handoff commit `babe1831e5037f7cff55df7654508c987bf76766` [skip ci] successfully moved the isolated task branch from `38b9afb528e3f9125ff0638096355d2477c19a8c`; subsequent source-only namespace repair `86b480256f2afa8bb49c018d62c1ff0d32e51e03` [skip ci] opened the existing `P3AffineTransitionJets` Point chart API (no theorem statement altered). Final proof file Git blob `0dd4b783d8600767bae04798a8ef5c66b3ed7797` and audit-only VERIFY blob `095fdc65cb097ccf0e7799d99cf65e470fc6912d` were fetched back from the actual branch; 6 #check registrations remain UNEXECUTED. Independent finite checks were 2600 cases / 15600 assertions; Lean/Lake/kernel/CI NOT RUN. Next: Mathlib Fourier 𝐞 pairing identification, then tagged-slot-to-physical-gamma multipliers. No new green or unconditional PP claim.

## P3.6 SOURCE_ONLY successor — pinned Mathlib positive inverse character (2026-11-07 UTC)

**Verified baseline:** `f2c5595ae4e99dbf7d4e8db98f7e3c0dc55100ea`, branch `chatgpt/p3-internal-original-w-20261105`. Previous proof `P3ActualFrozenOriginalSlotPhase.lean`, previous `P3ActualFrozenComplexThreeModes.lean`, `P3FourierActualInversion.lean`, task REPORT/REGISTRY/EXTERNAL_INPUTS, fixed paper §4 (F), and pinned Mathlib sources were read. Root and nested AGENTS searches returned NOT_FOUND. No unrelated paused branch or excluded full87 work is involved.

**New genuine internal source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualFrozenMathlibInverseCharacter.lean` (125 lines), exact Git blob `3bc0945c670874055cdd2a29e94007912c7dd7c1`. The pinned Mathlib source at `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` defines `Real.fourierChar_apply` as `exp(2*pi*I*t)`; `Real.fourierInv_eq` has a positive inner-product phase, while `Real.fourier_eq` has a negative phase. This packet proves five candidate statements: (i) the summed literal original-slot `2*pi` phase equals that exact character exponent on ANY finite set of slot IDs; (ii) the full original numbered-slot phase is the literal Mathlib positive inverse character; (iii) each real physical frozen ID word has the corresponding exact character; (iv) the three actual endpoint-frozen words multiply to the full inverse character under prior slot-ID Nodup+coverage; (v) the same identity at the genuine physical `slotLog U values` chart. Repeated physical values do not identify or reorder different slot IDs. Empty slots and d=0 are covered algebraically. This repairs the previously explicitly open Fourier-convention bridge WITHOUT assuming the desired Fourier separation of W_T.

**Manuscript target and scope:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F). This is a literal inverse CHARACTER bridge only. It does **not** identify Euclidean `⟪eta,x⟫` with the coordinate dot product in a compiled declaration, does not construct an ORIGINAL prime-value/slot-ID tuple dictionary, does not establish that real W_T has the required analytic Fourier class, and does not pay any physical modulus error. Q/rho are not changed.

**Checks actually done:** Pinned Mathlib `Real.fourierChar_apply`, Fourier forward/inverse phase definitions were read. Independent Python exact Fraction dot-sum and complex phase regression passed 1040/1040 finite cases for d=0..12; 80 empty-slot cases, 424 repeated-coordinate-value cases, and 907 wrong-sign controls that distinguish the forward character. Source escape-token scan 0; delimiter scan balanced; five new #check references registered, NOT EXECUTED. These do not establish Lean elaboration, kernel proof, W_T admissibility or arithmetic PP.

**NOT RUN:** Lean, Lake, CI, kernel replay, full transitive proof audit, Codex, heavy producer. This entire new module remains SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED. No green status. The only external restricted medium estimate (M) remains **REGISTER ONLY** in `EXTERNAL_INPUTS.json`, unchanged Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; no substitute external result or proof assumption is introduced.

**Next genuine entry:** Identify the pinned EuclideanSpace scalar pairing with the actual coordinate `originalSlotDot` and establish a provenance-preserving map from three ACTUAL physical ID words to the untagged prime-tuple boxes and the existing `physicalComplexLabelGamma`. Then compose the true W_T Fourier representation, continuous L1/Fubini, uniform H and growing m(N), and separately the full same-rho actual PP atom compiler, shifted mixed moments and product=T payment. No statement of P3.6 closure is made. The atomic [skip ci] commit SHA is to be recovered from the branch HEAD, since this handoff file cannot contain its own future commit ID.

## P3.6 SOURCE_ONLY successor — pinned Euclidean original-slot pairing (2026-11-07 UTC)

**Verified recovery and baseline.** Actual task-branch HEAD before edits was `321bac63b6c6853c736e403662796135d3394361`, branch `chatgpt/p3-internal-original-w-20261105`. The existing unique REPORT, REGISTRY, EXTERNAL_INPUTS and previous `P3ActualFrozenMathlibInverseCharacter.lean`, original phase and real Fourier sources were read. Root/docs/packet `AGENTS.md` returned NOT_FOUND; no private file was assumed. Manuscript remains pinned to `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F) and `paper/source/manuscript-body.tex` prime-products. No changes to manuscript/master.

**New internal mathematics.** Source `P3ActualFrozenEuclideanPairing.lean` (source commit `19f40e41ef09643d3201a123440176044b9f1d0c`, slot namespace repair commit `eb35c1aba6da5e0f91dbf26496883a2c542db069`; final Git blob `abc304c4dccbc22bcf715cf57cc60eda2697de47`) composes the REAL pinned `EuclideanSpace.inner_toLp_toLp` with the prior exact original-numbered-slot dot product and Mathlib positive inverse additive character. The genuine inner pairing `⟪toLp 2 eta, toLp 2 z⟫_ℝ` equals `Σ_i eta_i*z_i` (Mathlib's reverse-order real dotProduct is reconciled by commutativity). The candidate then factors that same inverse character along all three ACTUAL endpoint-frozen original slot-ID words, and specializes to original `slotLog U values`. Original slot IDs remain distinct and exhaustive; repeated prime values are allowed. No synthetic separability assumption, new axiom or physical rho rewrite.

**Four candidate declarations:** `originalSlotDot_eq_euclidean_inner`, `originalSlotCharacter_eq_euclidean_inverse`, `actual_frozen_euclidean_inverse_character`, `actual_frozen_slotLog_euclidean_inverse`. This discharges only the former coordinate-vs-Euclidean **source-level algebraic pairing gap**, with original `Fin n` and no additional analytic/discrepancy assumptions. It is **not** a tagged-slot-to-untagged physical prime tuple/gamma dictionary, a proof that the original real `W_T` has uniform Fourier inversion, an arithmetic estimate, or PP closure.

**Checks / limitations.** The exact pinned Mathlib source `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1:Mathlib/Analysis/InnerProductSpace/PiL2.lean` lines 215–219 was inspected, including the literal `EuclideanSpace.inner_toLp_toLp` statement. Independent deterministic integer pairing and three-word partition regression checked **1210/1210** cases (dimensions 0–9, 121 empty-dimensional instances and 484 repeated-coordinate instances); zero failures. This is a finite algebra check **not** a Lean or Fourier proof. Source-only forbidden proof tokens: **0**; lexical delimiters balanced. Four #check targets were registered in `VERIFY.lean` but **not executed**. Proof remains susceptible to elaboration/coercion/simp/API issues.

**NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. Status remains BLUE only for this narrowly scoped source candidate; P3.6 overall YELLOW. The sole outside medium estimate (M) remains exactly record-only in unchanged `EXTERNAL_INPUTS.json`, blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; not axiomatized or reimplemented. No changes to source production, dependency pins, PRs, dashboard, paused branches, or excluded full87 nodes.

**Next real internal entrance.** Prove a provenance-preserving reindexing from the THREE literal `Fin n` physical ID words to `List ℕ` prime slot boxes/complex normalized `physicalComplexLabelGamma`: positional `eta_i` must travel with their original IDs even across duplicate fine labels. Only then connect actual `W_T` Fourier integrand to the existing finite complex three-mode tensor. Independently prove full admissible W family ContDiff/integrated uniform D, continuous Fourier L1/Fubini/common H and growing m(N), actual physical Q_T/rho_T complete modulus moment and exact product T. Causal/whole-box, full HB, empty Gamma, high-rank/enhanced and same-rho complete PP remain internal. No new GREEN.

## P3.6 SOURCE_ONLY successor — original-ID to actual ordered prime-tuple Fourier mode (2026-11-07 UTC)

**Verified baseline:** `dc792e5f5528e10e153c5ed5f72f68e16eaeceff`, on sole P3 branch `chatgpt/p3-internal-original-w-20261105`; prior `P3ActualFrozenEuclideanPairing.lean`, `P3ActualFrozenOriginalSlotPhase.lean`, `P3ActualFrozenComplexThreeModes.lean`, unique REPORT/REGISTRY/EXTERNAL_INPUTS, pinned manuscript completion §4 (F), and actual frozen selection APIs were read. Root and ancestor AGENTS files were absent (GitHub NOT_FOUND). No other task's paused branch was touched.

**GitHub confirmed source commit:** `6254b816e1b7c173487343f190a7b74504810c7c` ([skip ci]); new source `P3ActualFrozenTaggedPrimeModes.lean`, 174 lines, Git blob `9d6ce0521f5da6dbf5643574f8af12c14a03b946`. `VERIFY.lean` now holds eight **not executed** audit targets, blob `23879c22e330341df77591cec2f4868a838ceb28`. The GitHub branch update used an expected-head, non-forced fast forward; source and VERIFY were read back and matched those exact blobs. These are not compiled proof certificates.

**Actual mathematics:** Retain ORIGINAL `Fin n` ID `i` at each ordered physical prime slot, with phase `2π eta_i log(p/U_i)` (imaginary exponent). `positionalPhaseSum` recursively zips the frozen ordered ID word and its ordered prime tuple; `positionalGroupMode` returns ZERO for mismatched lengths so no silent end-truncation is possible. On a realized tuple `ids.map values`, a nonduplicated ID word gives equality with the prior true `physicalWordCharacter` (including empty words and repeated prime **values**). Each scalar phase has zero real part and each finite positional mode has norm at most one, independent of Fourier frequency sign or log positivity assumptions; the same bound holds for each of the three literal frozen output ID words. Finally `actual_frozen_original_prime_mode_factors` composes this **constructed** positional multiplier with `actualFrozenSelectedPairSlots_perm`, the existing ID-word three-way inverse-character theorem and the same `slotLog`, yielding an actual three-group mode factorization for *realized original prime assignments*. This does not equate a product-only scalar with a position-sensitive weight and does not quotient repeated labels.

**Finite independent regression actually run:** deterministic Python mathematical tests on dimensions 0..12: **1560/1560** full-versus-three-realized-complex-character identities and individual mode modulus checks; **3606** deliberately mismatched-length cases correctly assigned zero; **1136** cases had repeated prime values. The computation used genuine real `log(p/U_i)` and `exp(2π i •)` with tolerance 5e-12, not a Lean evaluator. An additional 1500 exact rational additive-phase partition cases were checked (including 3175 unequal-length guards). Zero failures. GitHub source escape-token scan **0**; lexical bracket stack **balanced**.

**Unproved / exact boundary:** This new finite source does NOT prove that the original actual PP atom compiler maps all ordered prime tuples into `actualPrimeSlotBox B (ids.map label)` with the necessary original label/multiplicity dictionary. Therefore it does not yet feed the tagged multipliers into the no-ID `physicalComplexLabelGamma` for every actual original source. No real uniform original `W_T` continuous Fourier inversion/L1/Fubini/H, growing `m(N)`, or full same-`rho_T` modulus mass/shifted moment/product=T payment is claimed. `EXTERNAL_INPUTS.json` remains exact blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: (M) REGISTERED ONLY, not implemented or made an axiom. P3.6 remains YELLOW. The eight new declarations are BLUE only as *SOURCE_ONLY/UNCOMPILED/KERNEL_UNVERIFIED*; no new GREEN.

**Not run:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, heavy producer. Pinned Mathlib elaboration risks remain for the purely imaginary `Complex.norm_exp` rewrite, list `Nodup` destructuring and source-to-physical word coercions. No production, manuscript, dependency, dashboard, other branch, PR or excluded full-87 change.

**Next exact entry:** Establish the *non-circular* source label/slot-ID prime-box dictionary for all original PP atoms, including the strict sorted source, repeated label factorial and actual frozen word, and then instantiate the existing `physicalComplexLabelGamma` bound with these literal `positionalGroupMode` multipliers. Independently prove genuine uniform `W_T` Fourier admission and all same-`rho_T` complete arithmetic payments (nonzero shifts, full modulus mass, `b=T`, causal/HB/empty Gamma/high rank).

## P3.6 SOURCE_ONLY successor — literal original-ID prime BOX to physical label-gamma fibre (2026-11-07 UTC)

**Recovery:** Confirmed isolated branch HEAD `5964d60498b165c7b65b2dce1795cc424a239e6c` (without concurrent ref change immediately before write), read actual previous REPORT/REGISTRY/EXTERNAL_INPUTS, `P3ActualFrozenTaggedPrimeModes.lean`, `P3ActualFrozenComplexGroupGamma.lean`, actual frozen allocator source, original prime-box definition and the pinned completion note. AGENTS root was NOT_FOUND, as in previous handoff. Paper pin is `9731290e8f53cffda44129906cde6a965eaa869b`, completion note §§3 (T) and 4 (F). Fixed Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**Genuine internal increment:** New `P3ActualFrozenTaggedPrimeBox.lean` (153 lines, Git blob `de060bcf1b5028e842cb4c85a147beb951acfaad`) handles the **entire physical ordered prime box** rather than only one realized tuple. For any original ID word `ids`, original label map `label` and literal label source sets B, prove the whole set equality `actualPrimeSlotBox (B ∘ label) ids = actualPrimeSlotBox B (ids.map label)`. On each genuinely admissible original prime assignment, the realized ordered tuple lies in the exact label box. Applying the actual `actualFrozenSelectedPairSlots` (on original Fin n IDs, NOT on labels) supplies all three real ordered prime-tuple box memberships and equality of their combined complete integer product with the unfrozen source. Applying the original frozen permutation to `label` preserves the exact original repeated-label multiset. No position-dependent Fourier multiplier is permuted.

The exact original-ID fibre sum of the constructed `positionalGroupMode` is proved equal to the old `physicalComplexLabelGamma` on `ids.map label`, with the original declared block factorial. Using the old half-open-label gamma bound removes an extra boundedness hypothesis on this specific constructed Fourier mode; the **original block-word permutation** is deliberately kept explicit, not falsely derived for every actual PP atom. No external theorem is used.

**Checks:** New source forbidden proof escape scan **0**, lexical delimiters **BALANCED**. Independent JS exact finite support/product/label-multiset regression **1000/1000** (101 empty ID words, 566 repeated prime-value cases, 59685 explicitly enumerated tuple-box members), zero failures; partitions were generic permutations, so this does **not** test the actual frozen allocator implementation. Seven `#check` targets recorded in VERIFY, **NOT EXECUTED**. No Lean/Lake/CI/kernel replay, heavy producer, Codex or full transitive axiom audit; all results SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED, **NO NEW GREEN**.

**External boundary:** (M) remains **record-only** in unchanged `EXTERNAL_INPUTS.json` (blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`). Neither (M) nor any new classical analytic input was implemented, axiomatized or assumed as a target-equivalent field. No changes to the manuscript, production sources, other task branches, excluded full-87 node, toolchain, PR or CI.

**Remaining exact entrance:** Obtain the real complete PP atom compiler's original IDs, label membership, repeated-label run-length blocks, and whole-source dictionary **without** asserting the last permutation as a circular premise; then specialize the physical complex gamma and finite three-mode tensor for each actual family. Uniform W_T mixed derivatives/Fourier L1/H with m(N), complete physical Q_T/rho_T, nonzero shift, product=T, causal/all HB/empty Gamma/high-rank remain INTERNAL and UNPROVED. P3.6 overall YELLOW.

**Atomic source commit:** to be recovered from GitHub ref after the fast-forward tree write; next line of this unique handoff is filled with the actual commit ID.

**Confirmed GitHub atomic proof commit:** `caf250cc5c95ef821900877cec1c101d79332228` ([skip ci]); verified exact source blob `de060bcf1b5028e842cb4c85a147beb951acfaad`, VERIFY blob `12546d9d56323c3384102fdee32c223d378c3304`, REGISTRY blob before provenance update `4a26dcb2cabf6833a25db4f5d8a00e7835c4edee`, and REPORT blob before provenance update `b0d61a9c954c377ebe5c3584e4c5d98c763d4c5b`. Source branch comparison: ahead 1, behind 0, exactly source/VERIFY/REGISTRY/REPORT changed. The following provenance-only commit records these exact readbacks, not additional proof.

## P3.6 SOURCE_ONLY successor — noninjective endpoint allocator label naturality (2026-11-07)

**Baseline actually read:** `74879c21075027b4d3aaa5e231f1bacee9094a24` on `chatgpt/p3-internal-original-w-20261105`. Read the actual source of `ActualFrozenSelectedPairSlots`, `actualTwoCapacityGreedy_map`, original sorted run-length `ActualPrimeFineWordMultiplicity`, previous ID prime box and mode, current REPORT, REGISTRY, EXTERNAL_INPUTS and pinned manuscript completion §3 (T), §4 (F). Checked AGENTS at root, ancestors, task folder and ImbalancedChen: NOT_FOUND. Pinned paper `9731290e8f53cffda44129906cde6a965eaa869b`; fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New mathematical candidates:** `P3ActualFrozenTaggedLabelCompiler.lean` proves the actual selected-pair allocator COMMUTES with arbitrary ID-to-label mapping, including noninjective maps, with pulled-back upper endpoints and both greedy/repair cases. It does not wrongly permute positional multipliers. A genuine sorted original fine-label source now COMPUTES run-length `blocks` via `actualPrimeFineLabelBlocksOfWord` and proves the three actual ID-tagged group positional gamma one-bounds through that naturality. In this restricted sorted source, the old required `hword` and `hpair` are DERIVED, not supplied by a new hypothesis. The original repeated-label factorial is preserved by the imported `splitBlocks` and `physicalComplexLabelGamma` APIs.

**Exact domain:** input ID list of length at least three with a given Fin-3 front; potentially repeated fine labels, original label word weakly descending; physical upper endpoints exactly `actualPrimeFineLabelIntegerUpper N τ`, N≥1, τ≥0. Fourier modes retain original ID-specific frequencies and order. No claim that all PP atoms (marked, HB, high rank, enhanced) satisfy these data; no source-to-actual-rho dictionary or arithmetic discrepancy is paid.

**Checks and restrictions:** candidate SOURCE_ONLY with unexecuted three #check entries. Syntactic forbidden-token scan of proof body 0, rough delimiter scan balanced. No Lean, Lake, CI, kernel replay, axiom closure audit, Codex, producer, or toolchain changes. New proof requires future elaboration check, especially `simp` through greedy map and `hlabelMap` rewrite. Prior EXTERNAL_INPUTS unchanged, (M) REGISTERED ONLY, NOT IMPLEMENTED, no new axiom. P3.6 YELLOW / local source candidate BLUE only. Source Git blob `475b2ecbf2d93c238480d922b0591b0ccbde9f55`; proof commit recorded by the actual GitHub commit response.

**Next actual entry:** Connect each full PP atom compiler's original ID word and ordered label memberships to the tagged sorted-domain lemma, or separately construct honest marked/HB dictionaries where sortedness does not hold. Only then assemble all physical gamma atom families. Independently remain: W_T uniform continuous Fourier L1/Fubini/H for growing m(N), true physical Q_T/rho_T, exact coprime mean, nonzero shift and product=T payments, causal/whole box, empty Gamma, high rank and enhanced branches.

**Confirmed atomic proof commit and independent readback:** `f6187736221fa7bfa7a6a9208333a662ba4d245e` ([skip ci]), branch `chatgpt/p3-internal-original-w-20261105`; verified proof Git blob `475b2ecbf2d93c238480d922b0591b0ccbde9f55`, VERIFY blob `5856648a39a969503f681ffdd03d39843b689f91`; source compare ahead 1 / behind 0 and only the four task files changed. Independent deterministic STRUCTURAL regression (not the pinned Lean implementation): 2400 map-naturality cases (2304 with repeated labels, 328 capacity-selected, 2072 repair, 342 three-slot), 1000 sorted run-length/factorial group cases (960 with an empty group); **0 failures**. No Lean, Lake, CI or kernel acceptance, no new GREEN. The following provenance-only [skip ci] commit records the exact source commit.


## P3.6 SOURCE_ONLY successor — canonical actual unsorted-ID physical gamma (2026-11-07)

**Recovered baseline:** 14542f8c39bb8189558124855008575351b3d34a on chatgpt/p3-internal-original-w-20261105. Read prior actual proof P3ActualFrozenTaggedLabelCompiler, TaggedPrimeBox/Modes, complex group gamma, sorted source, true run-length compiler, current unique REPORT/REGISTRY/EXTERNAL_INPUTS and pinned completion §3 (T), §4 (F). Root AGENTS.md returned NOT_FOUND; no constraints inferred.

**Confirmed source commit:** 8c138e64ba0709899ab42d97015fd15b93848193 ([skip ci]); genuine 149-line new Lean candidate docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualFrozenCanonicalUnsortedGamma.lean, Git blob 1fede22f106822d597df8c9ac9ee0df6337c1284. VERIFY blob bade816990d1171467bef771d9177919c02df8b9 has seven additional unexecuted #check targets. Source and VERIFY read back at the actual pushed branch HEAD. Fixed manuscript 9731290e8f53cffda44129906cde6a965eaa869b, fixed Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**New mathematical argument, not merely another permutation interface.** A physical original-ID label word may be unsorted. Construct canonicalFineBlocks by sorting ONLY that finite label word and then computing the existing run-length block dictionary. Prove word permutation and pairwise distinct labels; prove that the original actualPrimeFineWordMultiplicity is invariant under this permutation (via exact occurrence-count identities). Consequently the resulting factorial equals precisely the original product of per-label occurrence factorials, not total slots factorial. The physical ordered prime tuple and its ID-indexed Fourier multiplier are NEVER sorted or permuted. The old genuine-ID fibre and gamma bound then apply to any source label order. On the literal actualFrozenSelectedPairSlots output, all three groups have locally exactly normalized positional gamma coefficients bounded by one, without a weakly-descending-word hypothesis. Empty words and repeated labels are included.

**Domain and explicit missing bridge.** This is for any explicit Fin n original ID word and given original fine-label map, N≥1, τ≥0, and existing literal selected-pair upper-endpoint allocator. It is not an assertion that every actual marked/HB/high-rank/enhanced PP atom already supplies these IDs and values. Nor does it establish the combined original M_0 M_1 M_2 / M_all restoration scalar for all such atoms; that requires the real compiler dictionary and is still internal. No Fourier L1, genuine T/m(N)-uniform smooth W_T, physical Q_T/rho_T, exact coprime mean, full modulus arithmetic error or product=T exception is paid.

**Independent checks:** deterministic finite arithmetic-model regression 1800/1800 arbitrary label words (1123 genuinely unsorted, 1118 with duplicate labels, 215 empty), 26454 exact enumerated full-product fibre cardinality comparisons with true per-label factorial; zero failures. These tests did NOT evaluate Lean definitions. Source forbidden proof-escape scan 0; delimiter balance PASS. Readback proof blob and VERIFY were identical to the created blobs. **NOT RUN:** Lean, Lake, CI, kernel replay, full axiom audit, Codex, heavy producer. Candidate status BLUE only, overall P3.6 YELLOW; no new GREEN.

**External boundary:** unchanged EXTERNAL_INPUTS.json Git blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab, (M) REGISTER ONLY / NOT IMPLEMENTED / no new axioms. Manuscript, production files, other task branches, excluded full87, CI, dependencies, PR and external progress board untouched.

**Next precise internal entrance:** From the true original marked/HB/other PP compiler, extract literal ID/label membership, exact full source occurrence dictionary and original M_all, then prove the three computed canonical group M_j match the genuine split counts and pay the restoring factorial ratio once. Only after that connect the true W_T Fourier integrals and full same-rho signed physical modulus ledger, including nonzero shifts and product=T. Do not equate label permutation with positional Fourier-weight invariance.

## P3.6 SOURCE_ONLY successor — actual unsorted-ID canonical frozen split payment (2026-11-07)

**Recovered real baseline:** `55297cc5c4a9fe4f5f88946844b33b706cf3e3dd` on `chatgpt/p3-internal-original-w-20261105`. Current source fast-forward commit: `11b0487971e8fee205fd5833b7eb783965470ec8` (`[skip ci]`); GitHub readback proof blob `55b5f3fdc3c3d796792a30e3d03d5d21d8f78ab0` and VERIFY blob `4e3b0abdc4575b46ed02782960845f1224187a7e`, unchanged external registry blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. Pinned paper: `9731290e8f53cffda44129906cde6a965eaa869b`, completion note §3 (T), §4 (F) and manuscript-body; pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**Substantive new source:** `P3ActualCanonicalFrozenSplitPayment.lean` (200 lines, five named proof-body candidates). The previous packet computed a canonical unsorted original-block factorial but did **not** derive how one source's actual frozen three-way split restores the original full scalar. This packet derives every canonical-block multiplicity as the sum of ACTUAL frozen occurrence counts, via genuine selected-pair allocator permutation and block-word permutation (without a caller `hword` premise). For each of three physical groups the computed split-block word permutes the actual output label word, including labels absent or split between groups. Consequently the genuine factorial correction (M_0 M_1 M_2 / M_{all}) is in [0,1] without replacing (M_{all}) by the total number of slots factorial, with every (M_j) computed from that ORIGINAL unsorted word and true frozen per-label counts.

The final theorem uses `selected_pair_slots_map` with potentially noninjective original-ID-to-label mapping to attach these very split blocks to the three ACTUAL ID-ordered physical group `physicalComplexLabelGamma` factors. Their positional Fourier modes remain attached to the original `Fin n` IDs; NO positional multiplier is transported through a label permutation. Each factor is one-bounded for the explicit input ID word, (N\ge1,\tau\ge0).

**Verification completed:** Fresh branch HEAD checked immediately before first write and checked again before nonforced expected-head update. New source and VERIFY read back from GitHub with the exact blobs recorded above. Lexical delimiter stack balanced, forbidden proof-escape tokens 0. An independent deterministic JS mathematical regression exhaustively enumerated 597,871 words/three-way group assignments (lengths 0–6, three-label alphabet): 0 failures; 164,683 empty-group, 597,645 repeated-label and 574,974 label-split instances (categories overlap). It checks exact per-label count conservation and factorial correction, **not** the fixed greedy allocator's operational code or Lean proofs. Five new `#check` declarations are registered in VERIFY but **NOT EXECUTED**.

**NOT RUN:** Lean, Lake, CI, kernel replay, complete transitive axiom audit, Codex, heavy producer. Elaboration risk includes `List.Perm.count_eq`, implicit `let` expansion, `fin_cases` and simplification through allocator label naturality. No new GREEN; P3.6 overall YELLOW. No change to pinned source files, manuscript, dependencies, production proofs, other automation branches, external dashboard, PR, excluded dynamic full87 node or toolchain.

**Trust boundary:** Existing (M) remains **RECORD ONLY**, unchanged EXTERNAL_INPUTS blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. No outside research input was implemented, no new axiom, no target-equivalent field and no discrepancy or complete-product-T payment has been assumed.

**Exact next entrance:** Read the genuine marked/HB/enhanced PP atom compiler and extract each atom's original ID/fine-label ordered source word and scalar, not an invented `hword`. Then connect these exact split blocks and ID-aware modes to the finite three-group same-rho tensor. The actual physical (W_T) uniform mixed-derivative/Fourier inversion/L1/Fubini/H with growing m(N), full (ho_T)/physical modulus, nonzero-shift moment, complete-product (n=T) and causal/all HB/empty Gamma/high-rank remain INTERNAL and OPEN.
## P3.6 SOURCE_ONLY successor — actual tagged unsorted finite modes at same rho (2026-11-07)

**Recovered and checked HEAD:** \`e2b11b115adbe13520fd85961516fc774c388cee\` on \`chatgpt/p3-internal-original-w-20261105\`. Latest actual canonical-split source, three-complex-mode tensor, tagged positional prime modes, noninjective label naturality, and unique REPORT/REGISTRY/EXTERNAL_INPUTS were read. No AGENTS file was present at root, ImbalancedChen, the source-only ancestor or packet path. Manuscript remains pinned to \`9731290e8f53cffda44129906cde6a965eaa869b\`, completion note §3 (T), §4 (F), Mathlib unchanged at \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`.

**Actual proof commit:** \`878b800876bc58fecaeff783d007fcffccfa6a2c\` (\`[skip ci]\`). New 204-line \`P3ActualTaggedUnsortedSameRho.lean\`; Git blob \`34b02cf18147dcf9ba7723905bf2132b8d345f27\`. VERIFY readback blob \`21df5bbef6ce59249d25ee2236aa28c6627e0e04\` registers three new UNEXECUTED \`#check\` targets. GitHub commit was fast-forwarded and independently compared to baseline (ahead=1, behind=0; only proof and VERIFY files).

**New internal connection:** The exact unsorted label word, canonical full repeated-label factorial, three split-group factorials and three ID-tagged positional modes all come from ONE explicit original Fin-ID word and the actual frozen allocator. The \`selected_pair_slots_map\` lemma transports possibly NONINJECTIVE ID labels to the physical label boxes without ever reordering the positional multipliers. The existing finite three-group complex tensor is thereby specialized to a COMMON finite Fourier mode index and then to \`fineKernel(T,q,full product)\` with the SAME integer \`rho(q)\` multiplying both exact congruence count and coprime mean. No target PP estimate is assumed. The mode-by-mode source budget additionally establishes the computed \`M0*M1*M2/M_all ∈ [0,1]\` and each of the three genuine physical gamma coefficient norms ≤1 for N≥1 and tau≥0. It does not bound the SUM of mode amplitudes or pay any Fourier L1.

**Independent checks and limits:** 520/520 deterministic complex-arithmetic cases using actual real logs, two finite modes and modulus-wise count-minus-exact-totient-mean, including 258 empty-group cases, 485 repeated fine-label words and 1,040 negative-rho summands; 0 failures. The independent model enumerates arbitrary finite partitions rather than executing the frozen allocator or Lean. Source proof-escape token scan 0; delimiter stack balanced. **NOT RUN:** Lean, Lake, CI, kernel replay, complete transitive axiom audit, Codex or producer. These are source candidates only, no new green node.

**Next real missing bridge:** The input is still one EXPLICIT ID word. Need derive its ID/label/raw marked scalar and physical modulus/rho from the true PP atom compilers; no global marked/HB/high-rank/enhanced coverage is claimed. Need actual original ordered-prime W_T source equivalence, continuous Fourier admissibility and m(N)-uniform L1/Fubini/H; then the full signed modulus mass, nonzero shifts and n=T exception. Complete HB, empty Gamma mother and causal whole-box remain INTERNAL. External (M) solely registered, unchanged \`EXTERNAL_INPUTS.json\` blob \`8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab\`, not implemented; no new axiom or target-equivalent premise. No other task files, excluded 87-domain source, production, manuscript, CI, dependencies, PR or external board modified.

## P3.6 SOURCE_ONLY successor — marked residual exact-product separation (2026-11-07)

**Actual recovered baseline:** `ecc97e763a36f73951d74ea61f1c3a6e73840714` on `chatgpt/p3-internal-original-w-20261105`, after reading the existing last proof, REPORT, REGISTRY, unchanged EXTERNAL_INPUTS, applicable source constraints and pinned completion note. **Proof commit:** `66d0a59a8148ae6c828d4fb5be452c4477375456` (`[skip ci]`), new `P3ActualMarkedResidualExactProduct.lean` (167 lines), Git blob `228e0c64cb5dd987addbd4d0f6170b7df0ef305c`. VERIFY Git blob `351bd9abd565c2f41952f48215a705fdb54cce00` registers four checks but did NOT execute them.

**Mathematical contribution:** The original manuscript's raw MARKED source divides ONLY by the residual fine-label occurrence factorial, while its marked multiplicity remains in the external signed scalar. We preserved this distinction for the actual three endpoint-frozen physical residual boxes and the original-ID positional Fourier weights. The external marked factor `r` enters the literal Möbius `mu(r * complete residual product)`, NOT the residual factorial. The kernel uses the identical signed integer `rho(q)` for count minus exact coprime mean. We proved candidate finite source separation into complete-product `n=T` and `n≠T` fibres with no `tau(0)`. When every physical `q` is coprime to `T`, the `n=T` part factors **AFTER** the complete signed modulus sum as
`mu(r*T) * (sum_q rho(q)*(1-1/phi(q))) * (the original complex weighted exact-T mass)`.
The signed modulus factor may be large. This is an exact identity, NOT its necessary smallness payment.

**Checks:** source/VERIFY read back exactly; balanced lexical delimiters, 0 forbidden escape tokens. Independently implemented deterministic complex arithmetic on 4,200 finite signed-modulus source cases: 0 failures; 11,841 exact-T tuple instances, 2,953 zero-Möbius cases, 2,664 cases with a negative rho, 468 empty modulus sets, 281 empty sources. This does NOT execute Lean or the actual frozen greedy allocator or source compiler. **NOT RUN:** Lean, Lake, CI, kernel replay, complete transitive axiom audit, Codex, heavy producer. No GREEN and no full P3.6 closure.

**Still internal and open:** the real marked/HB PP compiler has not been proven to return the displayed residual original ID/label words, marked factor r, restoring scalar c and physical Q_T/rho_T. Exceptional mass is not estimated; off-product nonzero-shift mixed moments and full modulus, real original W_T continuous Fourier L1/Fubini/common H and growing m(N), causal whole-box/all HB/empty Gamma/high-rank/enhanced remain unclosed. The excluded full-87 dynamic-parent node was neither touched nor used.

**Trust boundary:** original manuscript pin `9731290e8f53cffda44129906cde6a965eaa869b`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; existing (M) remains registration only. The untouched `EXTERNAL_INPUTS.json` Git blob is `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. No surrogate axiom, target-equivalent premise, manuscript/toolchain/production/PR/CI change.

**Exact next entrance:** prove the marked/HB compiler's actual residual-word IDs, multiplicities, outside marked factor and signed scalar, and identify literal physical Q_T and rho_T. Bind these to the existing finite same-rho three-gamma tensor and separately pay exact-T and nonzero-shift arithmetic after the true continuous W_T Fourier budget.


## Successor SOURCE_ONLY correctness repair — marked FULL product versus residual product (2026-11-07)

**Recovered exact remote baseline:** `41e3627784da695a56e4c513982fc1db53a10bc7`, branch `chatgpt/p3-internal-original-w-20261105`. This round reread the previous marked proof, REPORT, REGISTRY, EXTERNAL_INPUTS, actual weighted fine-kernel source, and fixed manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §1's literal `E_q` and §3 (T), plus the manuscript-body statement. Root/docs/packet AGENTS paths were queried and were NOT_FOUND. No newer master/alternate paper statement was substituted.

**Real source correction:** `a4a51709c252b3ce6f6993ce8a75701aeb446da8` (`[skip ci]`), corrected file `P3ActualMarkedResidualExactProduct.lean`, readback blob `6cacd8c2efc2877cfeb1a546e19678942065ab78`. **Actual VERIFY update:** `51e51cac678540fffcec6da26fe13ff1cda513fe`, `VERIFY.lean` blob `c14044b0569a3484a94e4f810ceddc79dc5409c2`. Both are GitHub-created commits; this packet does NOT run VERIFY, Lean, Lake, kernel or CI.

**Mathematical ERROR FOUND and withdrawn:** the previous `66d0a59` packet tested `fineKernel T q n` and filtered `n=T`, although `r` was the OUTSIDE marked prime product and `n` was only the residual word's product. The manuscript §1 defines the exact congruence and exact coprime mean on the product of **ALL ORIGINAL PRIMES**. If `r` represents the outside marked product, this is `r*n`. The old RHS also used `mu(r*T)` on an incorrectly selected residual `n=T` fibre. THESE EARLIER CLAIMS ARE RETRACTED in the marked scope, not counted as previously closed. For example r=2,n=3,T=6,q=5 has a genuine full-product=T event: the correct kernel is `mu(6)*(1-1/phi(5))=3/4`, whereas the old residual test would give `-1/4` and the old exceptional filter would miss the tuple.

**Corrected exact finite source:**
- `markedResidualKernel r T q n = mu(r*n) * fineKernel T q (r*n)`. The fineKernel remains the literal congruence indicator minus `1_{(r*n,q)=1}/phi(q)`, with no loss of the coprime test. Marked r is OUTSIDE `M_res`, not outside the complete physical product.
- Split on `r*residualProduct=T` versus `r*residualProduct≠T` using the SAME signed integer `rho(q)` and the same physical Q. The exact full-product fibre now factors as `mu(T) * (sum_(q in Q) rho(q)*(1-1/phi(q))) * (original complex exact-full-product weighted mass)` under the original explicit `forall q in Q, Coprime T q`. The factor is signed and is NOT bounded by the identity.
- NEW `marked_exact_fibre_empty_of_not_dvd` and `marked_exact_product_zero_of_not_dvd` show that if the **outside** factor r does not divide the target T, the exact full-product fibre is empty, and its signed-rho contribution is exactly zero, irrespective of Fourier weights. No asymptotic bound is assumed.
- The actual three frozen residual prime boxes still use original ID-position Fourier modes and the **residual-only** factorial `M_res`. The source's residualProduct is distinguished from the genuine full product `r*residualProduct` in every physical count/mean and exact-fibre test.

**Independent check and limits:** deterministic exhaustive elementary arithmetic model: 55,296 tuples over r,n in 1..12, T in 1..32, q in 1..12, including 852 actual exact-full-product instances, 41,616 instances with r not dividing T (no exact exception), and 974 cases in which the old residual congruence disagreed with the full-product congruence in the r*n!=T,n=T control. All corrected exact-coprime expressions passed; no floating discrepancy in the exact-case checks. This is an independent math sanity check, NOT an execution of the Lean definitions. Source-delimiter scan passed; proof escape tokens absent; VERIFY contains six checks in this marked scope but NONE were executed. **NOT RUN:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, heavy producer. The corrected statements are SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED, not GREEN.

**Fixed boundaries:** No changes to `EXTERNAL_INPUTS.json` (Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`): restricted medium (M) remains RECORD_ONLY with manuscript version, exact hypotheses and future call site; no outside theorem, new axiom, sorry, unsafe proof shortcut or invented result. No manuscript, toolchain, production source, other task branch, full87 dynamic parent, CI, PR or board edit.

**Exact next step:** First prove that the **REAL** marked/HB compiler maps each concrete residual occurrence list and marked factor r to the full physical integer product r*n, including all original labels, external marked scalar, repetition factorial and physical Q_T/rho_T. Do not infer marked source coverage from this conditional finite identity. Next bind it to the already-existing ID-tagged finite same-rho three-gamma source; then separately prove the complete product=T source mass and the off-full-product nonzero-shift mixed divisor moment (shift `T-r*n`, not `T-n`), with exact coprime mean. Independently prove original W_T all-source ContDiff/mixed-L1, Fourier normalization, Fubini, common H and growing-m uniformity. Causal/whole-box, all HB words, empty Gamma mothers, high-rank/enhanced, and full P3.6 assembly remain open. P3.6 is YELLOW; this corrected local finite source is BLUE only.


## Successor SOURCE_ONLY correction — sorted original W source FULL marked product (2026-11-07)

**Verified exact recovery:** branch `chatgpt/p3-internal-original-w-20261105`, baseline `33051b4a42c5c1dbc918f4af694932048031a5c0`. GitHub source+VERIFY commit: `b6915c529ab232df4e52085e8700d1c1681fb65f` (`[skip ci]`); proof Git blob `1dbb76dea830dfe614c3ead7a70e8450596cc3a1`, VERIFY blob `1d9609be7cacfe42198012c68efac575436e4498`. Source and VERIFY were read back. The external record remains the exact earlier blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`.

**Concrete mathematical error located and repaired:** In `P3ActualWeightedFineSameRho.lean`, the sorted, arbitrary-position-weight `weightedSortedPP` already multiplied by `mu(r*ps.prod)`, but tested `fineKernel T q ps.prod`. Its fibre formula and exact exception likewise tested the residual product alone. For a genuine outside marked integer `r` this violates the pinned manuscript §1 exact complete-product count and coprime mean, and §3 (T) marked/residual distinction. The prior marked scope of these three declarations is **withdrawn**. The corrected source tests `fineKernel T q (r*ps.prod)` everywhere and filters `r*n=T` for the exact fibre. For example r=2, n=3, T=6, q=5 gives correct factor 3/4 rather than the old -1/4.

**New source-only proof body:** `weightedSortedPP_split_full_product` separates the actual `actualPrimeFineLabelSortedTuples` source into `r*ps.prod=T` and `r*ps.prod≠T`, with the unchanged original arbitrary positional W, Möbius factor, signed rho(q), physical Q and exact coprime mean. No permutation invariance, extra source class, asymptotic bound or distribution assumption is introduced. The revised `weightedSortedPP_exact_product` requires only the explicit original `forall q∈Q, Coprime T q` to factor the literal exception. The marked integer r remains outside the residual label factorial, not outside the physical integer product.

**Manuscript pin and scope:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; `paper/source/modules/distribution-prime-product-completion-20261010.txt` §1 (E_q), §3 (T), §4 (F), and `paper/source/manuscript-body.tex`. No master update, no toolchain change. This sorted original-weight source is an explicit actual prime-tuple family; it is NOT yet a proven enumeration of all marked/HB/high-rank/enhanced PP atom compilers.

**Verification actually performed:** GitHub baseline and write lease, readback of source and VERIFY exact blobs; lexical delimiter check PASS, forbidden proof escape tokens 0. Deterministic independent finite JS regression **2,880/2,880** over outside r=0..7, target T=1..30, q=1..12, signed rho, original differently weighted ordered tuples, full Möbius and exact totient mean; original tuple sum equals product fibre sum and the exact/off split. It found **1,008 old-vs-correct counterexamples**, **189 nonzero exact-fibre cases**, and **1,920 negative-rho cases**. This is NOT execution of Lean definitions and is NOT kernel acceptance.

**NOT RUN:** Lean, Lake, CI, kernel replay, full dependency/axiom audit, Codex or heavy producer. Four source `#check` lines are registered only. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED, no new GREEN node. `EXTERNAL_INPUTS.json` still records medium (M) only, with accurate manuscript hypothesis/version/call-site; no implementation, replacement axiom or new research premise.

**Next concrete entry:** obtain the REAL PP marked/HB compiler's outside product r, residual original IDs and fine labels, signed restoring c, multiplicity normalization, and actual physical Q_T/rho_T, rather than inferring them from these free parameters. Then bind the corrected arbitrary W sorted source and the ID-tagged finite three-Γ tensor without sorting positional weights. Separately pay the **complete** exception r*n=T, nonzero-shift T-r*n arithmetic mass, and the original W_T Fourier L1/Fubini/common H uniformly for growing m(N). Causal/whole-box, all HB, empty Gamma mothers, higher rank/enhanced and full PP remain internal and open. **P3.6 stays YELLOW.**

## P3.6 SOURCE_ONLY successor — actual marked full-product OFF shifted-divisor bridge (2026-11-07 UTC)

**Recovery:** Exact branch HEAD `366e135d54a210e0100a9349fd56e867d65c60d1`. Read unique REPORT/REGISTRY/EXTERNAL_INPUTS, corrected `P3ActualWeightedFineSameRho.lean` and `P3ActualMarkedResidualExactProduct.lean`, prior real finite shifted-divisor module, the pinned completion manuscript note §1/§3/§4 and manuscript-body, and checked root/ancestor AGENTS (not found). No competing writer observed at immediate head checks.

**Actual proof-body commit:** `863857460b063d7af7f9e12ba3fcb00e25ecd40a` ([skip ci]); new `P3ActualMarkedOffShiftDivisors.lean` (126 lines, Git blob `c1dd502c0002a62ae8da068b06ca449818c3f39e`). `VERIFY.lean` updated with five unexecuted targets, blob `c75c020e9b5ea4ad1e416c3de67bedef856944b1`. Both blobs were read back from GitHub at the committed SHA. Pinned manuscript `9731290e8f53cffda44129906cde6a965eaa869b` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged.

**Genuine manuscript-internal increment:** Earlier corrected marked exact-product arithmetic separated `r*n=T`, but still lacked the actual marked nonzero-shift divisor bridge. This source now derives `markedShiftAbs r T n = |T-r*n|` as a natural absolute value and proves it is NONZERO exactly off `r*n=T`. On that domain it combines the existing fixed-library signed-integer divisibility lemma with `fineKernel_literal` and the previously constructed shift-divisor theorem, yielding the literal congruence test supported on physical divisors of `|T-r*n|`, MINUS the exact original coprime mean. The complete Möbius `mu(r*n)` remains on the complex marked kernel, not `mu(n)`. The final source theorem instantiates this at every tuple of the actual strictly sorted original fine-label prime source, preserving arbitrary position-dependent real W, external c, original physical Q and the SAME signed rho(q). It never applies a divisor estimate to zero and never sorts W.

**Independent checks actually performed:** Static forbidden escape token scan 0, lexical delimiters balanced. Deterministic finite arithmetic regression: **74250/74250** exact complete-product congruence versus signed-shift divisor tests for r=0..8, n=0..21, T=0..24, q=0..14; 20115 old residual-only mismatch controls. Independent full signed-rho/position-weighted prime-tuple double-sum regression: **5320/5320** cases, 142560 tuple terms, q=0 extension tested, zero failures. These are mathematical finite models, NOT Lean or actual atom compiler execution.

**Boundary:** NOT RUN Lean, Lake, CI, kernel replay, full axiom audit, Codex or heavy producer. All five candidates are SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED; possible Fin-1 product/cast API elaboration remains. No analytic shifted moment, product=T mass payment, true all-source marked/HB compiler dictionary, physical Q_T/rho_T identification, uniform original W_T continuous Fourier L1/H, causal/whole-box, all HB, empty Gamma mother, high-rank/enhanced or final PP assembly. No GREEN node. The external (M) record stays unchanged (Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`), REGISTER ONLY, not implemented or an axiom. Manuscript, production source, toolchain, PR, other tasks, excluded full87 and CI untouched.

**Next concrete entrance:** From the actual marked/HB source compiler obtain the original residual occurrence IDs, marks r, restoring scalar c, label factorial and original physical Q_T/rho_T; prove its source really has full integer r*n. Instantiate this nonzero-shift lemma and independently pay the complete off-shift mixed moment and exact r*n=T mass. Do not promote finite reindexing into full PP.



## Successor SOURCE_ONLY increment — even original prime source has no exact full-product T (2026-11-07 UTC)

**Recovery:** branch `chatgpt/p3-internal-original-w-20261105`; checked predecessor HEAD `8cee2ff3d1aef881f2eecc239e6ddc89ade1583b`, manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b` (`paper/source/modules/distribution-prime-product-completion-20261010.txt` §§1,3(T),4(F), plus `paper/source/manuscript-body.tex`). Root/ancestor packet AGENTS.md requests returned NOT_FOUND. Original sorted fine-prime selector, actual membership `p.Prime ∧ ¬p∣N`, corrected marked off-shift source, unique REPORT/REGISTRY/EXTERNAL_INPUTS were read. No competing task-branch writer was observed on initial and pre-write HEAD checks.

**Actual source-only proof-body commit:** `94401c3d401c7ce2fd302d9ec7bbf1c4e9b77333` ([skip ci]), `P3ActualEvenOriginalPrimeException.lean` 137 lines, Git blob `1f55928fb533377a475b6167ecdde398f0b59e36`; `VERIFY.lean` Git blob `ef8043e838e13ce9f0782eee0fb84ffce2afad5a`, five new unexecuted checks. Both were reread at the committed task branch.

**Nontrivial internal mathematics:** The *actual* `actualPrimeFineLabelFinset N τ i` membership (in `ImbalancedChen/ActualPrimeDisjointLabelProducts.lean`) excludes prime factors of N, not just primes below a guessed cutoff. Therefore for EVEN N, p=2 is excluded from every genuine fine box; pinned Mathlib `Nat.Prime.odd_of_ne_two` yields every original prime odd. Via the existing real `actualPrimeSlotBox_forall`, **every** genuine `actualPrimeFineLabelSortedTuples N τ blocks` tuple has odd residual product, including empty lists. When the outside marked factor r is ODD and target T is EVEN, the full physical product r*ps.prod is odd and cannot equal T. The exact full-product=T sorted-original-PRIME fibre is therefore empty and its **whole signed rho** and arbitrary tuple-dependent W contribution is exactly zero. This is a real restricted exception payment, not an asymptotic estimate, and it uses NO upper bound on `rho`.

Composing this parity result with the corrected `weightedSortedPP_split_full_product` and the previous `weightedSortedPP_off_divisors` removes the exceptional term in this restricted source: the full signed complete-modulus expression is its nonzero physical shift `|T-r*ps.prod|` divisor expression **minus the still-exact coprime mean**. Physical q, signed rho, external real c, full Möbius r*ps.prod and original ordered positional W are retained. No sorting of W or auxiliary modulus substitution occurs.

**Crucial scope limit:** `Even N`, `Even T` and `Odd r` are explicit hypotheses. The actual original Goldbach target is even, but *compiler-level* identification of N=T, proof that EVERY actual marked outside product r is odd, and completeness across all marked/HB/high-rank/enhanced PP atoms remain INTERNAL and UNPROVEN. HB integer factor carriers are NOT automatically prime tuples; parity cancellation in a complete HB sum cannot be assumed from the prime-only statement. The original literal zero-product exception in general arithmetic sources, all mixed shifted moments, complete physical Q_T/rho_T, true Fourier L1/H, causal/whole-box and final PP assembly remain open. No relative-Theta claim was introduced.

**Checks actually completed:** Pinned Mathlib  `Mathlib/Data/Nat/Prime/Basic.lean` at `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` was inspected and contains `Nat.Prime.odd_of_ne_two` (line 103). Static forbidden proof token scan 0; lexical delimiter balance PASS; proof and VERIFY blobs reread. Independently, deterministic Python finite original-prime-box parity model (even N=2..100, primes ≤29 with p∤N, sorted distinct tuples of length 0..3, odd r=1..21, even T=2..50) passed **1,326,875/1,326,875** full-product nonexception checks over 4,825 original tuples; a separate 71,820/71,820 physical nonzero congruence/divisor checks passed. These independent models are NOT Lean elaboration, the literal repository selector runtime, or kernel proof. Five `#check` lines registered, NOT executed.

**NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy numerical producer. All declarations remain SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED; **no green nodes**. Neither original manuscript nor production files, other task branch, excluded full87 node, toolchain/lock, PR, CI or board was modified.

**External input:** `EXTERNAL_INPUTS.json` remains at Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`, medium (M) RECORD_ONLY, source/statement/conditions/pin/call site registered but NOT implemented and NOT used as an axiom. No new external assumptions, sorry/admit or alternative axioms.

**Next exact entrance:** (1) From the actual marked-atom compiler show each outside marked prime factor belongs to the original excluded-prime universe, so for even N the real marked product r is odd. (2) Link N=T and the actual residual occurrence list, fine labels, restoring scalar and physical Q_T/rho_T; then apply this no-exception result ONLY to the honest prime tuple source, not unconstrained HB expansions. (3) Separately identify and bound any HB **integer source** complete-product=T fibre and nonzero T-rn mixed moment; preserve exact coprime mean. (4) Complete original W_T uniform Fourier L1/H and all remaining causal/whole-box, HB, empty-Gamma, high-rank/enhanced PP obligations. P3.6 remains YELLOW.


## P3.6 SOURCE_ONLY successor — full-target exception vanishes for nonempty ORIGINAL prime words, no parity premise (2026-11-07 UTC)

**Actual recovery and branch:** `chatgpt/p3-internal-original-w-20261105` at verified starting HEAD `ed82b18a118f9e409298f080807eb620ea024454`, not historical `de582e6`. Read prior unique REPORT/REGISTRY/EXTERNAL_INPUTS, `P3ActualEvenOriginalPrimeException.lean`, corrected original weighted and off-shift modules, fixed production `ActualPrimeDisjointLabelProducts.lean` and `ActualPrimeFineLabelSortedSelector.lean`, and pinned manuscript `chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b` `paper/source/modules/distribution-prime-product-completion-20261010.txt` §§1,3(T),4(F) plus `paper/source/manuscript-body.tex`. Root, docs, source-only and local AGENTS paths were queried and returned NOT_FOUND; no hidden constraints inferred. Branch head checked before every write; no competing writer observed at these checks.

**Real new Lean proof candidate:** `P3ActualNonemptyOriginalPrimeException.lean`, **133 lines**, Git blob `3058b8cea49f272cae31a50056d6cd56bc7490a3`, source commit `947bc4c568ca911a9fa576c45e515b70c1ec6873` (`[skip ci]`). Audit `VERIFY.lean` commit `5d136baf3b6df2f68e1a5e4c3a963233b831864c`, blob `4bb394fc154346ec149e61479ff8bfdae8ebb3e6`; registry commit `99e1e904a626aab54a6b3598dcde97414eaaad05`, blob `1f1a23aff64f25934e1ff57ff66c09127d2420f0`.

**Actual mathematical increment:** The LITERAL original fine prime alphabet has membership `p.Prime ∧ ¬p∣N ∧ [original half-open real endpoints]`. For any actual *nonempty* sorted residual original-prime tuple `ps=p::rest`, `p∤N`. If a complete marked physical product were `r * ps.prod = N` (the actual PP target T=N), elementary integer divisibility would give `p∣N`, a contradiction. This does **not** require N even, r odd, r coprime to N, positive r, or a replacement prime alphabet; it strengthens the prior parity-specific restricted source. The lemma `actual_sorted_exact_full_product_only_empty` isolates the ONLY remaining exceptional fibre on the honest original fine-prime carrier: **`ps=[]`**. With the real original residual word nonempty, `actual_sorted_nonempty_word_exact_fibre_empty` derives the entire empty exceptional finset and `weightedSortedPP_target_N_nonempty_word_off_divisors` combines existing corrected complete-product splitting and literal nonzero-shift divisor rewriting. The same signed integer rho(q), original physical Q/q, full `mu(r*ps.prod)`, exact coprime mean, scalar c, and arbitrary positional geometric W are retained. This is a genuine exact source-specific algebraic payment of the zero exceptional contribution, **not an off-shift analytic moment estimate**. No fabricated compiler field is introduced.

**Important boundary:** If the residual word is EMPTY then `ps.prod=1`, and `r=N` can yield a genuine complete-product=N exception. The new proof explicitly retains that case. It is NOT the same as a unit HB log slot, or an automatic payment of empty Gamma mother words. No blanket conclusion is made about whether each real marked/HB atom has a nonempty original prime residual word; that compiler-level provenance, original IDs/labels, marked r, scalar c, physical Q_T/rho_T and high-rank/enhanced cases are still open. Do not transfer this prime-only contradiction through arbitrary integer HB factorizations without a separate exact source identity.

**Checks really done:** Prewrite GitHub head lease, immediate source readback at commit, source word forbidden proof-token scan zero and simple delimiter balance pass, `VERIFY.lean` imports occur before `#check` (5 new targets registered, NOT run). Independent Python finite original prime-alphabet regression (N=2..100, p≤29 with p∤N, descending distinct prime tuples length 0..3, outside r=0..30) passed **46,035/46,035**. Exactly **29 empty-word exact-product** cases confirmed the necessary exception boundary; this uses a finite test alphabet rather than executing Lean or the real geometry selector. External inputs JSON verified unchanged, blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`.

**NOT RUN:** Lean, Lake, CI, kernel replay, full dependency/axiom audit, Codex, or heavy numerical producer. All new declarations are SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED with potential `simp`/list/Finset elaboration risks. **No green nodes.** (M) is RECORD ONLY with exact version/hypotheses/call site; not implemented, used as axiom, or promoted. No change to pinned manuscript, production source, other task branch, excluded full87 dynamic-parent node, toolchain/lock, CI, PR or board.

**Exact next entry:** Inspect TRUE marked/HB PP atom compiler to prove, rather than assume, which residual original fine-prime words have positive length, and whether its outside r and restored scalar reproduce literal full integer r*n at the same actual physical rho_T. Isolate and PAY the zero-residual case separately. Review the new five Lean candidates statically against the pinned source (no compilation by this line); then obtain true W_T uniform Fourier L1/Fubini/H and full nonzero-shift divisor mixed-moment estimate plus all causal, HB, empty Gamma, high-rank/enhanced PP sources. P3.6 stays YELLOW.


## Successor P3.6 SOURCE_ONLY — exact original empty-word exceptional fibre (2026-11-07 UTC)

**Recovery:** Verified branch HEAD 9d7b7a4702b860713d3b7ec7115999e28ee45489 before editing. Read prior unique REPORT, REGISTRY, EXTERNAL_INPUTS; actual sorted-prime and fine-label source, existing corrected marked full-product, shifted-divisor and nonempty-word proof files. Root, docs, source-only and packet AGENTS files were queried but NOT_FOUND. Also read the pinned manuscript UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, prime-product completion §§3(T),4(F) lines 123–171 and manuscript-body PP. Inspected existing P5 marked witness source as context only: that is not evidence of a complete P3.6 marked/HB PP atom compiler. No automatic migration to current master.

**Real proof candidate saved:** P3ActualOriginalEmptyWordExactPayment.lean, source commit 7e20cbff162fc19756305426fc0fddb8d06f0cef [skip ci], 134 lines, Git blob 86e82f36491f823643c2bd8bcf085415f81d29d8. VERIFY.lean blob 843dbf2362a1fa31f06d4065208c90d05a31bccb imports the new source before five new unexecuted #check declarations.

**Mathematical increment:** The prior nonempty-original-word result established that an actual original prime p does not divide the target N and therefore r*product=N is impossible for nonempty original prime tuple. The omitted boundary is now classified and its exact signed contribution computed. The literal original sorted-prime selector is a singleton {[]} for an empty expanded label word, even when nonempty block metadata contains only zero multiplicities. Thus the complete-product=N source fibre equals {[]} exactly when expanded word=[] and external r=N, and equals ∅ otherwise. Its exact physical discrepancy scalar, assuming the genuine physical moduli q are all coprime to N, is:
if (expanded_word=[] AND r=N) then (c*mu(N)*W []) * sum_{q in Q} rho(q)*(1-1/phi(q)) else 0.
This preserves the original signed rho, q, full Möbius factor, arbitrary positional W, external restoring c, and exact coprime mean. The fifth lemma joins this exact scalar to the existing nonzero |N-r*product| divisor formula as ONE finite equality for ALL actual original sorted-prime words at T=N. It is source-only finite arithmetic, NOT a smallness bound, not a proof that an actual compiler generates an empty word, not an empty Gamma mother word payment, and not a claim about arbitrary integer HB sources.

**Checks actually performed:** GitHub source and VERIFY blobs read back; proof escape tokens zero; lexical delimiters balanced; five #check declarations registered after imports but NOT run. Independent finite prime-alphabet support regression 25,632/25,632 with 14 genuine empty-tuple target matches and zero nonempty violations. Separate deterministic signed-rho, arbitrary c, positional W, exact coprime mean and off-divisor regression 2,200/2,200 full assemblies over 30,789 tuple occurrences, nine exact-product occurrences and zero nonempty diagonal violations. An initial Python check failed because sympy.mobius does not accept argument zero; corrected independent model uses the arithmetic-function convention mu(0)=0 and passed. These finite models are neither the literal Lean selector computation nor Lean elaboration or kernel acceptance.

**NOT RUN:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex and heavy producers. There is still possible simp/Finset/ring elaboration risk and NO GREEN. External research estimate (M) remains REGISTER ONLY, EXTERNAL_INPUTS blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab unchanged; no new axioms or equivalent-to-target premises. Manuscript, toolchain/lock, production files, other tasks, excluded full87, PR and external board untouched.

**Next actual entrance:** Identify the real marked/HB PP atom compiler, extract its exact residual occurrence IDs, label word, marked product r and restoring scalar c, and bind true physical Q_T and rho_T. Classify whether an empty residual word is really emitted by each source and quantitatively pay any surviving unit-residual singleton. Separately prove nonzero full-shift signed modulus mixed-moment budget, original W_T continuous Fourier L1/Fubini/common H uniform for growing m(N), and causal, all-HB, empty-Gamma-mother, high-rank/enhanced source coverage. P3.6 remains YELLOW.

## Successor SOURCE_ONLY increment — two literal original prime words eliminate the complete-product diagonal (2026-11-08 UTC)

- **Verified recovery baseline:** `4d2ec676ec57f7216f527ba710c442547c6f393f`, branch `chatgpt/p3-internal-original-w-20261105`.
- **Actual proof commit:** `20cfa56d801aa7aa98bc0b9615cb26943f424e61` (`[skip ci]`), 147 lines in `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualOriginalMarkedPrimeNoDiagonal.lean`, Git blob `a8ee2a1761430cd1e1a030f6dad23ad756383d80`.
- **Manuscript pinned:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`: completion note §1 original fine-prime exclusion, §3 (T) marked/residual normalization, §4 (F) full complete-product exception. Mathlib lock unchanged.

### Genuine manuscript-internal mathematical increment

The earlier original-prime residual-only packet left a possible singleton when the residual slot word was empty and the unconstrained external marked integer was `r=N`. This packet **does not** silently identify an arbitrary `r` with a real marked prime product. Instead, it constructs a **standalone** Lean candidate importing the existing production `ImbalancedChen.ActualPrimeFineLabelSortedSelector` directly. The marked and residual prime lists must EACH be members of the literal `actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)`, at possibly different `τm,τr`. Both alphabets exclude every prime dividing the same physical target `N`.

From genuine slot-box membership, a nonempty list has a prime `p ∤ N`. Yet if `marked.prod * residual.prod=N` then every prime in either list divides `N`. Hence any nonempty combined slot word excludes the entire exceptional fibre. When both words are empty, their complete product is exactly 1. Therefore for **N≠1**, the full marked-prime × residual-prime source has **no** complete-product=N exceptional fibre. A final candidate specializes to the literal full-product Möbius weighted count-minus-exact-coprime-mean, after the complete finite **same signed physical `rho(q)`** modulus sum. No mass estimate, positivity, or Fourier amplitude bound is required for this exact ZERO fibre.

This genuinely strengthens the previous residual-only singleton classification **on the exact domain where the outside marked factor is itself a product of actual target-excluding original prime slots**. It is NOT a blanket conclusion about actual marked compiler output, arbitrary marked integer `r`, HB integer convolution atoms, an empty Gamma mother-word or the full original PP theorem. Physical `Q_T,rho_T` and external scalar `c` remain to be identified with the true compiler. In particular, we did not replace the user's excluded dynamic-parent source.

### Source and checks

Five candidate declarations: `original_prime_box_product_not_dvd`, `marked_residual_full_product_ne_target`, `marked_residual_target_fibre_empty_of_nonempty`, `marked_residual_target_fibre_empty_of_target_ne_one`, `marked_residual_same_rho_exact_diagonal_zero`. The literal kernel in the final declaration uses complete physical product in both congruence and exact coprime mean. The candidate uses no new axioms or placeholder proof premise.

- GitHub original branch HEAD checked immediately before proof commit, and proof file reread with Git blob `a8ee2a1761430cd1e1a030f6dad23ad756383d80`. Existing production `ActualPrimeFineLabelSortedSelector.lean` and its slot-box facts were read directly. Root/packet/ancestor `AGENTS.md` probes returned NOT_FOUND; no implicit constraints inferred.
- Independent finite JavaScript exhaustive sanity sweep: **20,808/20,808** products for target N=1..72, marked/residual words length up to 2 from small primes excluding p|N, with one correct both-empty N=1 boundary and no violations. Removing the exclusion has the counterexample N=6, marked=[2], residual=[3]. This did NOT execute the Lean definitions or a compiler.
- Static banned proof-escape token scan: 0; parenthesis depth balanced. `VERIFY.lean` records five checks but does not run them.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, numerical producer. No green status.
- **IMPORTANT SOURCE_ONLY packaging caveat:** many earlier source-only files import `ImbalancedChen.P3...` modules that are stored only under `docs/source-only`, not the production `ImbalancedChen/` path. Such imports will not resolve in a normal Lake build without future staging/mapping. This new proof file instead imports an existing production module. It remains UNCOMPILED and may have elaboration issues.
- `EXTERNAL_INPUTS.json` unchanged; medium estimate (M) remains REGISTER_ONLY_NOT_IMPLEMENTED_NOT_AXIOM. No upgrades or other workstreams touched.

### Exact next entrance

Read the actual marked/HB atom generator and supply a genuine compiler-to-literal-prime-box membership proof before applying the new zero diagonal to a marked source. The HB integer source and arbitrary external r do **not** inherit it. Then pay the nonzero complete shift mixed divisor moment, real physical Q_T/rho_T, the original W_T uniform Fourier L1/Fubini/H, and the remaining causal/whole-box, full HB, empty Gamma and enhanced branches independently.

## Successor SOURCE_ONLY — actual original U7 marked rank-3/rank-4 PP and the SAME physical off-shift (2026-11-08 UTC)

- Baseline verified `18f6a7b217968b8ca002ac0387c2f016ff2a3614`, branch `chatgpt/p3-internal-original-w-20261105`; actual proof/VERIFY GitHub commit `fb699d2f44688caa22f50a7f366e64753e9e79bb` (`[skip ci]`). Proof file `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU7PhysicalOffshift.lean` with Git blob `bd42621549978641aef0b0d9e8eb5585d7ff234a` and `VERIFY.lean` blob `1dd7800515430eb0d967e2bc885f885291ce9ee5` read back after writing. Existing source `ImbalancedChen/P5U7OriginalPhysicalPP.lean` blob `1974fbd5e23db9d212535e2c28e00ceec40b0089` and `P5U7OriginalArithmeticFamily.lean` blob `fa2eeea0c5c8f8212b2d9d6f179dbd9bbfc74d68` actually read; `P5zPositiveFamilyBudget.lean` blob `463662f184e9d4c16c2460716fb0b417b69eede3` supplies the already-existing exact finite Fubini.
- Fixed manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, completion note §1 absolute signed PP, §3(T) original labels and §4(F) complete-product exceptional term; main `manuscript-body.tex` restricted PP. No master drift.
- **Mathematical gain rather than a generic API:** The genuine `p5U7ArithmeticThree N` and `p5U7ArithmeticFour N` source membership proves the *complete* rank-3/4 prime product is strictly less than physical N. Therefore exact product=N filters are empty, N-product>0 always, and finite original marked rank-3 plus rank-4 signed PP discrepancy equals (both physical `physicalDivisorSum Q rho (N-product)` sums) minus (the sum of the two original marked source masses times `physicalDensitySum Q rho`) minus the **two exact coprime corrections**. The existing authentic marked-weighted `p5U7ArithmeticProductWeight` source equals the same expression by the original finite rank-preserving transport. ONE unchanged real signed `rho(q)`, ONE physical Q, no taking per-rank norms or changing the mean. Distinct rank labels and repeated terminal coordinates remain.
- **No false scope expansion:** This is one real P5U7 marked receiver family and an internal finite identity, NOT the general marked/HB atom compiler; no new claim of all-original W_T, full integer-HB exception payment, auxiliary-vs-physical level correspondence, actual all-source rho_T, Fourier/H with growing m, or quantitative signed-modulus saving. The upstream U7 source and the new file remain SOURCE_ONLY uncompiled; no PP theorem assumed as a premise. No new axioms or research inputs were introduced.
- **Checks:** Independent finite model over 73 target N values and signed physical moduli q=0,1,2,3,5,7,11,13: 16,464 weighted tuple/modulus terms, 1,609 rank-three and 449 rank-four tuple occurrences, 0 zero shifts, 0 direct discrepancy vs divisor-shift mismatches. The model uses small prime triples/quads satisfying broad original rank/order/product/gcd conditions; it does NOT evaluate literal Lean selectors. Prohibited proof tokens: 0. Parenthesis static scan: PASS. New import and six #check entries registered; not executed. GitHub proof and VERIFY blob readbacks succeeded.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. Zero green promoted. This file imports existing production-path `ImbalancedChen.P5U7OriginalPhysicalPP` instead of an absent staged P3 module, but that imported source is itself uncompiled, with elaboration risk.
- External `EXTERNAL_INPUTS.json` unchanged blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`, (M) REGISTER_ONLY / NOT IMPLEMENTED / NOT AXIOM. Excluded dynamic-parent full87, other tasks, production files, manuscript and toolchain unchanged.
- **Next exact entrance:** Locate and read the real general marked/HB PP atom compiler, with original residual occurrence IDs, labels, full marked factor r, restoring scalar c and actual physical Q_T/rho_T. Reuse the finite nonzero-shift result only where its genuine source conditions hold; independently pay remaining HB zero-diagonal, complete signed-modulus moving shift moment, W_T continuous Fourier L1/H/Fubini uniform with growing m, and causal/full-HB/empty Gamma/high-rank/enhanced obligations. P3.6 remains YELLOW.


## Successor P3.6 SOURCE_ONLY — actual U9 ordered marked source same-rho complete offshift (2026-11-08 UTC)

- **Verified recovery:** The actual branch `chatgpt/p3-internal-original-w-20261105` was at `86230f465b9fbc7ff94fa36aa7f6491db232d0bd` after the previous U7 proof; the old `de582e6` was NOT reused. Read the full existing REPORT, REGISTRY, EXTERNAL_INPUTS and actual U7 source. Root, `docs`, `docs/source-only`, `ImbalancedChen` and packet AGENTS probes found no file.
- **Actual Lean source:** `P3ActualU9PhysicalOffshift.lean`, 136 lines, Git blob `761e513b1ae49f41cc39c3f71dba63226729e2b0`; source commit `5683e6ba9be8b1bbf59d0ec9e069acd60bf65ffd` (`[skip ci]`).
- **Verification list:** `VERIFY.lean` blob `b7008ba8dea189aad8c7f7a60a7708a0c99c913c`, commit `791cd1957e25c3410d28c4057efc2d077b9bb42a`, registers nine unexecuted checks with import ahead of checks.
- **Registry:** source and check record commit `ddb3383d6fc262c3a5aaf6c16fad7327e45b8567`, blob `0b138c3f167ddbe1cb349ec91f92c4d8d7e67146`.
- **Fixed manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §1 physical E_q and exact coprime mean, §3 (T) labelled multiplicity, §4 (F) complete-product offshift; `paper/source/manuscript-body.tex` PP section. Mathlib pin unchanged.
- **Real dependency source:** `ImbalancedChen/CurrentChenP5U9OrderedBranches.lean` blob `4fe6309961627f855e0203e3bd73871ff82fa862`, `ImbalancedChen/CurrentChenP5U9OrderedPhysicalPP.lean` blob `ae6a6ef3ef9b4edeb19ca41510e830d9b8e1dbb2`, and `P5zPositiveFamilyBudget.lean` blob `463662f184e9d4c16c2460716fb0b417b69eede3`. All were read, rather than inferred from filenames.

### Genuine new manuscript-internal math

The **actual switched U9** marked source is the disjoint **labelled** union of three original order gates `q<p1`, `p1≤q<p2`, `p2≤q`. The fixed inverse permutations deliver three exact physical rank-3 coefficient functions, all using **one and the same** physical `Q` and signed real `rho`. Actual source membership gives **full physical product m<N**, hence `N-m>0`, even where product values repeat across different labels. This independently excludes `m=N` for the entire U9 switched source and every ordered branch, without replacing it by a generic atom.

Define for each actual branch j:

`A_j = ∑_(t∈S_j) physicalDivisorSum(Q,rho,N-product(t)) - Mass(S_j)*physicalDensitySum(Q,rho) - CoprimeCorrection(S_j,product,1,Q,rho).`

By exact original labelled finite Fubini and the verified-in-source `product<N` predicate (NOT by analytic PP), the candidate source derives:

`E_U9(N;Q,rho)=A_0+A_1+A_2 = PP3(weight_0,Q,rho)+PP3(weight_1,Q,rho)+PP3(weight_2,Q,rho).`

Both equalities preserve signed sum **before** absolute value, full physical product, all original multiplicities and the separate exact coprime corrections. Crucially `physicalDensitySum` alone is NOT the coprime mean. This adds the actual U9 triple-branch source to the earlier bounded U7 3/4-rank family; it is **not** a proof that either family exhausts the real marked/HB compiler. The integer sieve `rho_T` and actual physical `Q_T` have NOT been extracted, and a free real rho is not an identification of them.

### Checks and limits

- GitHub head lease checked before every write; no observed concurrent branch change. New source and VERIFY blobs reread; forbidden proof escape tokens **0** after removing comments; lexical delimiters balanced; imports precede #check; nine checks registered but **NOT executed**.
- Independent deterministic Python **finite algebra** regression: 101 targets N=8..408 step 4; 1,015 label occurrences, 12,180 signed weighted modulus terms, order-branch occurrences 174 / 543 / 298, 480 negative rho coefficients, and zero congruence-vs-full-shift-difference failures. Independent model uses broad U9-like ordering, `m<N`, centre-coprimality and root wall but does **not** execute the literal Lean source selector or compile Lean. A separate 35-target finite model retained 51 repeated physical-product label occurrences across order gates; no product-image deduplication. Neither model certifies elaboration, full analysis or kernel acceptance.
- **NOT RUN:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, heavyweight producer. Upstream U9 source itself says SOURCE_ONLY/UNCOMPILED. The candidate may still contain elaboration bugs and remains **BLUE LIMITED SCOPE**, not green; P3.6 stays **YELLOW**.
- `EXTERNAL_INPUTS.json` untouched: blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`, restricted medium (M) only REGISTERED / NOT IMPLEMENTED / NOT AN AXIOM. No substitute axiom, target-equivalent hypothesis, toolchain/lock change, old production module rewrite, manuscript/master update, full87 dynamic-parent change, other-workstream edit, CI trigger or PR.

### Next exact entrance

Find and read the genuine ALL marked/HB PP atom constructor and prove its residual occurrence IDs, fine labels, external marked product r and restoring c correspond to the original physical product with the actual **integer `rho_T`** and physical `Q_T`. Only then use U7/U9 as named subfamilies where the actual compiler certifies inclusion. Independently pay the HB integer complete-product=T exceptional fibre, the nonzero-shift complete signed-modulus mixed divisor moment, original `W_T` continuous Fourier L1/Fubini/H uniformly in growing m(N), causal/whole-box, all HB source words, empty Gamma mothers, high-rank/enhanced and final same-rho PP. No external (M) estimate is implemented here.


## Successor P3.6 SOURCE_ONLY — actual U8 sharp-K inclusive repeated-terminal prime source (2026-11-08 UTC)

- **Verified recovery and immutable baseline:** existing task branch `chatgpt/p3-internal-original-w-20261105` was `782d66459c31b794de1b9ab3c0b6651e41fc3354` (the previous U9 increment), not the obsolete de582e6 baseline. Read latest unique REPORT, REGISTRY, EXTERNAL_INPUTS, previous U9 proof and authentic fixed U8 arithmetic/physical source; queried root and ancestor AGENTS (not found). No competing head change was observed during these writes.
- **New genuinely original Lean candidate:** `P3ActualU8SharpKOffshift.lean` (207 lines), Git blob `fdf4f5085f6815e4480b9cdfccf74de9d9366f19`, source commit `459efabfe17f3afb0b65ddd3cb5c241a001a7d7f` ([skip ci]). It directly imports actual production-path `ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP`, not an absent staged P3 module. `VERIFY.lean` blob `e46023e7055088b906a9348ee6c0a8442b4d9b20`, commit `776f82b7a296b92a8c58b19d3ff2d615394aa51a`, has 13 new **registered but not run** checks. `REGISTRY.json` blob `9a352f22779c9820d2767343634535901c513de2`, commit `14bd7bc58d91b5356d8bb9d969013d5820d3bff4`.
- **Fixed original manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §§1,3(T),4(F), and `paper/source/manuscript-body.tex` §1. The original U8 exact source is `ImbalancedChen/CurrentChenUpsilon8SharpKArithmeticSource.lean` blob `86bac93f428db269db068839ae890ef17306ff6c`; its physical rank-three coefficient and diagonal facts are in `CurrentChenUpsilon8SharpKPhysicalPP.lean` blob `ec293754c86ec0712d4e420a648c79e6c5897027`. The genuine unit-prime alternative lives in `CurrentChenUpsilon8PrimeSource.lean` blob `3aa63be2fb6041af2ff31d3ef532fa07d1bb7419`; `P5zPositiveFamilyBudget.lean` blob `463662f184e9d4c16c2460716fb0b417b69eede3` supplies original exact labelled finite Fubini and exact coprime correction.

### Mathematical source gain and exact limits

Unlike the previously connected U7 and U9 sources, this literal U8 sharp-K prime-quotient source has the **inclusive** terminal-prime ordering `p₁<p₂≤q`; `q=p₂` is a real repeated-prime diagonal, not an insignificant tie to discard. The genuine `arithmeticTriples N` support gives the full physical product `p₁p₂q<N` and centre coprimality `Coprime (N-p₁p₂q) N`. Thus every prime-quotient triple has positive full shift, and its product=N fibre is empty. The new labelled partition `arithmeticTriples = strictTriples ∪ diagonalTriples` is *disjoint on actual tuples*, with all repeated original occurrences retained; finite congruence and exact-coprime masses each split over it.

After the COMPLETE original physical signed modulus sum, the result is
`PP3(physicalWeight N; N,Q,rho) = ∑_(t∈actual U8 triples) physicalDivisorSum(Q,rho,N-product t) - Mass(triples)*physicalDensitySum(Q,rho) - CoprimeCorrection(triples,product,1,Q,rho).`
The actual original product-fibre weight `productWeight N m` has the same equality; all multiplicities are retained by the already-existing `productWeight_sum`. The same equality is decomposed into the literal `p₂<q` plus `p₂=q` signed errors, **before absolute value**, using one and the same physical `Q,rho`. The diagonal has its own exact nonzero-shift divisor expression with its separate exact coprime correction. No division by a surrogate density, no `tau(0)`, no extra rho and no replacement arithmetic hypothesis.

**Crucial exclusion:** `currentChenUpsilon8 N` has an additional literal **unit quotient** `q=1` fibre, already split from the prime triples by the upstream `currentChenUpsilon8_eq_primeMass_add_units`. It is not proved small here and must NOT be counted as covered by the new prime-quotient offshift. The terminal prime `q` is not the physical sieve modulus (called Q/rho). The repeated-prime diagonal does NOT inherit a squarefree Möbius weight; these U8 positive coefficients cannot substitute for the HB integer family. Actual complete physical `Q_T` and INTEGER `rho_T`, all marked/HB atom compiler residual IDs, external marked r and restoring c remain unbound.

### Actual checks

- New source and VERIFY reread from GitHub, exact source blob SHA `fdf4f5085f6815e4480b9cdfccf74de9d9366f19`, exact VERIFY blob SHA `e46023e7055088b906a9348ee6c0a8442b4d9b20`. New source forbidden proof escape tokens **0** after comments; lexical delimiters balanced; 13 declared names occur in VERIFY after its import, **none executed**.
- Independent deterministic Python **exact-rational finite algebra** model on 69 targets N=1000..6000 step 73. It generated **3,678** admissible U8-like labelled prime triples with the real exponent/window/order/product/centre-coprimality conditions approximated for a small finite model: strict `p₂<q` **2,989**, equality `p₂=q` **689**. For seven physical moduli `Q={1,2,3,5,7,11,13}`, with signed positive and negative rho, it compared **25,746** complete-modulus tuple terms and found **0** mismatches between original congruence-minus-exact-coprime-mean and full nonzero-shift divisor-minus-density-minus-exact-coprime-correction. Example equality tuple: N=1000, (p₁,p₂,q)=(3,11,11), full product=363, shift=637. This is an independent arithmetic model; it did **not** execute the literal Lean selector, check elaboration, kernel proofs or PP logarithmic savings.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, numerical producer. Upstream U8 is itself marked SOURCE-WRITTEN/UNCOMPILED. No green promotion; new U8 scope is BLUE SOURCE_ONLY, P3.6 remains YELLOW.
- `EXTERNAL_INPUTS.json` unchanged Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: restricted medium (M) merely REGISTERED / NOT IMPLEMENTED / NOT AXIOM. No new axioms, circular proof premises, toolchain/lock upgrades, manual changes to manuscript, default/main branch, excluded dynamic-parent full87, other workstreams, PR or external status board.

### Exact next entrance

Locate the genuine *all-marked/HB PP atom compiler*, not simply a named U7/U8/U9 receiver source. Extract residual original occurrence IDs and fine labels, complete marked product r, restoring scalar c, original physical `Q_T` and integer `rho_T` at the real shared threshold. For U8 preserve its `q=1` unit fibre and repeated-prime equality `q=p₂`; pay their quantitative contribution where required rather than silently deleting either. Independently prove the signed full nonzero-shift HB divisor mixed moment and exact product=T HB exception, original `W_T` quantitative continuous Fourier L1/Fubini/common H uniform for growing m(N), causal/whole-box, all HB, empty Gamma mother, high-rank/enhanced and final same-rho PP. All are INTERNAL, not reclassified as external (M).

## Successor P3.6 SOURCE_ONLY — actual U8 q=1 unit-quotient family, strict physical offshift and same rho (2026-11-08 UTC)

- **Recovered the real branch, not the obsolete de582e6:** `chatgpt/p3-internal-original-w-20261105` at `773245c32ad85154635d0d6cb2a68ff37a262b93`. Read its prior handoff, registry, unchanged external-input register, original U8 physical proof, actual U8 unit quotient constructor, U9 quotient witness and the exact p5z finite signed Fubini. The fixed manuscript is `9731290e8f53cffda44129906cde6a965eaa869b`, with §1 signed absolute PP, §3(T) occurrence multiplicities and §4(F) physical complete-product shifts. No master version drift; relevant ancestor AGENTS probes found none.
- **New actual code and hash:** `P3ActualU8UnitQuotientOffshift.lean`, 132 lines, Git blob `fb07f0e938d35cd49de3bdad106f70a03ee6ccdd`, proof commit `229dd71af90838e54f9c7ad15aa88735e35e0f19` ([skip ci]). Same commit updated the single existing `VERIFY.lean` (blob `7b3b32141151bd2924e9bc0c75850e169da5526b`) with eight registered, **not executed** #checks. Neither source nor current production dependency is kernel-accepted.

### Exact mathematics gained

The original U8 producer has a disjoint literal q=1 QUOTIENT pair family `currentChenUpsilon8UnitFibres N`, omitted by the previous rank-three prime-quotient offshift. For each actual pair `p=(p1,p2)`, the raw filtered quotient membership gives `1 ∈ chenQuotientPrimeSource N (p1*p2)`. Real pair prime carriers ensure `0<p1*p2`, so the already-existing `currentChenUpsilon9_quotient_witness` gives **`p1*p2*1<N`**. Hence the full physical product `p1*p2` is below N, its shift `N-p1*p2` is positive, and its exact product=N fibre is empty. The unit QUOTIENT is not an empty HB/Gamma mother word, nor the physical sieve modulus, nor the repeated terminal prime `q=p2`.

The exact genuine pair-source physical error for ANY common `Q,rho` is
```
 E_unit = sum_(p in actual unit pairs) physicalDivisorSum(Q,rho,N-p1*p2)
        - Mass(actual unit pairs)*physicalDensitySum(Q,rho)
        - CoprimeCorrection(actual unit pairs,p1*p2,1,Q,rho).
```
The last correction is essential: it is the difference between exact coprime mean and total mass/phi, never silently zeroed. The new total U8 identity combines **existing physical rank-three PP** and this actual pair error **before absolute value**, with their distinct preserved corrections and one signed `rho`. All original pair labels are retained, not deduplicated by product. The source uses existing exact p5z finite Fubini and rank-three physical transport, not a target-equivalent hypothesis or new input.

**Exact limits:** This completes only the finite arithmetic U8 prime-quotient+unit-quotient pair separation, still not the general marked/HB atom source; the Q/rho arguments are free and do NOT identify physical `Q_T` or integer `rho_T`. The upstream card bound `#unit <= N^(2/3)` is an ordinary source-card bound, **not yet** a modulus-weighted PP error payment without a bound on the real `sum_{q in Q_T}|rho_T(q)|` and its exact mean. The HB integer exceptions and analytic nonzero-shift moments remain untouched. This source is SOURCE_ONLY and has not run Lean/Lake/CI/kernel.

### Reproducible independent checks, not Lean acceptance

- GitHub source and VERIFY readbacks matched those two exact blob SHAs; proof commit parent `773245c32ad85154635d0d6cb2a68ff37a262b93`, and changed exactly the new proof plus existing VERIFY. The head lease was checked again before the push. No competing write observed.
- Independent Python exact-rational sanity model: N=500..10000 stepping by 97 (98 targets), 64 targets with at least one model unit pair, **176** original-window admissible pair labels with distinct prime receiver and centre coprimality, seven positive physical q=1,2,3,5,7,11,13 with signed rho (positive and negative), **1,232** direct count/mean vs nonzero shifted divisor/density/correction term checks, **zero mismatches** and zero complete product>=N. The model uses the original exponent windows but DOES NOT evaluate the Lean definition or full sifted source predicate. The initial regression harness mistakenly subtracted `1` instead of `1/phi(q)` from the density, found a contradiction, corrected its **test formula** and reran successfully; this was a harness issue, not a proof to hide or a Lean pass.
- Forbidden proof-escape tokens in source code after comments: **0**. Delimiter scan passed, eight #checks registered after the new import. File hashes are Git blobs, not kernel certificates.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex or heavy numerical producer. Previous staged-only VERIFY imports remain not resolvable in a default Lake compilation without staging. No green promotion. `EXTERNAL_INPUTS.json` unchanged at blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; (M) **REGISTER_ONLY / NOT IMPLEMENTED / NOT AXIOM**. No toolchain, manuscript, full87 dynamic parent, other task, production code, master, PR, merge or forced ref modification.

### Concrete next entrance

The next internal gap is not another reformulation of the U8 finite identity. Use the real physical sieve constructor to bind `Q_T` and the **same integer** `rho_T`, then prove and pay a signed or absolute *modulus-weighted* bound for the U8 unit-pair branch (the existing `N^(2/3)` pair-count bound by itself does not do it). In parallel the genuine all-marked/HB PP atom compiler still needs occurrence IDs, fine labels, full marked product r, restoring c, causal whole-box, complete HB sources, empty Gamma mother words and high-rank/enhanced coverage. After binding them, pay HB product=T exceptional mass, nonzero-shift mixed divisor moments, original `W_T` continuous Fourier L1/Fubini/common H uniformly in growing m(N), strict endpoints and final absolute arbitrary-log PP. This packet stays YELLOW; U8 unit source is BLUE limited SOURCE_ONLY.

## Successor SOURCE_ONLY increment — genuine U8 unit physical modulus L1 (2026-11-08 UTC)

- **Actual checked baseline:** `e0e4d9a457fa8187c7c76f22bd103e2551efec4e`; no competing writer observed before this proof source write.
- **Proof commit:** `cacfd568914464fa495a275912af42c6f2a3b5a5` (`[skip ci]`). New source: `P3ActualU8UnitPhysicalNorm.lean`, 116 lines, exact Git blob `f7f4a47d03edba7b88ef1f07a97772069b813b7b`.
- **Unchanged fixed manuscript:** `9731290e8f53cffda44129906cde6a965eaa869b`, distribution completion §1 count/coprime mean and §4(F); pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- **Real imported source APIs:** `p5z_labelledDistributionError`, `p5z_labelledCongruenceMass`, `p5z_labelledCoprimeMass`, and existing actual `currentChenUpsilon8_unitFibres_card_le_power`. This is not a copied abstract surrogate family.

### Actual mathematical increment

For every **positive physical sieve modulus** q, both the exact labelled congruence count A_q and the exact coprime mean B_q/phi(q) lie in [0,#S], because every original unit-pair occurrence has indicator weight one and phi(q)>=1. Crucially, **|A_q-B_q/phi(q)| <= #S, not 2#S**. The source candidate `labelled_unit_signed_error_le_l1` proves by finite sum triangle and one unchanged signed rho:

```
|sum_(q in Q) rho(q) * (A_q - B_q/phi(q))|
   <= #S * sum_(q in Q) |rho(q)|.
```

The concrete `actual_u8_unit_error_le_physical_l1` then uses the ALREADY EXISTING actual unit-pair injection `#S_unit(N) <= N^(2/3)` to derive:

```
|E_U8_unit(N;Q,rho)| <= N^(2/3) * sum_(q in Q) |rho(q)|.
```

Both the original occurrence labels and exact coprime mean remain intact; q=1 as a **quotient** is not conflated with a physical sieve modulus 1 or an empty Gamma mother. This is a genuinely quantitative finite reduction, **not** a complete PP estimate. In particular, it does **not** prove the actual sieve rho_T has sufficiently small physical L1 norm. An O(N^alpha) norm with alpha<1/3 would give a power reserve, but this is a criterion to establish from the real coefficient, NOT an assumption already paid.

### Checks and limitations

- Independently modelled 147 targets N=11,13,...,303, 748 small actual-like unit-pair labels, 1,764 physical modulus discrepancy terms (785 negative-rho) over q=1..12: **zero mismatches** for the per-modulus and full signed norm inequalities; physical q=1 cancellation checked 147 times. The model does **not** execute the Lean selector or prove source equality.
- Exact source file read back from GitHub with blob `f7f4a47d03edba7b88ef1f07a97772069b813b7b`; escape-token scan of the new source found zero forbidden proof escapes.
- **NOT RUN:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex or heavy numerical producer. New `#check` names are registered in `VERIFY.lean` only, not executed. Nothing is promoted GREEN; elaboration and imported SOURCE_ONLY paths remain risks.
- `EXTERNAL_INPUTS.json` unchanged: (M) remains only registered, not formalized or axiomatized. No new axioms, manuscript/production/toolchain/lock changes, excluded full87 work, PR or CI action.
- **Next exact entrance:** identify real integer rho_T and its physical Q_T and prove a useful norm/cancellation on that *literal* coefficient for this unit family; continue all-marked/HB atom compiler, nonzero-shift mixed moments, exceptional HB product=T, and uniform original W_T Fourier L1/H with growing m(N). P3.6 stays YELLOW.


## Successor SOURCE_ONLY increment — actual U8 direct unit source payment, prime-only same-rho insertion (2026-11-08 UTC)

- Baseline HEAD: c4d0bf71dbd1c2770add4f89a519482a7ff85e19 on chatgpt/p3-internal-original-w-20261105; read current REPORT, REGISTRY, EXTERNAL_INPUTS, authentic U8 source and the pinned manuscript. Root, docs, source-only and packet AGENTS.md paths not found; no inferred hidden restrictions.
- Genuine proof source: P3ActualU8DirectUnitPayment.lean, 148 lines, blob ea258443d84a53874835aa8334cff910ba827cf7. Proof commit 8750778c8bdf7ac78414998b09e78f3bdb9f0bfa with [skip ci]. VERIFY.lean blob 3c241b45c1118bb92c92c73b9caff1296c56f557; three new imports-first checks REGISTERED but NOT RUN.
- Paper pin: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b; completion module section 1 and 4(F), manuscript-body original U8/PP. Mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 unchanged.

### Precise mathematical contribution and correction

The previous U8 unit physical L1 theorem is only a conditional reduction; it is NOT necessary to spend its unknown actual physical rho L1 for the ORIGINAL U8 upper COUNT. The already proved-in-source identity is literal U8 count = actual prime-quotient triple prime mass + actual quotient-one unit-pair count. The latter is a direct positive source-count error with upstream card <= N^(2/3); it is not the physical modulus q=1 and is not an empty Gamma mother. This does not claim global unit-pair PP as a separate distribution statement.

The new first candidate uses the real arithmetic productWeight_sum and arithmetic_filter_prime_eq to prove that its original positive-family small prime PP cutoff loss is <= the actual small-Goldbach-prime triples count, provided physical presieve cutoff z <= N^(1/5). The sieve loss P<z is strict, whereas the actual small source uses P<=N^(1/5), so no endpoint is dropped. Original product labels, inclusive repeated terminal prime, true multiplicities and centre mask are retained.

The second candidate uses the existing noncircular pointwise sieve upper majorant for ALL n and positive-family PP insertion to derive a new genuine finite U8 upper counting inequality:
    U8 <= original rank-three mass*physicalDensity(Q,rho)
       + exactCoprimeCorrection(Q,rho)
       + true Part3 primeProductSignedError(Q,rho)
       + #actualSmallGoldbachPrimeTriples + #actualUnitFibres.
The same signed physical rho appears in count, coprime mean and density, with the complete modulus sum before absolute value. No separate unit-family PP error or L1 hypothesis is inserted.

The third candidate uses the existing actual source-error power payment to bound BOTH literal source-count errors by epsilon*singularNormalization for all sufficiently large N; the threshold precedes z, Q and rho. It does not invent a target-equivalent PP premise. The remaining prime-triple PP is still an analytic obligation.

### Checks, trust boundary and next entry

- GitHub proof and VERIFY readback matched blob ea258443d84a53874835aa8334cff910ba827cf7 and 3c241b45c1118bb92c92c73b9caff1296c56f557, three declared names present, imports before checks. Forbidden proof escapes 0, lexical delimiters PASS.
- Independent Python exact-Fraction arithmetic model: 341 N targets 60..400, 14,760 tuple-modulus terms, 8 small-prime examples and 3,643 model unit-pair occurrences; signed physical rho(1)=2, rho(2)=-1/2, rho(3)=-1/4, rho(5)=-1/4 has pointwise kernel >=1; observed 0 mismatches. This is a broad finite model, NOT the literal Lean U8 selector, and not a Lean proof.
- NOT RUN: Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. All new and upstream nodes remain SOURCE_ONLY/UNCOMPILED/KERNEL_UNVERIFIED; no GREEN promotion.
- EXTERNAL_INPUTS.json unchanged at Git blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab. Research (M) remains RECORD_ONLY_NOT_IMPLEMENTED_NOT_AXIOM. No new axioms, target-equivalent assumptions, default/production changes, manuscript or lockfile edits, excluded full87 parent, other tasks, PR or CI changes.
- Next: bind literal physical Q_T and integer rho_T from the frozen upper sieve policy into the genuine pointwise majorant and cutoff z<=N^(1/5), then into the rank-three actual PP. Do not confuse the physical sieve level with auxiliary cover. Independently complete marked/HB compiler, full HB product=T exception, nonzero mixed divisor moments, original W_T continuous Fourier L1/Fubini/H and growth in m(N), causal/whole-box, empty Gamma mothers and high-rank/enhanced. P3.6 remains YELLOW.

## Successor P3.6 SOURCE_ONLY — authentic raw small/rough Rosser Q,rho in U8 insertion (2026-11-08 UTC)

- **True recovery baseline:** branch `chatgpt/p3-internal-original-w-20261105` at `999a86c9967ea729b20233525578765139c9acce`, rather than obsolete de582e6. Inspected current REPORT, REGISTRY, EXTERNAL_INPUTS, last `P3ActualU8DirectUnitPayment.lean`, original `P5zPositiveFamilyBudget`, `ActualSmallRoughAttachment`, `FiniteUpperCarrierCore`, `RealPhysicalUpperWeightBridge`, original U8 source and pinned manuscript. Root and relevant ancestor AGENTS.md probes returned NOT_FOUND. No competing update observed during this change.
- **New proof candidate:** `P3ActualU8RawPhysicalSieve.lean`, **113 lines including final newline**, Git blob `00997a2486dc0af9bb3d0fa702b497aba60ac2ba`; source commit `672a3c988ecb2402e4ee0f7c436f6dcddb90283d` [skip ci]. VERIFY additions commit `9416d1d8ae662083f600844df4a58bd7842dc73c`, Git blob `745bdf2e64b10932cadef0fcb4443ed91880c1c1`; REGISTRY update commit `efb30741c80984cb37816d7bf5dd8ecccece38a6`, Git blob `4724c914798c42488d307dcaa795798134804121`. Exactly three named candidate #checks registered; **not Lean-executed**.
- **Fixed source statement:** `chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b` in `manuscript-body.tex` lines 256–280 (absolute signed PP, exact coprime mean) and 452–556 (same `rho_N` pointwise upper and positive product application), completion module §1 and §4(F). Pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged.

### Exact new internal connection

The preceding direct-unit insertion required an independent pointwise majorant for arbitrary physical `Q,rho`. This increment discharges **that specific finite hypothesis** for the **genuine raw small/rough Rosser attachment** supplied by production-path `actualSmallRoughRho_sieveProduct_majorant`.

For any retention policy `retainOdd`, auxiliary enumeration cap `cap`, real presieve cutoffs `w≤z≤cap`, Rosser level `1<L` with `w≤L`, define only by the unchanged source:
`Q=actualSmallRoughModuli retainOdd N cap w z` and
`rho=actualSmallRoughRho retainOdd N cap w z L`.
The upstream **proved-in-source** pointwise Rosser majorant gives for **all** natural test integers `n`:
`1_(gcd(n,sieveProduct(N,ceil(z)))=1) ≤ physicalDivisorSum(Q,rho,n)`.
This uses the same literal physical `Q,rho` in the U8 mass times density, exact coprime correction, and the original rank-three `Part3.primeProductSignedError`. The new theorem `actual_u8_upper_at_raw_physical_coefficient` inserts that genuine weight with no `hmajor` premise and with the actual rank-three product coefficient and inclusive repeated terminal-prime wall. U8's **quotient-one pair** stays a direct source-card error; no unit-family PP/L1 is assumed or hidden.

The companion `actual_u8_raw_physical_moduli_legal` traces **the same displayed carrier** through upstream squarefree, coprime-to-target, and divisor-of-`sieveProduct(N,ceil(z))` lemmas, without identifying the auxiliary rough cap as a physical sieve level. The cutoff `ceil(z) ≤ N^(1/5)` is explicit: the physical prime selector uses strict `p<z`, hence precisely `p<ceil(z)` also at integral `z`; U8's small Goldbach-prime source uses inclusive `P≤N^(1/5)`. No endpoint has been discarded.

Finally `eventually_actual_u8_raw_physical_upper` derives from the prior genuine U8 power-error budget a **common eventual threshold chosen before** `cap,retainOdd,w,z,L`. At that threshold, the two literal source-card errors are absorbed into `epsilon*singularNormalization N` uniformly over parameter choices satisfying the geometric hypotheses. The rank-three physical PP discrepancy remains explicitly in the upper bound, unestimated and with the same signed rho.

### What this increment does **not** prove

This binds an actual **raw** real-valued Rosser attachment, **not** the manuscript's final causally frozen compiled **integer** `rho_T` or its final `Q_T`. There is no proof yet that the final policy equals this parameterized raw coefficient, nor that its `z_T=N^(19/96)` rounding obeys the needed `ceil(z_T)≤N^(1/5)` uniformly at one target threshold. The coefficient's physical/auxiliary levels cannot be exchanged. No density `K`, arbitrary-log PP estimate, Fourier `W_T` budget, HB product=T payment, or all-source atom compiler is established by this theorem. Source-only import of the preceding staged P3 module **does not resolve on a default Lake module path**; both this source and its ancestors remain UNCOMPILED/KERNEL_UNVERIFIED.

### Checks actually performed

- Read back the newly created GitHub source blob `00997a2486dc0af9bb3d0fa702b497aba60ac2ba` and VERIFY blob `745bdf2e64b10932cadef0fcb4443ed91880c1c1`; forbidden proof-escape tokens in new source after comments: **0**; simple lexical `()[]{}` delimiter counts balanced; all three declared names present in new source and VERIFY, with imports preceding the checks. JSON registry parsed and updated; external input register unchanged.
- Independent deterministic Python finite model checked **83,997** cases of strict prime cutoff `p<z` against `p<ceil(z)` and equivalence of the full indicator to literal coprimality, including **688 integral-prime endpoint** cases, N=2..62, negative/zero integer test arguments and rational cutoff values. Checked another **18,598** small finite model squarefree/coprime/divisor support cases. **Zero discrepancies.** These are model/endpoint sanity checks and **do not execute the original Rosser coefficient or Lean definition**, much less certify the real majorant in the Lean kernel.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex or heavy producer. No new green node. `EXTERNAL_INPUTS.json` unchanged blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; (M) REGISTER_ONLY, NOT IMPLEMENTED, NOT AN AXIOM. No new axioms, circular target premises, changes to manuscript, source producer, main/master, full87 excluded node, other tasks, PR, dependencies, or toolchain. Commits use [skip ci].

### Specific successor

Locate the genuine finite causal `retainOdd_N` compiler and the **FINAL** physical `Q_T` and integer `rho_T`, and prove their identity to the parameterized raw attachment with its exact support/levels; derive `ceil(z_T)≤N^(1/5)` at one target threshold. Then attach the actual U8 prime-three absolute arbitrary-log PP bound and physical density/coprime budget, without inventing the required analytic saving. Independently continue all-marked/HB atom source dictionary, product=T HB exceptions, nonzero-shift mixed divisor moments, original `W_T` Fourier L1/Fubini/H uniform over `m(N)`, causal whole-box and empty Gamma mothers, high-rank/enhanced, and full same-rho PP assembly. P3.6 remains YELLOW, this particular RAW coefficient-insertion candidate BLUE only.

## Successor P3.6 SOURCE_ONLY — literal attached N-dependent upper and rho_0 ceiling (2026-11-08 UTC)

- **Checked recovery baseline:** c536a15ac3814c8153b8ce4d4fcedd1c9638fcb4 on chatgpt/p3-internal-original-w-20261105, NOT the obsolete de582e6 branch; last handoff REPORT, REGISTRY, EXTERNAL_INPUTS and actual P3ActualU8RawPhysicalSieve/DirectUnitPayment sources were read. Root and ancestor AGENTS.md paths returned NOT_FOUND. No same-branch concurrent edit was seen before proof push.
- **Actual proof commit:** 5480b5126c8f2082a2fd281cf6a089b09e0719b9 [skip ci]. New file P3ActualU8AttachedPhysical.lean, 115 nonempty/terminal-line-adjusted lines (source split length 116), Git blob e16dd2c3ac1c958cf1598af920d08c31604b2f68. VERIFY new blob b77e249842e59436d444072072df1d0af0300cff; REGISTRY blob 7e160d9aa466a8c371b2639df05ec4ca48d33c0e. Three new #check declarations registered only; none executed. The entire commit changes only these three P3 files.
- **Pinned manuscript:** UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex line 364 (rho_0=19/96), lines 256-280 (same signed PP/coprime mean), 462-467 (physical sieve upper), and paper/source/modules/distribution-prime-product-completion-20261010.txt §4 (F). Mathlib pin unchanged at e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

### Genuine mathematical/source contribution

The prior raw coefficient bridge allowed arbitrary w,z,L, requiring the hypothesis ceil(z) <= N^(1/5) at each target. The actual existing production source ImbalancedChen/ActualUpperCountingInputs.lean ALREADY defines a nontrivial N-dependent attached pair:

    Q_N = attachedUpperModuli nu r epsilon retain cap N
    rho_N = attachedUpperCoefficient nu r epsilon retain cap N
    w_N = N^(nu epsilon^2), z_N = N^(nu r), L_N = N^(nu epsilon).

This packet now uses those exact source functions, not an independently copied Q/rho. The existing attachedUpperCoefficient_majorant proves the pointwise majorant without requiring any PP discrepancy. The source-only candidate eventually_attached_u8_cutoff uses the existing eventually_floor_rpow_add_one_le_rpow for the strict gap nu*r<1/5 and proves the precise CEILING inequality eventually. The eventual target threshold is chosen BEFORE any retain/cap functions; their only remaining coverage condition at each N is cap(N)>=N^(nu*r).

Then eventually_u8_at_attached_upper feeds this literal majorant, exact U8 labelled mass/density, original coprime correction and original rank-three Part3.primeProductSignedError into the earlier genuine direct unit-card payment. **The same rho_N** occurs in all three terms; the quotient-one fibre is not separately charged a PP/L1 norm. The analytic PP discrepancy remains an EXPLICIT unbounded term, and no sign of rho is discarded.

Finally eventually_u8_at_manuscript_rho0 specializes (nu,r)=(1,19/96). Exact exponent comparison:

    19/96 = 95/480 < 96/480 = 1/5.

It is essential that ceiling<=N^(1/5) is EVENTUAL, not true for every N. One independent finite numerical regression checked N=2..200000 (199,999 cases): **151,467** failed the stronger ceiling inequality and 48,532 passed, so claiming it pointwise would be false. The proof candidate instead uses the pre-existing rigorous power-gap eventual lemma. An additional independent 100-digit decimal sanity check at N=2^480 (145-digit integer) found upper/z about 2 and upper-z about 3.9614081257e28. The elementary identity x=N^(1/480)>=2 => ceil(x^95)<=x^95+1<=x^96 confirms a possible large threshold; these computations are illustrative ONLY, not Lean acceptance.

### Trust boundary and next entrance

- New source forbidden proof-escape scan after comments: zero; lexical bracket balance passed. VERIFY imports occur before every #check; REGISTRY JSON parsed. GitHub atomic create-tree/commit/ref-write returned success for the proof commit, with exact branch-base optimistic lease.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex or heavy numerical producer. Inherited staged-only import ImbalancedChen.P3ActualU8DirectUnitPayment is not on default production path, so the source does not claim default Lake buildability. All declarations remain candidate SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED; **no GREEN**.
- This result still has a REAL-valued attached raw coefficient with arbitrary retention/cap and an admitted cap-coverage condition. It does **not** identify the final causally frozen compiled INTEGER rho_T or physical Q_T. It does not prove actual density currentK, exact whole-family PP arbitrary-log absolute error, the nonzero-shift arithmetic mixed moment, W_T Fourier uniform L1/H/Fubini, HB product=T exceptional payment, causal whole-box, empty Gamma mothers, or high-rank/enhanced sources.
- EXTERNAL_INPUTS.json remains unchanged, Git blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab. Research input (M) is ONLY REGISTERED, not implemented or axiomatized; no new axioms, unsafe shortcuts, production modifications, manuscript edits, excluded full87 work, toolchain or CI changes.

**Next:** Trace the actual final frozen retained-prefix policy, the compiler's physical modulus carrier and coefficient (including the integer-versus-real issue), and an exact equality or a source-proved error bridge to attachedUpperCoefficient. Keep the same complete signed rho in count/density/PP and derive the final causal cap coverage. Only then tackle the genuine analytic PP saving and whole marked/HB atom compiler. P3.6 remains YELLOW; this specific attached physical and rho_0 cutoff source scope is BLUE without any compilation verification.

## Successor P3.6 SOURCE_ONLY — literal U8 signed PP on a compiler common carrier (2026-11-08 UTC)

- **Actual branch baseline:** `2276c9b3b463cf9df0683f21c461a6704c1e9d38`. Proof commit: `f31bd9f50f2f60fd851976bfa415c7fb1695637f` ([skip ci]); source `P3ActualU8CommonCarrierPP.lean`, 160 lines, Git blob `e9b23071808a1356b3871ee10060bb29f0f5767f`. Actual GitHub readback confirmed the source blob. New VERIFY blob: `eb410a15e2507935ae066c94f8d8f27586684315`; registry blob: `f1f9455936894ea58343d95e1a71359a94519750`.
- **Fixed manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; `paper/source/manuscript-body.tex` lines 256–280 (same signed rho, original prime-product label and exact coprime mean), lines 452–478 (final physical compiler); `paper/source/modules/distribution-prime-product-completion-20261010.txt` §1 and §4(F). No manuscript version switch. Mathlib pin unchanged `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- **Source dependencies actually inspected:** `ImbalancedChen/FiniteUpperCarrierCore.lean` literal `sum_actualSmallRoughRho_mul_eq_on_common_carrier`, `ImbalancedChen/CurrentChenUpsilon8SharpKPhysicalPP.lean` original source and `distribution_eq_physicalPP`, `ImbalancedChen/P5zPositiveFamilyBudget.lean` exact signed discrepancy and coprime correction. Root and relevant ancestor `AGENTS.md` paths were probed and returned NOT_FOUND, no unseen constraints inferred.

### Mathematical increment and exact applicability

For every genuine raw retained upper rough support (R_0) and covering finite carrier (R\supseteq R_0), the physical small/rough attachment with the **same raw signed coefficient extended by zero** gives exactly the same original U8 rank-three signed PP discrepancy. This follows by the existing nontrivial zero-extension coefficient identity and an explicit original labelled-U8 reindexing, not by comparing two independent absolute errors. The exact labelled coprime correction and original U8 physical divisor sum are also transported unchanged. The union carrier `actualUpperCommonRoughSupport` discharges the inclusion automatically and may include additional compiler-only moduli.

**CRITICAL DISTINCTION:** this is a ZERO EXTENSION of the RAW retained coefficient. It does **not** prove that a separately compiled rough coefficient has the same values, that compiler-only moduli obey the raw physical support/level constraints, or that final (Q_T,\rho_T) are this function. To pass from the raw coefficient to the final *integer* (\rho_T), the compiled-minus-raw coefficient error (including compiler-only terms) remains a genuine, unpaid internal obligation. This packet proves no analytic PP logarithmic saving. The U8 repeated terminal prime (q=p_2), primitive mean and source multiplicities remain literal.

### Checks and trust boundary

- One SOURCE_ONLY proof file, five names; lexical delimiter scan PASS, forbidden proof escapes 0; GitHub readback blob matched. The five `#check` names are **registered only**, not executed.
- Independent deterministic integer-scaled finite arithmetic regression: **1,800 cases, zero failures**; 26,688 signed modulus terms, 4,128 negative-rho occurrences, 8,208 additional zero-coefficient moduli and 1,416 repeated-product source labels. Exact scaling 27,720 covers totients used in the toy carriers. This is a model of finite signed zero-extension and does **not** run the actual Rosser algorithm, U8 selector, Lean or the kernel.
- **NOT RUN:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, heavy producer. New source imports production modules only, but those source declarations and some upstream files remain independently uncompiled. No new GREEN.
- `EXTERNAL_INPUTS.json` unchanged at Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: external (M) REGISTER_ONLY, not implemented, not axiomatized. No changes to other tasks, production source, excluded 87-domain parent, manuscript, toolchain, lockfile, PR, merge, force push or CI.

### Actual next proof entrance

Read the final finite causal compiler's actual retained policy, integer coefficient and physical (Q_T); establish its pointwise coefficient difference from this literal raw source, including compiler-only moduli, before transferring *analytic* PP bounds. The physical and auxiliary covers cannot be conflated. Separately the quantitative original (W_T) Fourier uniformity, mixed shifted divisor bounds, HB product=T exception, all marked/HB source coverage, empty Gamma mother words, high-rank/enhanced and common threshold remain open. **P3.6 stays YELLOW**; this limited exact source-only zero-extension candidate is BLUE only.

## Successor P3.6 SOURCE_ONLY — actual U8 integer rough candidate coefficient delta (2026-11-08 UTC)

- **Recovered actual branch HEAD**: `dac18949a010ac33f93468c24cbc6bfd2d74c884` (no new concurrent branch changes at pre-write checks), branch `chatgpt/p3-internal-original-w-20261105`, not obsolete `de582e6`.
- **Proof commit**: `874e463cc59ad6e5962c05cb2685f072c8ef7e24` ([skip ci]); file `P3ActualU8CompiledDelta.lean` (175 split lines including the trailing newline), Git blob `c0e1ffa2f01c20064f1f705fd7c9dc6705efe685`, fetched back from GitHub.
- **Verification registration / structural repair**: `991f8864f35817d788e39815e6d97d745ab518a2`; `VERIFY.lean` Git blob `6f491226fc5ff684cff05a1c5fba66bc29b1a1f1`. The predecessor file had ONE import below executed-looking (but **not actually executed**) #check commands; all 54 imports were moved before any #check, and four new checks registered only.
- **Updated registry**: commit `e0a74de4132572dda5726efdce34792f40d3dd1c`, `REGISTRY.json` Git blob `2af95430896f98424d4b68bcb20196406e271f75`. Original external register unchanged, blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`.
- **Pinned manuscript**: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; `paper/source/manuscript-body.tex` lines 256–280 (signed PP and exact coprime mean), 452–478 (physical compiler); `paper/source/modules/distribution-prime-product-completion-20261010.txt` sections 1, 4(F). The fixed Mathlib pin remains `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- **Real sources actually read**: `ImbalancedChen/FiniteUpperCarrierCore.lean`, `ImbalancedChen/FixedRoughCoefficients.lean`, `ImbalancedChen/ActualSmallRosser.lean`, `ImbalancedChen/SmallRoughAttachment.lean`, `ImbalancedChen/ActualUpperCommonCarrier.lean`, `ImbalancedChen/CurrentChenUpsilon8SharpKPhysicalPP.lean`, `ImbalancedChen/P5zPositiveFamilyBudget.lean`, `ImbalancedChen/ActualUpperCountingInputs.lean`, both predecessor P3 common-carrier and unit-positive-modulus norm files. Root/ancestor packet `AGENTS.md` reads returned NOT_FOUND; no hidden instructions inferred.

### Genuine internal math/source increment

The previous packet established RAW `rho_raw` zero-extension invariance on a common carrier, but that does **not** equal a separately compiled coefficient. This increment makes the missing difference **EXACT** for the actual sorted U8 rank-3 positive prime-product family, retaining the `p2=q` repeated terminal-prime wall and original source occurrence IDs.

For original small Rosser support (S_{\\mathrm{small}}), a rough common carrier (R) containing the actual retained raw rough support (R_0), and genuine physical product moduli (Q=S_{\\mathrm{small}}R), the new file defines two different physical coefficients using the SAME small Rosser attachment:

- `rho_raw`: literal retained `fixedRoughCoefficient` attached on (R), equal to the old raw coefficient on (Q_0) after zero-extension;
- `rho_comp`: an **arbitrary integer-valued rough candidate** `compiled : Nat -> Int` first cast to `Real` and then attached using exactly the same small Rosser kernels.

Writing `delta(q)=rho_comp(q)-rho_raw(q)`, `A_q` for the actual U8 full labelled congruence mass and `B_q` for the **exact** coprime mass, the candidate establishes

`E_U8(Q,rho_comp) = E_U8(Q_0,rho_raw) + sum_(q in Q) delta(q)*(A_q-B_q/phi(q))`.

The full signed sum is kept intact until after the coefficient difference is formed. Compiler-only moduli remain in the delta sum; no arbitrary modulus is silently thrown out. In contrast to the raw zero-extension theorem, the extra term does **not** vanish by support inclusion alone.

For (R) consisting of genuine `RoughPrimeSupportedAt` factors, `commonQ_positive` derives **positive physical moduli** from actual small-Rosser squarefreeness and nonzero rough factors. The existing exact indicator-source bound then yields

`|E_U8(Q,rho_comp)-E_U8(Q_0,rho_raw)| <= card(S_U8) * sum_(q in Q)|delta(q)|`.

This is a finite algebraic quantitative *reduction*, NOT a proved bound on the actual final compiler, and does NOT supply the manuscript's arbitrary-log PP saving. In particular **an integer rough candidate passed through real small Rosser weights need not itself produce an integer physical coefficient**. The final causally frozen integer `rho_T`, its physical (Q_T), exact support/levels, retained policy and a useful delta mass bound still require a literal producer connection. This statement makes no target-equivalent assumption.

### Actual checks and unverified boundary

- Source was read back at blob `c0e1ffa2f01c20064f1f705fd7c9dc6705efe685`. Source escape-token scan after comment removal: **0**. Static bracket/delimiter scan: **PASS**. Four new Lean declaration names found and registered; #check registrations were **not run**. Earlier `VERIFY.lean` import ordering defect was fixed; remaining SOURCE_ONLY modules are still not proven to resolve in the default Lake path.
- Independent deterministic scaled-integer finite regression: **504/504** source/modulus/positive-coprime-mean perturbation cases, **0** differences; **301** test cases included at least one duplicate physical product with distinct occurrence IDs. The model checked raw zero-extension, signed compiled-minus-raw equality and the cardinal times L1 envelope, including signed rough candidate coefficients. This is **NOT** an execution of the original rough compiler, exact U8 Lean selector or its proof.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axioms, Codex, or heavy producer. Four new declarations and both imported predecessor SOURCE_ONLY proofs remain compilation/elaboration risks; **NO GREEN**.
- No change to manuscript, master, other automation branches, excluded full-87 parent/history, production modules, PR, toolchain or dependency locks. (M) is **registered only**, not implemented or used as an axiom.

### Precise next internal entrance

Find and read the final frozen causal integer compiler and its retained-`retainOdd_N` policy. Prove that its literal **physical** coefficient and moduli correspond to `integerCompiledRho` / `commonQ` (or supply the exact difference), including real-small-weight casting and extra compiler-only modulus support. Prove a true usable delta mass/weighted discrepancy estimate, not merely assume it. Then combine with actual U8 signed PP under a single coefficient, controlling density and the exact coprime correction together. Separately still open: all marked/HB atom dictionary, complete-product=T exceptional mass, nonzero shifted-divisor moments, actual (W_T) Fourier L1/H/Fubini uniform for growing (m(N)), causal whole-box, empty Gamma mothers, high-rank/enhanced and final same-rho PP assembly. **P3.6 YELLOW**; the four exactly delimited finite source candidate statements BLUE; kernel/CI verification absent.


## Successor P3.6 SOURCE_ONLY — genuine even-retaining first-exit tree at the original U8 PP (2026-11-08 UTC)

- **Actual recovery and scope:** verified HEAD `d1aa48acc704f1fc6a165b77cda95d02057bd710` on `chatgpt/p3-internal-original-w-20261105` before writing; read last REPORT/REGISTRY/EXTERNAL_INPUTS and actual U8 compiled-delta source, inspected root/docs/packet AGENTS (all NOT_FOUND) and frozen manuscript `9731290e8f53cffda44129906cde6a965eaa869b`. Also read existing finite `ActualUpperPolicyFiniteBridge`, `ActualSmallRoughAttachment`, `CurrentChenUpsilon8SharpKPhysicalPP`, `FiniteUpperCarrierCore`, `P3ActualU8CommonCarrierPP` and relevant upper compiler/density modules.
- **Actual proof commit:** `5e1c878d4e8f96b23d84a67e6e6b5891fce669f6` [skip ci], new SOURCE_ONLY `P3ActualU8EvenRetainedTreePP.lean` (167 changed lines), Git blob `42c78c1c15520ef7a1112c310c6646a56a3aac3f`; same commit updates `VERIFY.lean` blob `6ab6d9644597b7b6881c83f4f597e2c6b6c3e54f`. GitHub readback matched both exact blob SHAs and all six declaration names. It affects ONLY the stated P3 packet.
- **New source-level contribution:** for a genuine first-exit Boolean retention policy that ALWAYS retains the even sign, the original first-exit support and INTEGER Möbius lookup are shown pointwise equal to the raw `fixedRoughSupport`/`fixedRoughCoefficient` built from its odd test, including off-support zeros. This uses the existing nontrivial `UpperPolicyFiniteBridge` identities, not a fabricated compiler field. As a result the original actual small Rosser attachment has literally the same physical Q and REAL-valued rho for the pointwise sieve majorant, original U8 sharp-K signed rank-three PP insertion, density and exact labelled coprime correction; the p₂=q terminal repetition remains in the untouched original physical weight.
- **Common-carrier payoff on the exact-equality class:** if the added rough carrier contains that actual tree support and the compiler rough values are LITERALLY those same first-exit INTEGER values, the entire original U8 PP is exactly its raw PP on the original physical carrier, including the complete signed primitive mean. Hence the compiled-minus-raw coefficient difference is **identically zero for this precisely identified class**; this is stronger than the preceding mere L1 criterion but is NOT valid for a different independently constructed causal compiler. No estimates on different compiler candidates are smuggled in.
- **Pinned manuscript locations:** `paper/source/manuscript-body.tex` original signed PP and exact primitive means (around lines 256–280), physical upper compiler (around 452–478); `paper/source/modules/distribution-prime-product-completion-20261010.txt` §1, §4(F). No changes to manuscript or pinned dependency.
- **Checks actually run:** readback of GitHub source and VERIFY, lexical proof-escape scan (0 matches), balanced `()[]{}` static scan, six new names found and six `#check` registrations present (none executed). Independent deterministic Python exact-rational toy model checked **768 cases / 6,144 modulus terms**, of which **2,304** have negative coefficient, with **0 mismatches** for the original signed discrepancy and unchanged zero-extension. There were 108 labelled model occurrences including 61 with p₂=q. It did **not** execute the original first-exit producer, real Rosser weights, Lean selector or actual U8 theorem.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axioms, Codex, heavy producer. The new module imports staged SOURCE_ONLY code and remains UNCOMPILED/KERNEL_UNVERIFIED; no GREEN. `EXTERNAL_INPUTS.json` remains EXACT blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; manuscript (M) REGISTER_ONLY, not implemented or axiomatized.
- **Crucial limitation / next exact entry:** a free even-retaining first-exit policy is NOT the final causally frozen whole-domain policy, and an integer rough coefficient passed through real small Rosser weights need not produce an integer physical `rho_T`. Identify the literal final retained policy, physical Q_T and coefficient producer; establish literal equality to this class or prove a genuine quantified coefficient difference with level and weight bounds. The all-source marked/HB atom dictionary, product=T exceptions, nonzero shifted-divisor moments, quantitative original W_T Fourier L1/H/Fubini uniform in growing m(N), empty Gamma mothers, high-rank/enhanced and arbitrary-log same-rho PP remain INTERNAL open obligations. P3.6 YELLOW; only this limited actual tree/U8 source candidate BLUE.

## Successor P3.6 SOURCE_ONLY — sign-sensitive physical-to-rough delta norm (2026-11-08 UTC)

- **Verified branch baseline:** `1cae54a1c103f2dcb91bdc7699cca0283658a8e5` on `chatgpt/p3-internal-original-w-20261105`. Before ref update GitHub HEAD and parent tree were re-read; update_ref returned success with non-force fast-forward. No concurrent branch update was observed at both checks.
- **Real proof commit:** `41c1dfe8f97a5400460cbf72491c4d847c061abb` (`[skip ci]`); new staged source `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8RoughDeltaNorm.lean` (235 lines), Git blob `012c5eaadb686f2be89e46c9d99777cc28ab27a3`. `VERIFY.lean` was updated in the same commit; Git blob `eef66501f8934c51c349319b16e5b87437fa6059`, four checks registered, **not executed**.
- **Real dependency inspection:** `SignSensitiveAttachment.lean` (literal sign switch), `SmallRoughAttachment.lean` (one physical coefficient, unique cutoff-separated product), `ActualSmallRosser.lean` (literal upper/lower Rosser weights), `FiniteUpperCarrierCore.lean`, `P3ActualU8CompiledDelta.lean`, `P3ActualU8UnitPhysicalNorm.lean`, `CurrentChenUpsilon8SharpKPhysicalPP.lean`. Root, docs, source-only, packet, and ImbalancedChen `AGENTS.md` were queried and not found; no hidden constraints inferred. Fixed manuscript `9731290e8f53cffda44129906cde6a965eaa869b`, `manuscript-body.tex` lines 450-478 and `distribution-prime-product-completion-20261010.txt` section 1 were read; no version change.

### Real mathematical increment

For fixed literal small-prime Rosser beta-minus/beta-plus and ANY two rough real coefficients x,y, the sign-dependent attachment satisfies

`|signAttachedCoefficient(x,betaMinus,betaPlus)-signAttachedCoefficient(y,betaMinus,betaPlus)| <= max(|betaMinus|,|betaPlus|)*|x-y|`.

The proof explicitly handles the two cross-zero cases; **it does not incorrectly treat signAttachedCoefficient as a linear function of c**. By the already-proved unique physical small/rough product, this pointwise Lipschitz result yields the true finite physical coefficient estimate

`sum_(q in Q) |rho_comp(q)-rho_raw(q)| <= B_small * sum_(d in rough) |compiled(d)-fixedRoughCoefficient(d)|`,

where `Q=smallRoughModuli(actualSmallRosserSupport,rough)` and `B_small=sum_(a in actualSmallRosserSupport) max(|actualSmallRosserMinus(a)|,|actualSmallRosserPlus(a)|)`. The beta norm is **the actual Rosser provider's**: a small slot with both weights zero contributes zero, so no artificial factor `#Q` appears. This is a precise new reduction of the previous *physical* compiled-minus-raw L1 criterion to the *rough* coefficient change.

Composing it with the actual original U8 rank-3 signed PP difference and positive-modulus exact-primitive-mean L1 lemma gives

`|E_U8(Q,rho_comp)-E_U8(Q,rho_raw)| <= card(original_U8_arithmeticTriples) * B_small * sum_(d in rough)|compiled(d)-raw(d)|`.

All original U8 sorted occurrence labels (including p2=q), the complete physical products, the same Q, and exact coprime mean remain untouched. This compares TWO coefficients on the SAME common carrier; the predecessor raw-zero-extension theorem is separately needed to compare against the smaller raw carrier. No final compiler policy, coefficient difference budget, or PP saving is claimed.

### Checks and outstanding obligations

- GitHub proof and VERIFY readback matched both blobs. Source lexical forbidden-escape scan: 0; brackets: balanced. Verify import ordering remained 56 imports before every `#check` (registered only).
- Independent signed integer-slope finite algebra: **14,641/14,641** crossings/sign combinations with 0 errors. Independent toy cutoff-separated product family with exact integer-scaled beta and rough coefficients: **240/240** physical L1 inequalities, 0 errors. These are **not** Lean, not exact Rosser producer execution and not a proof of the true source's bound.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axioms, Codex, heavy producer. The SOURCE_ONLY file imports previous uncompiled SOURCE_ONLY proof material; elaboration risk remains, and there are no new GREEN nodes.
- **(M):** `EXTERNAL_INPUTS.json` remains exactly Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: record only, no implementation or axiom. No production module, manuscript, other task, excluded 87-domain node, toolchain, PR or master edit.
- **Next strict entry:** bound `B_small` using the actual Rosser active-support predicate `d<L`; then inspect the genuine causal frozen rough coefficient producer and derive a **real** bound on `sum|compiled-fixedRaw|` (not a mere named hypothesis). Identify physical and auxiliary levels, complete `rho_T,Q_T`; otherwise this norm inequality is not a paid discrepancy. Independently open: full marked/HB source, complete product=T exceptions, nonzero shifted divisor moments, actual W_T quantitative Fourier L1/H/Fubini uniform for growing m(N), empty Gamma, high-rank/enhanced and complete same-rho PP. **P3.6 stays YELLOW.**

## Successor P3.6 SOURCE_ONLY — actual small Rosser strict-level mass (2026-11-08)

- **Baseline and scope:** read the verified branch HEAD `ced21fa5d9ceb9d4dc053bacdb5c624cb0b5681f`, this unique REPORT, REGISTRY, EXTERNAL_INPUTS and the immediately preceding `P3ActualU8RoughDeltaNorm.lean`; also read the genuine `ImbalancedChen/ActualSmallRosser.lean`, `ActualSmallRoughAttachment.lean`, `ActualUpperCountingInputs.lean` and `ActualUpperPolicyFiniteBridge.lean`. Root/docs/packet AGENTS files were queried and NOT_FOUND; no unshared constraints inferred. Frozen manuscript `9731290e8f53cffda44129906cde6a965eaa869b` was read in `manuscript-body.tex` lines 257–280, 451–475 and distribution completion §1 / §4(F).
- **Proof commit (actual GitHub):** `67ee5a1c609fedff27d4aae574338c50604953dd` [skip ci], new staged `P3ActualU8SmallNormLevel.lean` (140 lines), Git blob `b1bbdc3d5318e09f945c901da5387d0f3e8403cf`; `VERIFY.lean` blob `a78b1f80a15d8450b8eacb221a9aa7ba4a5b3e33`, three new `#check` recorded **not run**. Both blobs and exact names were read back after pushing. The second handoff-only commit records these facts; no production files, paper, other branches, PR, or toolchain changed.
- **Actual mathematical progress:** the original provider's `actualSmallRosserMinus_active` and `actualSmallRosserPlus_active` state nonzero implies **strict** `(d : ℝ) < L`. Contraposition makes **both** signed weights zero whenever `L ≤ d`. Their real absolute values are individually ≤1, so for the true small support `S`:

  `B_small = sum_(a in S) max(abs(betaMinus(a)),abs(betaPlus(a))) <= card({a in S : a < L}) <= Nat.ceil L`.

  Reusing the immediately previous source-level U8 complete signed discrepancy bound with unchanged physical Q and exact primitive mean yields:

  `|E_U8(Q,rho_comp)-E_U8(Q,rho_raw)| <= card(U8 original arithmeticTriples) * Nat.ceil L * sum_(b in rough) abs(intCompiled(b)-fixedRoughCoefficient(b))`.

  The same labelled p2=q repetition, complete product, sign-sensitive small attachment, positive physical moduli and signed rho are preserved by using the prior genuine U8 theorem. This is **not** a proof of the final causal rho_T producer nor an arbitrary-log absolute PP discrepancy saving. The level L can be N^(nu*epsilon), so the ceil L factor alone is polynomial. No rough compiler delta smallness is assumed or achieved. Strict inequality at d=L is retained: coefficients vanish on that boundary.
- **Checks actually executed:** GitHub source/VERIFY/blob readback matched. Source after comments: no sorry/admit/axiom/unsafe/native_decide, balanced round/square/curly delimiters; 57 VERIFY imports all precede all `#check`; three new declarations registered. Independent deterministic exact-rational **2500/2500** toy cutoff/mass cases with 0 discrepancies, including 197 exact level-equality cases. This toy check uses abstract 0,±1 coefficients consistent with the strict cutoff: **not** real Rosser execution, Lean, or kernel verification.
- **NOT RUN:** Lean, Lake, CI, kernel replay, complete transitive axioms, Codex, heavy producer. This SOURCE_ONLY proof imports an uncompiled staged predecessor and may fail elaboration; no GREEN node. (M) remains record-only and untouched at blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`; no external source was axiomatized.
- **Next entrance:** extract the true finite causally frozen rough integer coefficient from the approved original producer, test exact equality to the even-retaining class or obtain **real**, actually useful bounds on the rough coefficient difference. Do not confuse physical Q_T/rho_T with auxiliary support, or infer arbitrary-log saving from a polynomial ceil L. General W_T Fourier L1/H/Fubini uniform in m(N), entire marked/HB atom dictionary, product=T cases, nonzero shifted moments, causal whole-box, empty Gamma and high-rank/enhanced remain INTERNAL open. P3.6 overall YELLOW; this exact strict-level coefficient candidate BLUE only.

## Successor P3.6 SOURCE_ONLY — literal original fifth-policy physical U8 (2026-11-08)

- Checked baseline: 1d5a280aefa2cd7e8da1866b66311f44136180b8, branch chatgpt/p3-internal-original-w-20261105. No concurrently advancing HEAD was seen at the write checks. Previous REPORT, REGISTRY, EXTERNAL_INPUTS, and prior proof were read. No AGENTS.md exists at the searched root/docs/source-only/packet/ImbalancedChen paths.
- Proof commit: ae12b68bb619831d5420ac4aa83bc925270ceb95 [skip ci]. New SOURCE_ONLY proof P3ActualU8OriginalFifthPolicyPP.lean, 149 lines, Git blob 10dc2387c5a27f278ff95d723acf133e8d469d4c. VERIFY.lean blob b0bc5676d36bc27590e1df50e3a5174ac26f74e4, three registered #check (NOT executed).
- Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, manuscript-body.tex around lines 256–280 (original PP and exact primitive mean), 450–479 (physical upper compiler) and distribution-prime-product-completion-20261010.txt section 1 and section 4 (F). Pinned Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 unchanged.

### Genuine source-only mathematical step

The P1OriginalHistoricalPhysicalCoefficient.finalPolicy is the LITERAL original fifth-capped policy: original firstStop, activated third level, original fourth continuation and fifth historical lookup, including the source's J4/cap4/J5/cap5 parameters. This is NOT a substitute or solution for the excluded full87 dynamic-parent obligation. The upstream finalPolicy_even and original roughCoefficientInt support lookup yield a new exact bridge: the integer-valued rough coefficient (cast to real) matches its own raw odd-test first-exit coefficient at every integer, including off-support zero. Its actual small Rosser physical attachment remains REAL valued and is not claimed to be the global final INTEGER rho_T.

The new original_fifth_u8_common_carrier_PP theorem candidate transfers actual sorted labelled sharp-K U8 rank-three signed discrepancy to the larger rough carrier containing its literal original retained support. No label, p2=q repetition, exact primitive mean, signed physical rho or complete product is changed. The common-carrier identity is exact for the raw coefficient; it does NOT erase a delta for another globally compiled coefficient.

The new eventually_u8_original_fifth_rho0 candidate plugs the true original fifth-policy physical Q and rho into the already implemented source-only U8 direct-unit-quotient count and eventual 19/96 < 1/5 rounded cutoff. The common threshold is chosen before e, chi, m, omega, both fourth/fifth tables and enumeration cap; the latter has the real N^(19/96) coverage hypothesis. The resulting U8 upper bound retains physical density, exact coprime correction, the UNESTIMATED signed rank-three PP error, and delta*singularNormalization(N). This is a finite source-count insertion, not arbitrary-log PP, nor uniform original W_T Fourier admissibility.

### Verification and remaining obligations

GitHub source/VERIFY readback matched exact blobs; 58 imports precede all 348 #check commands. Static forbidden proof escapes: 0; lexical bracket stack balanced. Independent exact-integer toy regression: 720/720, no mismatches (300 even-retaining policy/odd-policy tree cases, 420 physical signed exact-mean zero-extension cases, 1400 negative-coefficient modulus appearances, 1310 duplicate tagged occurrences). These toy tests do not execute original frozen producer, real Rosser weights, Lean definitions or kernel.

NOT RUN: Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. Candidate elaboration remains unverified; no green state. EXTERNAL_INPUTS.json unchanged blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab: medium estimate (M) recorded only, never implemented or axiomatized. No production, manuscript, toolchain, excluded full87, other branches, PR or master modification.

Next entry: Identify whether the GLOBAL manuscript causal coefficient equals this actual fifth producer on its precisely licensed region; otherwise use the compiled-minus-raw delta and prove its real budget, distinguishing rough integer and physical real coefficient as well as physical/auxiliary levels. Still internal: all marked/HB words, product=T exception, nonzero shifted-divisor moments, actual W_T Fourier L1/H/Fubini uniform for growing m(N), causal whole-box, empty Gamma, high-rank/enhanced and actual same-rho arbitrary-log PP. P3.6 remains YELLOW.


## Successor P3.6 SOURCE_ONLY — actual fifth-policy rough mismatch cardinality (2026-11-08 UTC)

- **Verified baseline and branch:** `c4009207ca9dee48bc366cfbb1c9002652ade833` on `chatgpt/p3-internal-original-w-20261105`; the GitHub HEAD was checked before writing. Actual new proof commit: `1888835c7c6e1626b1fb1be2a3d263d68acb4a87` with `[skip ci]`.
- **Proof source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8FifthMismatchBudget.lean`, 144 lines, verified Git blob `ea3255cc578f2e6be63629f4aa28a23d766d3f6b`. Prior source `P3ActualU8OriginalFifthPolicyPP.lean` was read, as were `P3ActualU8SmallNormLevel.lean`, `P3ActualU8RoughDeltaNorm.lean` and literal producer `P1OriginalHistoricalPhysicalCoefficient.lean`. Root/docs/packet/production AGENTS paths were queried and absent. Excluded full87 files were not edited.
- **Original paper pin:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; `manuscript-body.tex` lines 256–278 (same signed rho and exact coprime mean), 451–469 (sign-sensitive small attachment) and distribution module §4(F) lines 151–171. Mathlib pin unchanged `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### Actual new manuscript-internal reduction

Let `cFifth(d)` be the actual fifth-capped historical first-exit integer coefficient, and `cOther(d)` an explicitly integer-valued, one-bounded rough candidate on the SAME rough physical carrier `R`. Put `D={d in R: cOther(d) != cFifth(d)}`. The genuine built-in `roughCoefficientInt_abs_le_one` supplies the fifth coefficient bound, while the candidate needs its separate one-boundedness hypothesis. A new finite Lean proof-body establishes

```
sum_(d in R) |cOther(d)-cFifth(d)| <= 2 * #(D)
```

by discarding equal slots and bounding each unequal integer coefficient difference by two. The second actual theorem combines this with the *previous* genuine sign-sensitive small-Rosser `ceil(L)` estimate and the actual U8 sharp-K labelled complete signed PP:

```
|E_U8(Q,rhoOther) - E_U8(Q,rhoFifth)|
 <= #S_U8 * ceil(L) * 2 * #D.
```

Both real physical rho functions are obtained by attaching the SAME original minus/plus small-Rosser weights to their respective integer rough coefficients. This is a SAME-PHYSICAL-CARRIER comparison, not an asserted global final rho_T identification. It keeps original labels, possible repeated terminal primes, complete product and exact primitive mean without replacing any modulus or choosing coefficients separately for individual count terms. It is stronger than simply charging the cardinality of the whole rough carrier when there are few genuine coefficient disagreements. It does **not** prove #D small or even that the final global compiler satisfies the premise, and `ceil(L)` may be polynomial in N. No arbitrary-log PP gain is inferred.

### Checks and exact boundary

- GitHub source readback `ea3255cc578f2e6be63629f4aa28a23d766d3f6b`; no banned proof-escape tokens; lexical delimiter balance PASS. Two `#check` declarations registered in `VERIFY.lean`, not executed.
- Independent finite exact integer disagreement scan: 810/810, zero failure. Independent exact-scaled signed-PP toy model: 900/900, with 1,600 negative physical coefficient instances, 18,000 repeated-prime tagged occurrences and 432 instances with complete product equal to target. It uses toy signed small weights and same q/primitive mean; it neither executes the actual fifth producer nor proves the analytic estimate.
- **NOT RUN:** Lean, Lake, CI, kernel replay, transitive axiom audit, Codex, heavy producer. Source candidates remain uncompiled and kernel-unverified; no new green node.
- `EXTERNAL_INPUTS.json` unchanged at blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: (M) merely registered and not implemented or invoked as an axiom. No production, manuscript, toolchain, PR, main branch, other automations or excluded 87-domain modifications.

**Next precise entry:** Identify the global final compiler's integer rough coefficient and the actual licensed physical rough carrier. Verify one-boundedness and control the exact disagreement set D relative to the literal fifth policy, or derive a genuine cancellation bound when D is not small. An unsigned cardinality criterion with a potentially polynomial `ceil L` does not pay the required absolute arbitrary-log PP estimate. W_T source-integrated Fourier L1/H/Fubini uniformly in T and m(N), full marked/HB, complete-product=T arithmetic, causal whole boxes, empty Gamma and high-rank/enhanced branches remain internal obligations. P3.6 **YELLOW**.

## Successor P3.6 SOURCE_ONLY — actual first-exit Möbius support mismatch (2026-11-08 UTC)

- **Verified GitHub baseline:** `d4313bda00bd6d44e9fe8d251144f4e95f371e93`; branch `chatgpt/p3-internal-original-w-20261105`. Before the proof commit and again on proof readback the branch head was checked. No concurrent branch movement was observed in those checks.
- **Real source commit:** `59e180f21f0c10819cedd79f3e62d08cef292f65` [skip ci]. New proof `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8FirstExitSupportDelta.lean` (202 lines), Git blob `3718be60c8fd929ef064408e1f793ee9656aac26`. `VERIFY.lean` Git blob `0f18a88ed217bbca2c8824f77315670ca94166a6`; two new `#check` commands are registered but **NOT executed**. Handoff updates are a second [skip ci] commit with the branch head as the authoritative identifier.
- **Fixed manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` lines 256–280 and 450–479, and `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F), lines 151–171. Pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged.

### Nontrivial actual finite refinement

The previous `original_fifth_u8_disagreement_PP` applied to any separately one-bounded integer rough candidate and charged *two* per coefficient disagreement. The actual `FirstExitGenericModuli.firstExitRetainedCoefficient` is more rigid: for any genuinely retained first-exit policy `P` on the SAME original finite `roughPrimeUniverse`, its coefficient is literally

`c_P(b) = if b in firstExitRetainedModuli(P) then moebius(b) else 0`.

Consequently two such policies cannot assign opposite nonzero signs at a common modulus. With `S_other` and `S_fifth` their actual support sets and a fixed permitted common rough carrier `R`, put

`D = {b in R : (b in S_other and b notin S_fifth) or (b in S_fifth and b notin S_other)}`.

New source-level proof `firstExit_rough_delta_le_support_mismatch` shows `sum_(b in R) |c_other(b)-c_fifth(b)| <= card D`, **not** `2*card D`. This is a sharper genuine same-carrier statement for first-exit producers, with no assumption that a separately supplied arbitrary integer compiler is one-bounded.

`original_fifth_u8_firstExit_support_mismatch_PP` uses the literal original fifth `finalPolicy`, real small Rosser plus/minus attachment, existing genuine U8 sharp-K labelled original rank-three source, and the prior `ceil L` budget. It yields

`|E_U8(Q,rho_other)-E_U8(Q,rho_fifth)| <= card(arithmeticTriples N) * ceil(L) * card(D)`.

Here `Q` is the SAME actual small/rough physical carrier for both terms and each `rho` is attached through the SAME true small Rosser signed weights. Original complete products, repeated `p2=q` labels, signed coefficients and exact coprime mean are untouched. This is a coefficient stability result, not a bound on the individual analytic PP errors and not a final causal compiler identification.

### Checks and unresolved boundary

- New source and VERIFY were read back from GitHub, exact blob IDs above. Static banned proof escape tokens: 0. Parenthesis/bracket/brace lexical balance: PASS. VERIFY imports precede `#check`.
- Independent deterministic finite Mobius-sign model: **1,000 / 1,000** support-pair checks with no failures; 2,518 common-support occurrences tested. These are standalone toy sets, NOT actual frozen policy enumeration, Rosser producer execution, Lean, or kernel verification.
- **NOT RUN:** Lean, Lake, kernel replay, CI, full transitive axiom audit, Codex, heavy producer. The two Lean theorem bodies remain SOURCE_ONLY with possible elaboration errors and uncompiled imported predecessors; no new green node.
- `EXTERNAL_INPUTS.json` unchanged at exact blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: medium estimate (M) recorded by source/version/exact conditions/call site **ONLY**, not implemented, axiomatized or invoked in this source. No new axioms or surrogate analytic PP hypotheses.
- No production, manuscript, main, toolchain, PR, other-task, or excluded full87 dynamic-parent files changed. The complete original final integer `rho_T` and licensed physical `Q_T` remain unknown; the new arbitrary other policy is NOT asserted to be that final compiler. The support XOR may be large, and `ceil(L)` can be a positive power of N, so arbitrary logarithmic PP saving remains unproved.

**Next precise internal entry:** identify a non-excluded genuine compiler policy and prove a real structural/signed bound on the actual support symmetric difference with the original historical fifth policy. Do not assume mismatch smallness from a set name. Separately: original physical `W_T` admissibility and uniform Fourier L1/H/Fubini in growing m(N), HB all original sources, exact complete product=T, mixed shifted moments, causal whole boxes, empty Gamma, high-rank/enhanced and final same-rho PP remain internal. Overall P3.6 YELLOW; this limited proof source BLUE only.

## Successor P3.6 SOURCE_ONLY — actual signed first-exit rough-response U8 (2026-11-08 UTC)

- **Actual checked baseline:** `241e383616be04c04a6416efbe7c41f8e16efb04`, branch `chatgpt/p3-internal-original-w-20261105`; **source commit**: `b3341b6e80a446f270711d978721994b3fad5c7c` with `[skip ci]`. No branch move was observed at the source write lease and its subsequent readback.
- **New source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8FirstExitSignedResponse.lean`, **191 lines**, Git blob `ab51a4f64ae737c60230f9aa244bf73bb1b7f79b`. Updated `VERIFY.lean` Git blob `f62772a0fb7527b43f2c0817f153d24117a54858`: 61 imports precede all 355 audit `#check`; 3 new declarations are registered, **never executed**.
- **Fixed manuscript**: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` around lines 256–280 (finite compilation, positive/negative small-Rosser attachment), 450–479 (exact signed PP and primitive-coprime mean), and `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F), lines 151–171 (Fourier, physical tail). Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged.

### New nontrivial exact finite arithmetic identity

For each literal first-exit policy P on the **same** roughPrimeUniverse, its integer coefficient is exactly `mu(b)` on `S_P=firstExitRetainedModuli P carrier`, zero off `S_P`. Define the actual physical **signed** source response of the rough modulus b:

`R_U8(b)=sum_(a in actualSmallRosserSupport) signAttachedCoefficient(mu(b),betaMinus(a),betaPlus(a)) * [A_U8(a*b)-B_U8(a*b)/phi(a*b)]`.

Here `A_U8(q)` is the complete original labelled sorted `arithmeticTriples N` congruence mass, `B_U8(q)` is its exact coprime mass; the same original physical modulus a*b appears in both. There is no restriction or renormalization by individual root fibres.

The new `firstExit_physical_signed_response` uses already-implemented *unique small/rough product factorization* and the actual sign-sensitive attachment to obtain an exact sum by b over the actual retained support; **both signed beta weights are retained**. Then `firstExit_physical_signed_support_difference` proves for any two genuine first-exit policies P1/P0 (same rough, small and physical carrier):

`E(P1)-E(P0) = sum_(b in R ∩ (S1\S0)) R_U8(b) - sum_(b in R ∩ (S0\S1)) R_U8(b)`.

The new `original_fifth_u8_signed_support_difference` specializes to the *literal original historical fifth* `P1OriginalHistoricalPhysicalCoefficient.finalPolicy` and the real original `P5U8SharpKSource.physicalWeight` / `Part3.primeProductSignedError 3 N N`. Compared with the predecessor's `#arithmeticTriples * ceil(L) * #support-XOR` upper bound, the full signed arithmetic response remains visible for future cancellation. **No cancellation estimate is claimed**; the other policy is not identified with a final global compiler.

The identity preserves the original rank-three ordered labels and possible p2=q diagonal, exact primitive-coprime means, complete physical products, original minus/plus small Rosser sign switch, and the same Q for both coefficients. It neither grants the other policy the pointwise majorant nor proves that the non-smooth U8 indicator belongs to the admissible smoothed PP class.

### Checks and limits

- Full source and VERIFY read back directly from the pushed source commit with the exact Git blobs above; forbidden proof escape token scan = **0**, lexical delimiter stack = **PASS**; VERIFY import order **PASS**. No AGENTS.md at checked root, ImbalancedChen, docs, source-only and packet paths.
- Independent Python **exact Fraction** finite regression: **2,400/2,400** signed identities, zero mismatches. Includes 2,176 tests with positive oriented mismatch set, 882 with negative oriented mismatch set, 2,164 nonzero signed deltas, repeated prime labels and 12,000 occurrences of p2=q. The toy has 16 distinct physical moduli, honest phi/coprime mass and signed small weights. It is **NOT** execution of the true first-exit producer, real Rosser weights, Lean declarations or the real manuscript estimate.
- **NOT RUN**: Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex, heavy producer. The three new declarations are SOURCE_ONLY, may fail elaboration, and create **no GREEN** status.
- `EXTERNAL_INPUTS.json` unchanged Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: restricted medium estimate (M) remains exact-version/hypothesis/call-site **RECORD ONLY**, not implemented or axiomatized. No new axioms, no toolchain/lockfile, production, manuscript, main, other automation or excluded full87 edits.
- **Next exact entry**: identify a permitted non-excluded real causal comparison policy and control these two actual signed rough-response sums by source-specific arithmetic, rather than assuming the support XOR is small. Independently discharge original W_T ContDiff/integrated derivative uniformity in T and growing m(N), all marked/HB source families, complete-product=T exception, nonzero shifted divisor moments, empty Gamma, high-rank/enhanced and actual same-rho arbitrary-log PP. Overall P3.6 YELLOW.


## Successor P3.6 SOURCE_ONLY — actual U8 full prime-plus-unit first-exit response (2026-11-08 UTC)

- **Verified branch baseline:** `de435c90c888a03469e5ef932ca8f211f012a1a7` on `chatgpt/p3-internal-original-w-20261105`. Actual [skip ci] proof commit `27963e7a483c3b60fb5dd5e10f9a769c1519fed4`; GitHub fast-forward readback checked. New file: `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8FirstExitPrimeUnitResponse.lean` (163 source lines, Git blob `b6e970e064cedebf713b58ffd028bb7443fea797`). `VERIFY.lean` blob `7a8288c0b9dc2e4b734f877ab6dcbf3e893c2ec1` has 62 imports before 358 registered #checks; 3 newly registered checks **not executed**.
- **Manuscript pin:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`. `paper/source/manuscript-body.tex` lines 256–280 (exact same signed rho/coprime mean), lines 450–479 (sign-sensitive attached physical coefficient); `paper/source/modules/distribution-prime-product-completion-20261010.txt` §1 (PP) and §4 (F). Mathlib pinned `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` unchanged.

### Actual manuscript-internal increment

Prior `P3ActualU8FirstExitSignedResponse` preserved the original U8 rank-three sorted labelled prime triples, including the inclusive p₂=q boundary, but did **not** combine the separately recorded original quotient-one pair family. The new `actualU8UnitSignedKernel` is the genuine `currentChenUpsilon8UnitFibres N` rank-two labelled congruence mass minus its exact coprime mean, divided by the genuine physical totient. The theorem `actual_u8_prime_unit_same_rho_signed_kernel` combines this with the original sharp-K rank-three signed `Part3.primeProductSignedError` using **one unchanged physical Q/rho** and **one complete q-sum**, without merging their different source ranks, labels or complete products. `prime_unit_signedRoughResponse_split` preserves the exact sum of the two signed small-Rosser responses before any triangle inequality.

For the **literal** historical fifth first-exit policy, comparison with any other first-exit policy on the same original roughPrimeUniverse now yields the exact SOURCE_ONLY identity:

```text
E_U8_prime+unit(rho_other) - E_U8_prime+unit(rho_fifth)
  = sum_(b in R ∩ (S_other \\ S_fifth)) R_prime+unit(b)
  - sum_(b in R ∩ (S_fifth \\ S_other)) R_prime+unit(b).
```

The original small Rosser minus/plus selection is unchanged, and both source discrepancies retain their **exact** primitive coprime means. No fibrewise Theta condition is added. This **does not** identify the other policy with the final global causal compiler, prove cancellation, admit the non-smooth U8 indicator into the smooth PP class or establish any arbitrary logarithmic error. The original unit-pair *count* can be paid separately by the pre-existing direct power-error bound.

### Checks and remaining obligations

- Source and VERIFY Git blobs were read back. Forbidden proof-escape tokens = 0; static delimiter scan PASS. Independent exact **integer-scaled** finite algebra model: **1280/1280** success, 0 mismatch, 596 positive / 586 negative signed comparisons, including Möbius-zero rough terms and separate triple/pair kernels. This does **not** execute the real first-exit producer, Rosser weights or Lean.
- **NOT RUN:** Lean, Lake, CI, kernel replay, full transitive axiom audit, Codex or heavy producer; no new GREEN. All three new declarations and their prior imports remain source candidates with elaboration risk.
- `EXTERNAL_INPUTS.json` unchanged at blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: restricted estimate (M) remains **REGISTER ONLY**, source/version/hypotheses/call-site recorded; never implemented or introduced as an axiom. No other production, main, manuscript, PR, toolchain, other automation or excluded full87 node changes.
- **Next:** identify a genuinely licensed non-excluded causal policy and derive a real arithmetic estimate for both oriented signed sums (or bypass the unit part with its direct-count payment); independently finish original W_T smoothness and log budgets uniform in T and m(N), Fourier L1/H/Fubini, complete modulus arithmetic including product=T, all marked/HB atoms, empty Gamma, nonzero-shift moments and high-rank/enhanced. P3.6 stays **YELLOW**, the limited source candidate **BLUE**.

## Successor P3.6 — original fifth native U8 two-rank carrier transport (2026-11-08)

- Verified baseline: `e3dab5aa2da62da77937b6e8dfd22a68adfaf6e1` on `chatgpt/p3-internal-original-w-20261105`; the branch ref was checked before writing and the proof commit was pushed by expected-head compare-and-swap without force.
- Actual SOURCE_ONLY proof commit: `d8030fbf4ef3f299043d8dce9ecce00d21d0892a` with `[skip ci]`; new `P3ActualU8PrimeUnitNativeCarrier.lean` (168 lines; Git blob `8f9294b08674e20badbc286944e382f3b6278130`). `VERIFY.lean` blob `64fd2f83cf5a21e49125615cb98df4761fa1a053`; three new `#check` commands are **registered, NOT executed**.
- Original paper pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `manuscript-body.tex` around 257–280 and 450–479, distribution completion §4(F) 151–171. Fixed Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

### New source-level internal result (not an analytic PP saving)

The previous literal U8 prime-plus-unit signed response compared two first-exit coefficients **only on a larger common physical carrier**. The native historical fifth coefficient actually has its own `P1OriginalHistoricalPhysicalCoefficient.physicalModuli` and `.rho`, so a native-to-common transport for BOTH original source ranks was missing.

`prime_unit_zero_extension` transports the actual rank-three original sharp-K triples **and** the independent quotient-one prime pairs simultaneously from the original physical Q and real signed rho to a containing rough carrier. It reuses the previously proved-in-source generic labelled signed-distribution zero-extension for the pair and the previous true original U8 rank-three transport. The original complete products, distinct source ranks, labels/multiplicities, small Rosser +/- attachment, and **exact coprime means** are unchanged.

`original_fifth_prime_unit_zero_extension` specializes the transport to the literal original fifth-capped historical `finalPolicy` using the already defined integer-Mobius coefficient and the original `roughCoefficient_eq_fixed` / support-identification bridge. It assumes only that the common rough carrier contains the genuine fifth rough support. It does **not** assume that an arbitrary global compiler coincides with the fifth policy.

`original_fifth_prime_unit_native_offshift` composes this native transport with the pre-existing complete-product offshift equality. Thus the **native** historical fifth two-source signed error equals the **common** carrier's full labelled divisor/offshift, density and exact coprime correction expression, with no new analytic-error hypothesis. This is an exact finite arithmetic source bridge, not cancellation nor proof of the manuscript PP bound.

### Actual checks and environment

- GitHub proof+VERIFY file blobs were read back after the `[skip ci]` commit. Source lexical bracket balance PASS, forbidden proof escapes 0; proof declarations are registered after imports.
- Independent exact rational `Fraction` toy regression: **750/750** cases with original and larger rough carrier, duplicate separately labelled triple/pair occurrences and signed small-factor weights. Zero mismatches. These are toy models and do **not** execute real Rosser or the historical fifth policy.
- Pinned toolchain and manifest were read: `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Compilation is now **authorized** by the user, but **was not run**: this execution container has neither a `lean` nor `lake` executable, and the direct git network probe returned DNS resolution failure. No local verified compilation is possible in this environment without an existing pinned execution setup. **No CI was dispatched**, per task restriction. No kernel replay, full axiom audit, Codex, heavy producer or toolchain upgrade.
- `EXTERNAL_INPUTS.json` remains unchanged (blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`), (M) is **record only**. No new axioms or external results were implemented.
- No production source, frozen manuscript, global source, excluded full87 node, other automation work, PR or master was modified.

**Next precise entrance:** first map the SOURCE_ONLY dependency chain to an existing correct pinned Lean/Lake environment and elaborate this new native carrier transport, correcting concrete errors instead of adding unchecked interfaces. Mathematically this removes only the common-versus-native U8 pair/triple carrier discrepancy. The true final causal integer `rho_T` and physical `Q_T`, signed rough response saving, complete marked/HB/empty Gamma/high-rank sources, growing `m(N)` uniform original `W_T` Fourier bound and full-product `T` exception for other atoms remain INTERNAL YELLOW. No new GREEN node.


## Successor P3.6 — actual U8 strict-terminal prime-only PP counting reduction (2026-11-08 UTC)

- **Verified baseline:** `f6b9cbb48f2510b428660dd0a42c6f93c06fd3d0` on the existing unique P3.6 branch `chatgpt/p3-internal-original-w-20261105`; source commit `88b94a376f71b8a9bb0ca34e63abdbd41ce26de0` with `[skip ci]`.
- **New proof source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8StrictPrimePP.lean`, 182 lines, Git blob `2af339690e2b9a00e8ec9326e9c5873c0396415a`; `VERIFY.lean` blob `ca56462abb4da7ff72329fee05606d9ffc0f0dea`. Three named theorem candidates and their three audit `#check` lines were actually committed, not executed.
- **Fixed manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; `paper/source/manuscript-body.tex` §2 distribution from local to prime products (lines 257–280) and finite compilation (450–479), `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4(F) lines 151–171. Fixed Lean `leanprover/lean4:v4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, no upgrade.
  
### Actual mathematical delta

Unlike the preceding source, which kept both triple/quotient-one families as an exact signed distribution on a common or native physical carrier, this packet **removes the inclusive terminal-prime diagonal from the ANALYTIC U8 counting PP obligation by paying its positive count directly**. The actual strict source is `P5U8SharpKSource.strictTriples N` with p₁<p₂<q; the actual diagonal remains `diagonalTriples N` with p₂=q, not an empty or discarded fibre.

The proof first uses `actual_u8_sum_partition` for the original labelled arithmetic triples and the genuine product-multiplicity identity `productWeight_sum` to give the exact original prime-mass partition. It then invokes the actual `p5z_labelledPrimeMass_le_main_add_errors` positive-family sieve majorant **only on strictTriples**. The inclusive diagonal is bounded by its real original cardinality, while the strict small-Goldbach-prime loss is bounded by the *full* source small-prime count. The latter deliberately allows overlap with the already paid diagonal; this is a harmless overestimate, not two disjoint counts being asserted.

For any one physical `Q : Finset ℕ` and one unchanged signed `rho : ℕ → ℝ` satisfying the genuine pointwise sieve majorant (no PP assumption), the new candidate proves:

```text
currentChenUpsilon8 N
  <= mass(strictTriples)*physicalDensitySum(Q,rho)
    + exactCoprimeCorrection(strictTriples,Q,rho)
    + signedPP(strictTriples,Q,rho)
    + #smallGoldbachPrimeTriples + #diagonalTriples + #unitFibres.
```

The two directly paid U8 errors `#small + #unit` already have a genuine source-count bound `o(H_N)`; the original `#diagonal` has `N^(2/3)` bound. The new eventually theorem splits an **arbitrary prior epsilon** into these two budgets before N, z, Q or rho are chosen. Thus the strict-only counting insertion has one common threshold independent of the physical coefficient. **This is not PP for the still-sharp strict indicator and does not identify its Fourier-smoothed W class.** The final global causal integer rho_T, true arithmetic signed-error saving, common physical and auxiliary levels, HB/marked/empty Gamma/high rank and full assembly remain unproved.

### Verification and trust boundaries

- GitHub readback at proof commit `88b94a376f71b8a9bb0ca34e63abdbd41ce26de0` confirmed exact 182-line source SHA `2af339690e2b9a00e8ec9326e9c5873c0396415a` and VERIFY blob `ca56462abb4da7ff72329fee05606d9ffc0f0dea`. The commit contains only the two intended task files and is a direct fast-forward child of the checked baseline. Forbidden proof escape scan: 0; lexical delimiter check passed; all imports precede all 364 registered `#check`.
- Independent Python exact-rational toy regression: 900/900 finite labelled/counting cases, with original strict/diagonal labels and deliberately signed rho on Q={1,2,3,6}; 776 cases had nonzero signed modulus discrepancy, 2,428 diagonal label occurrences. The tested pointwise majorant was independently checked on each finite N. This verifies a finite algebraic pattern, **not** actual selector/Rosser execution, Lean elaboration or an analytic estimate.
- Lean/Lake **NOT RUN**: the current container has no lean/lake executable and direct GitHub git DNS resolution fails. The user now authorizes local compilation in a pinned environment, but it was unavailable here. No CI, separate kernel replay, Codex, heavy producer or full axiom audit was launched. `#check` remains unexecuted; the new source has possible tactic/API/elaboration errors and cannot be green.
- `EXTERNAL_INPUTS.json` unchanged, Git blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: manuscript-external (M) remains **REGISTERED ONLY**, never implemented or added as an axiom. No manuscript, production module, excluded full87 parent/history node, main branch, PR, toolchain, other automation or external board change.

**Next exact entry:** In the first available pinned Lean environment, elaborate this specific three-theorem strict counting reduction and its direct dependencies before building further unchecked layers. Mathematically, identify the actual final causal `Q_T,rho_T` and produce genuine arbitrary-log signed discrepancy **for the strict prime-triple source after admissible smoothing**. Complete original `W_T` derivative/Fourier L1/H/Fubini uniformity in growing `m(N)`, whole-box causal selection, marked/HB family coverage, full product=T exceptions beyond these strictly sub-N U8 sources, shifted moments and high-rank/enhanced branches remain INTERNAL. P3.6 is **YELLOW**. New source is **BLUE/SOURCE_ONLY**.


## Successor P3.6 — strict labelled Part3 physical PP (2026-11-08 UTC)

- **Baseline and actual source commit:** `2f8f1c4fe57063a0eeb0fd75f95f14ca7d2e1336` → `4edc2b155bf7dbeaa31c0d2994c3552e065ad615` on the existing P3.6-only branch `chatgpt/p3-internal-original-w-20261105`; proof file `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8StrictPhysicalPP.lean`, 224 lines, Git blob `8bf503ebe701b95ca5c1705353b35d326af82d72`. Source commit is a direct fast-forward child with `[skip ci]`; the check/handoff commit is a separate fast-forward.
- **Fixed frozen manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`. Relevant statements: `paper/source/manuscript-body.tex` lines 257–280 (PP: same signed physical rho, fully labelled products, exact coprime mean, smooth source class), 450–479 (compiled physical upper coefficient); `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4(F), lines 151–171 (quantitative Fourier and arithmetic-tail obligations).

### Proven mathematical identity / Lean candidate scope

The previous strict-prime counting packet left the remaining PP term as `p5z_labelledDistributionError (strictTriples N) product ... N Q rho`. The real analytic interface is `Part3.primeProductSignedError 3 N N Q rho W`, requiring an explicit genuine labelled rank-three weight. The existing upstream `P5U8SharpKSource.physicalWeight N` includes the `p₂=q` terminal diagonal, **so it cannot be reused for the strict-only PP term**.

This packet defines `strictPhysicalWeight N` on the original `Part3.labelledPrimeTuples 3 N` as the literal indicator `physicalInverse u ∈ strictTriples N`. Using the actual `natCoord`, `physicalInverse` and original prime-cap source, `strictPhysicalWeight_sum` supplies a label-level finite bijection for every `F : ℕ → ℝ`; this construction deliberately does **not** factor the strict predicate through a product-value deduplication. The weight has absolute bound one and preserves each original `p₁<p₂<q`, full-product `<N`, centre coprimality, and `N^(417/5000)` individual lower cutoff.

The exact same `Q : Finset ℕ` and signed `rho : ℕ → ℝ` occur in each congruence term and the **unmodified primitive coprime mean**:
```text
p5z_labelledDistributionError (strictTriples N) product (fun _ => 1) N Q rho
  = Part3.primeProductSignedError 3 N N Q rho (strictPhysicalWeight N).
```
The final two new counting candidates insert that exact rank-three Part3 expression into the existing finite and eventual U8 strict-prime reductions; diagonal `p₂=q`, small Goldbach prime and unit quotient counts remain separately direct-power paid, not dropped.

This is a **finite source identification**, NOT the required manuscript `O_A(N/log^A N)` signed discrepancy. A sharp `strictPhysicalWeight N` has not been shown to equal an admitted smooth original `W_N`; this proof does not identify the final causal integer `rho_T` or its physical `Q_T`, and does not resolve the original Fourier/HB/empty Gamma/arithmetic tail obligations.

### Checks and trust boundaries

- GitHub proof file was read back as blob `8bf503ebe701b95ca5c1705353b35d326af82d72` at commit `4edc2b155bf7dbeaa31c0d2994c3552e065ad615`. Static banned proof-escape scan: zero. Lexical delimiter counts balanced (not syntax or type checking). New import and eight `#check` expressions are registered in `VERIFY.lean` but have NOT been executed.
- Independent exact rational finite regression: **500/500** model cases; 9,239 strict labels, 4,016 separately retained diagonal labels, and 2,971 nonzero signed-modulus discrepancies. This validates finite algebraic patterns only, **not actual Lean code, original producer execution or analytic estimates**.
- Compile permission remains in effect, but in this container `lean` and `lake` are absent; GitHub git DNS is unresolved. No Lean/Lake command was executed. Pinned versions remain Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; not upgraded. No CI, independent kernel replay, Codex, producer or transitive axiom audit was run. **SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED**.
- `EXTERNAL_INPUTS.json` retained unchanged blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`: (M) remains REGISTERED ONLY, not implemented or assumed as new axiom. Excluded full87 dynamic-parent node, frozen manuscript, production code, main branch, other task files and external board were not modified.

**Next precise entry:** first elaborate this specific strict rank-three weight identification in an existing pinned Lean environment, repairing actual errors before extending the proof stack. Then identify original smooth `W_T` admissibility (quantified mixed derivatives and Fourier L1/H at growing m(N)) and genuinely bound the complete physical PP discrepancy with the final causal integer rho and the same physical modulus family. No new GREEN nodes; P3.6 remains YELLOW.

## Successor P3.6 — strict U8 smooth-weight selective physical boundary (2026-11-08 UTC)

- **Restored and checked baseline:** `ba39dfa6013f027ab868c5543f3c8f7809e8827c` (unique P3.6 branch `chatgpt/p3-internal-original-w-20261105`). Proof commit **`3fbcbcca5296ffd1a0ef2a7977fb14bafc3f0a6a`** with `[skip ci]`, exact file blob **`682622dc7678cc13246dce39dfad0526bfa9d74b`**; VERIFY blob **`80e8064da754ca4c078deb294445aee196b7ceea`**. No concurrent branch advancement at the commit lease.
- **New source:** `P3ActualU8StrictSmoothBoundary.lean`, 147 text lines, two local kernel definitions and three named theorem candidates: `physicalKernel_abs_le_budget`, `strict_minus_smooth_exact`, and `strict_minus_smooth_boundary_bound`. All declarations registered but **NOT Lean-elaborated**.
- **True mathematics:** On the original Part3 rank-three labelled-prime carrier with literal `strictPhysicalWeight N`, any proposed replacement `W` has an exact signed PP difference **inside the full physical modulus sum**, using the very same `Q,rho,N`, ordered full labelled product and original coprime mean. The pointwise discrepancy kernel is dominated by the sum of the exact congruence indicator and coprime indicator divided by the true totient. If `W = strictPhysicalWeight` off a specified boundary set `B` on actual prime labels, the difference is bounded by the explicit **B-only** weighted physical modulus sum: `sum(q in Q) |rho(q)| * sum(u in labels intersection B) |strict(u)-W(u)| [1_(product=N mod q)+1_((product,q)=1)/phi(q)]`. No fibre-relative Theta, hidden signed cancellation, modulus deduplication, q=0 special lemma, or alternate rho.
- **Precise limitation:** Neither the existence of a globally geometric C-infinity W satisfying the exact off-B equality, nor small weighted B mass, nor `O_A(N/log^A N)` is proved. In particular the sharp original strict selector contains arithmetic coprime/order/target gates and cannot automatically be declared smooth; a small wall volume alone does not pay the arithmetic discrepancy. This packet **does not** instantiate the final causal integer `rho_T` and original `Q_T`.
- **Frozen manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `manuscript-body.tex` lines 257–280 (smooth PP, same rho, no added arithmetic filter) and 450–479 (compiled upper physical coefficient), `distribution-prime-product-completion-20261010.txt` §4(F) lines 151–171 (Fourier/tail after complete modulus sum). Same fixed toolchain: Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- **Checks actually executed:** GitHub branch compare-before-write and source/VERIFY SHA readback; finite exact Fraction regression 600/600, including 358 nonzero signed changes, signed rational rho, distinct labels with equal products, exact totients and arithmetic mean, and independently chosen B. This is ONLY a model of the finite algebra. Source-only prohibited-escape scan was zero; independent source delimiter check was textual only; VERIFY 66 import lines and 377 registered `#check` lines, **never executed**.
- **Unexecuted:** Lean, Lake, kernel replay, transitive axiom audit, CI, Codex, heavy producer. Current available container lacks `lean`/`lake` and direct GitHub git access fails DNS; the connector can read and commit but **cannot compile**. Treat ALL three theorem candidates as SOURCE_ONLY, with remaining elaboration risk. No new GREEN.
- **External boundary:** `EXTERNAL_INPUTS.json` unchanged (blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`); (M) remains RECORD_ONLY_NOT_IMPLEMENTED_NOT_AXIOM. No external estimate, replacement axiom, excluded full87 node, frozen manuscript, main branch, production source, PR, other tasks, or board modified.

**Next exact entrance:** verify the actual module's elaboration with pinned Lean after staging dependencies in an isolated mapping, repairing type errors; then identify a *genuine* smooth original geometric W and a quantitatively small **physical arithmetic weighted** boundary set. Only after this can this comparison transfer a proven smooth PP estimate to the sharp strict U8 source. In parallel remain final original integer rho_T/Q_T, all marked/HB/empty Gamma/high-rank source admission, nonzero shifted mixed moments, full product=T exceptions and growing m(N) uniform D/Fourier. P3.6 YELLOW; this restricted source packet BLUE/SOURCE_ONLY.

## Successor P3.6 — strict U8 boundary by original labels, exact full-product exception (2026-11-08 UTC)

- **Actual resume/head:** `fa2317ae0664d72ecd477a42093053f06afee26c` on existing unique branch `chatgpt/p3-internal-original-w-20261105`. GitHub fast-forward proof commit **`60102fc4cba00ece15d6d598b6a086ac3d73a7fe`** (`[skip ci]`); new `P3ActualU8StrictBoundarySourcewise.lean`, 143 lines, Git blob `adaf2a0773739db036f85c3e84c83c2eb7d0e5d4`; `VERIFY.lean` blob `a3fa130db55d5e467378db17de50d166680b2452`. Five named SOURCE_ONLY theorem candidates were registered but have NOT been elaborated.
- **New mathematical scope (not a new distribution saving):** The actual strict U8 weight is zero when its *complete* original triple product is N, because any nonzero strict source has `labelledProduct u < N`. Consequently, if a proposed W agrees with strict sharp weight outside B, every genuinely nonzero target-product label of W lies in B. This locates the exceptional term without silently defining tau(0) or claiming it small. For the SAME `N,Q,rho`, the previous physical arithmetic boundary norm is then exactly reordered by original prime labels *after the full q sum*:
  `sum(q in Q) |rho(q)| sum(u in labels∩B) |sharp(u)-W(u)| Kbud(q,u) = sum(u in labels∩B) |sharp(u)-W(u)| sum(q in Q) |rho(q)| Kbud(q,u)`.
  The per-label complete physical response is split into (i) the exact congruence indicator and (ii) the **original** coprime indicator divided by `phi(q)`. No labels or equal-product occurrences are collapsed, and the signed rho remains identical in the two underlying PP errors. This pinpoints the two genuinely distinct pending arithmetic payments, not a fictitious small geometric-wall mass.
- **Precise old dependencies:** `P3ActualU8StrictPhysicalPP.strictPhysicalWeight_support_data` and `P3ActualU8StrictSmoothBoundary.strict_minus_smooth_boundary_bound`. The new source contains only finite rearrangement and the literal strict <N gate; no new external theorem, replaced axiom, target-equivalent premise, or separate modulus coefficient. The final `rho_T,Q_T` is still **not identified** and a geometric admissible W with quantitatively small physical arithmetic B mass is still **not constructed**.
- **Pinned manuscript:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`. `paper/source/manuscript-body.tex` lines 257–280 (smooth PP with exact mean and no added arithmetic filter) and 450–479 (same compiled physical coefficient); `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4(F) lines 151–171 (post-modulus Fourier/tail and full-product=T exception). No manuscript changes.
- **Environment/checks actually executed:** GitHub branch equality against the proof baseline before writing, protected fast-forward commit and exact proof/VERIFY blob readback; JSON parse for current registry; textual delimiter balance (parentheses 85/85, brackets 5/5), zero proof escape tokens in the new source, 67 import lines before 382 registered `#check` lines (not run). Independent Python `Fraction` regression **700/700** finite signed test configurations, including 21 target-equal-N nonzero smooth-weight occurrences necessarily placed in B and 269 negative signed discrepancies. This validates only elementary finite algebra, **not** genuine Lean elaboration, actual source producer, analytic saving, or uniform asymptotics.
- **NOT EXECUTED:** Lean/Lake (no pinned Lean or Lake binary installed in the available execution container), CI (forbidden), separate kernel replay, full transitive axiom audit, Codex, heavy producer. Pinned `leanprover/lean4:v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, goldbach `09b97db5764ade1246bfb77206baa1b124760958` unchanged. There may be elaboration/API errors in the new candidate. No GREEN status is warranted.
- **External boundary:** `EXTERNAL_INPUTS.json` blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab` unchanged; (M) **REGISTERED ONLY**, no implementation/new axiom. The excluded full87 dynamic parent/history node, production modules, other task branches, master, PR, CI and boards were not changed.

**Next exact entrance:** Pin-matched targeted Lean elaboration of this module and its source-only dependencies, fixing actual failures first. Then distinguish the complete labelled congruence boundary response from the exact coprime mean, establish the actual arithmetic shifted-divisor and full-product=N payments, and construct admissible original geometric W with uniform mixed/Fourier bounds for growing m(N). The final causal integer rho_T and physical Q_T and all marked/HB/empty-Gamma/high-rank coverage remain YELLOW. P3.6 overall YELLOW; this restricted packet BLUE/SOURCE_ONLY.

## Successor P3.6 — signed exact-target diagonal extraction on original labels (2026-11-08 UTC)

- **Verified resume baseline:** `74b3eee5cec83951631e4b7f7e700d4c2feb4f71` on the unique P3.6 branch `chatgpt/p3-internal-original-w-20261105`. No writer drift at both pre-write checks. New proof commit **`787976dd72cc0b76c24f696532af540bf4ad03e5`** (`[skip ci]`).
- **New source:** `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualU8ExactTargetResponse.lean`, 163 text lines, Git blob **`bbea7fc0ec895e6fbbc188bb357a44f49e249762`**. `VERIFY.lean` blob **`338f7ee0ada42ec5c46fe0af87e5128f926f6114`**, with 68 imports before 389 registered `#check` commands (NOT executed). Two finite definitions and five candidate theorems.
- **Paper pin:** `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` lines 257–280 and `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4(F). Toolchain pin unchanged: Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

### Actual finite mathematical progress

The earlier source-wise boundary packet only *located* the complete-product=N exception. The new packet evaluates its complete signed physical congruence-minus-coprime kernel **exactly**, with no termwise absolute value: for each original rank-three labelled u with `labelledProduct u = N`, `Nat.ModEq q N N` is true for **every physical q**, including Lean's totalized zero-modulus convention. The old strict-source lemma supplies `strictPhysicalWeight N u = 0`. Define

```
R_target(N,Q,rho) =
  sum_(q in Q) rho(q) * [1 - 1_((N,q)=1)/phi(q)].
```

Then the full modulus sum of the original STRICT-minus-smooth kernel on the exact-target labelled carrier factors as

```
sum_(q in Q) rho(q) * sum_(u in labels, P(u)=N)
    [strict(u)-W(u)] * K_q(u)
  = -[sum_(u in labels, P(u)=N) W(u)] * R_target(N,Q,rho).
```

If W agrees with strict off the actual labelled boundary B, the factor in square brackets is **exactly** the W mass on `labels ∩ B ∩ {P=N}`. `targetResponse_split` also identifies `R_target = sum_q rho(q) - sum_q rho(q)*1_coprime(N,q)/phi(q)`: this is the complete physical divisor response at zero shift minus its literal primitive mean, not a made-up tau(0) expression. The original physical Q and signed rho are shared throughout, and distinct labels with equal product remain distinct.

This is a narrower actual algebraic advance than a full PP estimate: neither `R_target`, the target boundary W mass nor their product has been shown power-small or arbitrarily log-small. It is not a new external assumption, and does not identify the final causal `rho_T,Q_T` or construct an admissible geometric smooth W_T.

### Checks and precise trust boundary

- Source and VERIFY Git blobs were read back at the exact proof commit; current EXTERNAL_INPUTS.json blob remains **`8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`**. New source: forbidden proof escape tokens **0**, lexical delimiter balance **PASS**; registry JSON parse **PASS**.
- Independent exact Python `Fraction` finite model: **1,400/1,400** signed factorizations and off-B target mass checks, including **1,323** nonzero diagonal signed values, **387** cases with q=0, and **1,238** cases with repeated complete products on distinct labels. It confirms only elementary finite identities under the stated model assumptions.
- Current isolated container probes: `command -v lean` exit **1** and `command -v lake` exit **1**, i.e. matching binaries absent. **NOT RUN:** Lean/Lake compilation, elaboration of seven registered names, CI, independent kernel replay, full transitive axiom audit, Codex, heavy producer. No declaration is upgraded to COMPILED or GREEN.
- External (M) remains **REGISTERED ONLY** in `EXTERNAL_INPUTS.json`; no new analytic theorem implementation or surrogate axiom. Unchanged: the frozen manuscript, production modules, excluded full87 parent/history task, other branches, CI, PR and external board.

**Next precise entry:** first compile and repair these exact declarations in a pin-matched isolated Lean environment. Then control the real target boundary W-mass times the exact signed zero-shift physical response, separately from the off-target congruence/coprime arithmetic boundary. Construct a truly admissible original W_T with uniform derivative/Fourier/H-box bounds for growing m(N); finish actual same-causal-rho Q_T PP on all admitted marked/HB/empty-Gamma/high-rank sources. P3.6 stays YELLOW, this limited proof source BLUE/SOURCE_ONLY.

## Successor P3.6 — even geometric rank-three target diagonal vanishing (2026-11-08)

- Actual checked baseline: e0cad461048eb873df8ce0cfa4091aaca3dc269d on chatgpt/p3-internal-original-w-20261105. Proof commit 17cfa831ffe6f4de4fe09849a172afe46981d184 [skip ci], new P3ActualU8EvenGeometricTarget.lean (blob 18f903cf84fdad5eaccaf7fda64c75fb4a93ba38), VERIFY.lean (blob 505301391bc2998385d1007a219d6b2d297064ed); 3 new SOURCE_ONLY candidate declarations.
- Mathematical improvement: the frozen manuscript permits smooth geometric weights on original labelled primes with each nonzero slot at least c*N^a, no additional arithmetic filter. When 2<c*N^a, all actual labelled primes in the support are >2 and hence odd. Thus for even Goldbach target N their complete rank-three product is odd and CANNOT equal N. This proves that the weighted target-product label sum is literally zero, so the previous EXACT signed factorization gives ZERO complete-target discrepancy with unchanged physical Q/rho, for ANY signed coefficients. No bound on the possibly large targetResponse is assumed. Distinct labels are retained.
- Scope and unpaid obligations: a CONDITIONAL source-level theorem for rank-three original prime labels; the actual original W_T lower support and a common eventual N threshold for fixed positive c,a remain to be connected, as do smooth mixed-derivative/Fourier conditions. This does NOT apply to arbitrary HB integer factors, or bound the off-target arithmetic boundary, or identify final causal rho_T/Q_T. It avoids inventing a parity mask, an analytic PP saving, a target-equivalent premise or an axiom.
- Original inputs inspected: manuscript @9731290e8f53cffda44129906cde6a965eaa869b, manuscript-body.tex lines 257–280 and distribution-prime-product-completion-20261010.txt §4(F) lines 151–171; actual production CurrentChenUpsilon8SharpKPhysicalPP.lean triple-product identity; pinned Mathlib Data/Nat/Prime/Basic.lean at e4c9178 explicitly contains Prime.odd_of_ne_two and not_odd_iff_even. Source inspection is NOT Lean typechecking.
- Actual checks: GitHub branch ref and proof/VERIFY blobs read back; static source escape scan 0 and delimiter scan PASS; independent exact Python Fraction 500/500 even-N finite models (36 target labels requiring factor 2 excluded by geometric support, across 7 samples with target labels); q=0 and signed physical coefficient cases. Not actual Lean or native producer. Current environment has no lean/lake and GitHub git DNS fails. NOT RUN: Lean/Lake compilation, separate kernel replay, CI, full transitive axiom audit, Codex, heavy numerical producer. No new GREEN.
- External input boundary unchanged: EXTERNAL_INPUTS.json blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab, (M) record-only. No manuscript, production, main, PR, other branch, excluded full87 node or board edits.

Next concrete entry: use a version-matched Lean/Lake environment to elaborate this 3-theorem module and dependencies and fix any errors. Then establish actual W_T geometric support, 2<c*N^a eventually with the correct uniform quantifier order, and apply this exact-zero target payment ONLY to the genuine rank-three prime source. Complete off-target shifted divisor/physical modulus boundary, W_T uniform Fourier budget and all final same causal rho_T/Q_T source families. P3.6 YELLOW; restricted new code BLUE/SOURCE_ONLY.

## Successor P3.6 — all original-prime ranks: even target-product fibre vanishes (2026-11-09 UTC)

- **Restored exact HEAD**: `9f796a034c47b0bd0998f165c039e19ab430e8cf`, task branch `chatgpt/p3-internal-original-w-20261105`; previous actual handoff was `9f796a0`, not the original `de582e6`.
- **New proof commit**: `42839b7f99b0189e31b08c5fc0a012d46b45e824` with `[skip ci]`; exact new source blob `8e58d288d7c425985e0004295e0388c739a15785`.
- **File**: `docs/source-only/20261105-p3-fourier-coordinate-ibp/P3ActualAllRankGeometricTarget.lean`, 121 lines, four candidate theorems; no production modules modified.
- **Source definitions actually read**: `ImbalancedChen/Part3DistributionTargets.lean` defines `labelledPrimeTuples k P`, `labelledProduct`, and the literal `primeProductSignedError k P N Q rho`. Root `AGENTS.md` was absent at the checked branch, consistent with predecessor packets.
- **Frozen manuscript**: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` lines 254–274 and `paper/source/modules/distribution-prime-product-completion-20261010.txt` §§1,4. Pinned Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
  
### Actual mathematical increment

Prior rank-three U8 proof showed the target product is impossible on an even N when every original prime coordinate of W is strictly above 2. This round **removes the rank=3 restriction** and proves the finite all-rank parity induction on the *original* Part3 prime-label carrier, including empty rank. For any fixed k, cap P and even N, if a genuine geometric weight W can be nonzero only where all original prime coordinates are at least `c*N^a>2`, then `W(u)=0` whenever `labelledProduct(u)=N`. In particular:

```text
sum_{u in labelledPrimeTuples(k,P), labelledProduct(u)=N} W(u) = 0
Part3.primeProductSignedError k P N Q rho
  (fun u => if labelledProduct u=N then W u else 0) = 0
```

Both identities keep original labels and occurrence multiplicity, complete prime-product scale, the same arbitrary signed physical Q/rho and literal coprime/totient mean. The latter is the real Part3 signed-error functional, **not** an artificial replacement metric. No new parity filter has been imposed on admitted W. This pays the complete-product=N diagonal **only for geometrically supported original prime-coordinate sources of any rank**. It does **not** pay HB integer slots (even factors are allowed), sharp-to-smooth off-target arithmetic boundary mass, or derive the true uniform W_T admissibility and threshold.

### Evidence and limits

- Exact branch HEAD read before the write; source file created successfully at commit `42839b7f99b0189e31b08c5fc0a012d46b45e824` and subsequently fetched with matching blob `8e58d288d7c425985e0004295e0388c739a15785`.
- Static banned proof-escape scan: zero; delimiter check: balanced. `VERIFY.lean` has four additional **registered, not executed** `#check` statements.
- Independent Python arithmetic regression: 230,942 labelled prime tuples over even N=2..80, k=0..4, with 111 target-product occurrences; no admissible nonzero target W. Independent exact Fraction randomized signed test: 600/600, 164 target labels, physical q including zero and arbitrary signed rational rho, all target-part responses zero. **These tests are not Lean elaboration or a mathematical proof.**
- Environment probe in the present execution container: neither `lean`, `lake`, nor `elan` is installed; direct git access failed DNS resolution. Hence **NOT RUN**: Lean, Lake, CI, independent kernel replay, transitive axiom audit, Codex and heavy producer. Every declaration is `SOURCE_ONLY_UNCOMPILED_KERNEL_UNVERIFIED`; no new green status.
- `EXTERNAL_INPUTS.json` unchanged, blob `8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab`. The external restricted medium input (M) remains RECORD_ONLY, not implemented and not an axiom.
- No excluded full87 parent/history node, other task, manuscript, main/master, production source, toolchain, CI configuration, PR or external board was changed.

### Next exact proof entry

1. Compile the four new declarations with the fixed Lean/Mathlib pins (in an isolated source-only import mapping) and repair any elaboration error; do not promote any of the preceding 100+ source-only modules automatically.
2. Produce a **real uniform original geometric W_T support contract** and one common large-N threshold with fixed c,a before N and all source labels, then connect the all-rank diagonal result. Do not assume arbitrary W has this property.
3. Retain a separate exact-product=T arithmetic estimate for HB **integer** slots; pay the off-target complete-modulus congruence and coprime mean, actual mixed shifted moments, normalized Fourier/H-box error and growth m(N) uniformly.
4. Identify final causal integer `rho_T` and physical `Q_T` (distinct from auxiliary level), finish marked/HB/empty Gamma/high-rank/enhanced sources. P3.6 remains **YELLOW**.

## Successor P3.6 — actual strict rough-HB even complete target exclusion (2026-11-09)

- **Verified inherited head:** 0e10983bce5f5b51713b1b0f7b73028cfee20a7e; branch chatgpt/p3-internal-original-w-20261105. No replay of the obsolete de582e6 entry.
- **Actual proof commit:** bcf8162d4260fc3a932080d46bb7cd77f06666fe [skip ci]. P3HBEvenRoughTarget.lean (89 lines), Git blob **b07494d068a53bd0c5c91c525964315b77f8e9a8**.
- **VERIFY commit:** 7749ec7e43c959b382d1482325fc088edfb0ebf0; import plus four registered, **not executed** check commands. VERIFY Git blob **a45b432d034ea61812ea130c7de474272ecbc788**.
- **REGISTRY commit:** ccd4c15d5aa7e1aaec498469a83e49242edb9e53; Git blob **1f870a371b3590ff51cf0ca6bce972294b85737c**, valid JSON.
- **Frozen source:** chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, prime-product completion sections 2 and 4. Lean v4.33.0-rc1 and Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 unchanged.
- Root, ImbalancedChen, docs, docs/source-only and this packet AGENTS.md lookups were NOT_FOUND. Actual production definitions of roughOneSlot/roughOneSlot_support, actual rough HB role words and factor tuples, and the predecessor literal rough mass source were read. No extra constraints were inferred.

### Actual internal mathematical increment

The production roughOneSlot z n is the literal STRICT rough indicator requiring z < p for every prime p dividing n. Consequently, if T is even and 2 <= z, its original strict rough multiplier at T is **exactly zero** (2 divides T). There is no extra parity mask and no new analytic premise.

The existing production roughOne_list_prod identity then shows that the **product of all original rough group projectors** vanishes whenever their group products multiply to even T, for an arbitrary list length. This exact diagonal statement does not add any cost depending on the growing HB length.

For the actual ordered factorTuples (2*(j+1)) T and original roughTupleWeight z y (roles j), actual_word_mask makes EACH occurrence at complete product T zero. The new final theorem sums these genuine occurrences with the unchanged **signed** order-three HB coefficients +3, -3, +1, preserving the real y cutoff, unit factors, single log slot and positional multiplicities. This is not an abstract surrogate PP theorem.

**Scope:** The proof applies to sources that truly retain the same strict rough projector on each original HB group. It does **not** establish that the final compiler supplies it for all marked, high-rank or empty-Gamma mother cases. An even marked outside factor needs separate scrutiny; actual Zchart >= 2 with a common eventual threshold is also still to be proved. No off-target arithmetic discrepancy, exact coprime mean estimate, full physical modulus mass, Fourier/H tail, final causal rho_T/Q_T, or arbitrary log saving is claimed.

### Verification and open boundary

- GitHub source read-back blob: b07494d068a53bd0c5c91c525964315b77f8e9a8. Forbidden proof escape scan **0** and textual delimiter balance **PASS**. These are NOT Lean checks.
- Independent Python integer regression: **64,908/64,908** ordered positive factor tuple instances, all even T from 2 through 100, all HB j=0,1,2, cutoffs z=2,3,5,7, zero surviving rough projector products. This does not validate elaboration or analytic estimates.
- Actual container command lookup showed **no lean**, **no lake**. **NOT RUN:** Lean/Lake typecheck or compilation, kernel replay, CI, transitive axiom audit, Codex, heavy numerical producer. The source-only module import path is not installed. Four declarations remain **SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED** and can still contain elaboration errors. No GREEN promotion.
- EXTERNAL_INPUTS.json unchanged: Git blob 8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab. Medium analytic estimate (M) is **REGISTERED ONLY**; no implementation or new axiom. No changes to the manuscript, production source, main, excluded full87 dynamic-parent/history node, other tasks, PRs, CI or board.

**Next exact entrance:** Targeted elaboration in the pinned Lean/Mathlib environment (isolate source-only import mapping without changing production files); correct any true errors in these four and their prerequisites. Then prove the actual whole-compiler strict rough mask and Zchart >= 2 with the required common quantifier order; keep marked-even and empty-Gamma exceptions separate. Complete non-target arithmetic moments and true Fourier/H uniformity with the same original physical rho_T,Q_T before any P3.6 closure claim.


## Successor P3.6 — original fine-marked primes joined to strict rough HB: even exact target zero (2026-11-09)

- **Verified inherited head:** b1fb206689f3eebfebc28dfab7bffdac48a42abb, branch \`chatgpt/p3-internal-original-w-20261105\`. Frozen manuscript: \`chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, prime-product completion §§2–4, original-source marked/factorial section (T), geometric/Fourier section (F). Pinned Lean v4.33.0-rc1 and Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 unchanged.
- **New candidate module:** \`docs/source-only/20261105-p3-fourier-coordinate-ibp/P3HBOriginalMarkedFineTarget.lean\`. This reuses actual production \`actualPrimeSlotBox (actualPrimeFineLabelFinset N tau)\`, actual ordered \`factorTuples\`, \`roughTupleWeight (roles j)\`, \`fineKernel\`, and two previous real source lemmas \`original_prime_box_product_not_dvd\` and \`literal_occurrence_target_zero\`. It does not invent a source dictionary or a new PP hypothesis.
- **New narrow mathematical result:** For even N and 2<=z, any actual original fine-marked-prime tuple times an original strictly rough HB integer occurrence of complete product N contributes ZERO. With a nonempty marked label word, its prime product cannot divide N; with an empty marked word, the marked product is 1, the residual integer equals even N and the strict HB rough projector annihilates every occurrence. Thus the labelled complex-weighted exact-target fibre vanishes at every original physical modulus q (literal coprime mean included) and remains zero after the same arbitrary integer rho, Q sum with HB signs +3,-3,+1. This closes ONLY this mixed source's exact-target diagonal; arbitrary even external marked integers and final compiler admission remain unproved.
- **No analytic saving:** No off-target divisor moment, Fourier/H uniformity, full-source PP, actual rho_T/Q_T, growing-m threshold or medium (M) implementation follows from this exact finite classification. This is SOURCE_ONLY; no green status.
- **Independent finite regression:** Enumerated even N=2..200 and marked prime words of ranks 0..3 from primes <=53 omitting all prime divisors of N. Exactly 100 full-target marked/residual cases occurred, all with empty marked word, and none survived a strict rough cutoff z in {2,3,5,7}. Counterexample outside the allowed alphabet: N=30, marked=[2], residual=15, z=2 permits nonzero rough residual, showing the original marked source restriction is material. These finite checks are NOT Lean elaboration, a kernel proof or a bound.
- **Environment / verification:** Current execution container has no Lean/Lake binaries; no pin-matched compiler or SOURCE_ONLY import mapping was installed. Not run: Lean/Lake, CI, independent kernel replay, full transitive axioms, Codex or heavy producer. Static no-proof-escape scan 0; JSON parse and final Git blob verification must be separately reported. \`EXTERNAL_INPUTS.json\` stays unchanged (blob \`8b463fb2ef9a93148ad1fc3c3d2ca134f1a295ab\`), external (M) REGISTERED_ONLY.
- **Next entry:** Pin-matched elaboration/repair of these three declarations and dependencies, then identify whether every actual marked+rough-HB consumer uses this original fine alphabet and full strict rough projector. Other marked even multipliers and empty-Gamma mother words remain separate. Focus subsequent work on non-target complete-modulus arithmetic discrepancy and uniform original geometric W/Fourier before claiming same causal rho_T PP.
