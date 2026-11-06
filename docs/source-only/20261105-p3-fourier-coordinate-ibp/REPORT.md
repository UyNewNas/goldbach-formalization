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
