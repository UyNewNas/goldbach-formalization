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
