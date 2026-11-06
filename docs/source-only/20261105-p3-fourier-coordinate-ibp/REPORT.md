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
