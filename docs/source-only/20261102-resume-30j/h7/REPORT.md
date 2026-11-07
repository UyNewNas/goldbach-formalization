# J / h7 — original U7 scalar correction and actual enclosure

Status: **substantive local analytic step supplied; full h7 OPEN; source only; uncompiled; kernel_verified=false; formal_credit=0**. Only `docs/source-only/20261102-resume-30j/h7` was written. No compiler, build, CI, certificate replay, finite decision execution, Git operation, quota call or subagent was used.

This delivery does **not** claim to remove either saved sharp endpoint premise of `p5z_original_h7_of_actual_full_policy_source_supplied`. It supplies the previously missing exact analytic identification of its genuine Omega integral with the scalar integrals used by the actual original numerical producers, and proves a direct rational enclosure of the semiprime correction. The resulting enclosure is weaker than the saved endpoints. Full-policy density, licence, active support and same-coefficient PP are also still open.

## Original source and the actual missing step

The task row, J README, current manuscript lines 562–630 and 691–996, the complete `9ffe5d3.md` engineering tree, and the two named production predecessors were read. The manuscript fixes `d=59/250`, the original marked U7 source and its coefficient **two** in the Chen functional. Current `c=49044063/25000000` and `K=8452171/1250000` are unchanged.

`P5U7OriginalSourceSuppliedRoute.lean` already derives the combined rank-three/rank-four arithmetic source mass from `P5U7OriginalArithmeticMeanUpper`; it must not be supplied or counted again. `P5U7ComponentLeadingIntegrals.lean` already splits the actual Omega functional into its terminal-prime and ordered-semiprime components, and evaluates the prime component as

    P = integral_[59/250,1/3] log((1-2t)/t)/(t(1-t)) dt.

Its semiprime component remained a genuine nested integral, with the inner logarithmic kernel present only for `u<(1-t)/3`. `P5U7OriginalRationalCoverCertificate.lean` supplies a different two-dimensional staircase certificate route, but its `independentOriginalCheck_sound` still assumes a finite Boolean check. This delivery does not invoke that guard or claim it passed.

The actual original source was found at `../goldbach-research/certify_sharp_switch_midpoint.py`, SHA `4b1830eb0168470f2007581777f6755a8a2dd14dfa67bd14b2f6fa0b6f103476`, and `../goldbach-research/sharp-switch-simpson-independent.py`, SHA `545a9e5772f11bb51b91e742ba0f9a61debd0a4e460ff7b0b41515adb12cb792`. These match the bindings recorded by the original output files. Both consume the same correction

    C = integral_[2,132/59] (log(s-1)/s) log(191/(59(s+1))) ds.

`sharp-switch-midpoint-proof.tex` explains the initial-branch/Fubini identity. Its current proof-library copy has the identical SHA `3b89076e90113e4b8d0a85feb02196c19b7090e546911d0a1f874dffa0dacbaa`. The selected upper output has 1024 cells, and the independently produced lower output has 64 panels and 112-bit rounding. Their recorded success fields and hashes were read as source provenance, not treated as Lean proofs or re-executed.

## New proof bodies

`P5U7OriginalScalarCorrection.lean` provides the full analytic dictionary rather than assuming a scalar-integral equality.

1. Continuous global max extensions provide genuine primitives of `log(s-1)/s` and of its product with `log((191/59)/(s+1))`. They agree pointwise with the original kernels throughout every used interval; the extension does not change any source domain.
2. The actual semiprime logarithm is evaluated on the **closed** active interval, including the `s=2` seam, where its value is zero. With `s=(1-t-u)/u`, the derivative of `-G(s)/(t(1-t))` is exactly the original semiprime kernel. FTC supplies the inner variable change, including `t=1/4`.
3. The actual semiprime row vanishes for `t>=1/4`. Its full outer integral therefore equals the integral over `[59/250,1/4]`.
4. Put `s(t)=1/t-2` and `L(t)=log((191/59)t/(1-t))`. The explicitly defined primitive `G(s(t))*L(t)-H(s(t))` has derivative equal to that actual row. The derivative terms cancel because `L(t)=log((191/59)/(s(t)+1))`. At the lower endpoint `L=0`; at the upper endpoint `G(2)=H(2)=0`. FTC yields `p5U7ComponentSemiprimeIntegral=C` without assuming Fubini, table semantics, an endpoint or an integral estimate.
5. `originalOmegaIntegral_eq_scalar_pair` consequently gives the exact original `J7=P+C`. `originalOmegaIntegral_eq_mul` and `currentOriginalOmegaIntegral_eq_components` preserve the original K-linearity. There is no extra half factor, ledger factor two or Chen quarter inside `J7`.

`P5U7OriginalScalarCorrectionEnclosure.lean` proves a concrete missing estimate from this actual kernel. For `R=132/59` and `2<=s<=R`, the elementary analytic bounds `1-1/x <= log(x) <= x-1` give

    (s-2)(R-s)/(R(R-1)(R+1)) <= correctionKernel(s)
      <= (s-2)(R-s)/6.

The quadratic shape is integrated by an explicit cubic primitive. The resulting unconditional endpoints are

    (14/59)^3 / (6*(132/59)*(73/59)*(191/59)) <= C
      <= (14/59)^3 / 36.

`originalOmegaIntegral_bounds_from_prime_component` inserts these bounds into the actual original Omega integral, around its genuine rank-three prime component. These are proved analytic inequalities, not a finite decision guard or a generic pointwise-bound hypothesis. They account for the ordered-semiprime contribution exactly once. Their precision is intentionally not represented as sufficient for the saved sharp endpoints.

## Remaining original obligations

The following inputs of the original source-supplied h7 route remain unchanged:

- The saved upper endpoint `J7 <= (1672464594622060236183097/1208925819614629174706176)/(67619/10000)`.
- The independent lower slope endpoint `(7183180737282426411788973366247539/5192296858534827628530496329220096)/(67619/10000) <= J7`.
- The actual common full-policy reciprocal-totient density limit, its bound and strict gap to the fixed density coefficient.
- A chosen actual same-e policy's licence, cap and active-support conditions.
- The signed **sum** of rank-three and rank-four prime-product errors at that exact attached coefficient, with the original uniform threshold order.

The next endpoint task can now work directly on the two actual scalar kernels `P` and `C`. It still needs genuine midpoint/Simpson error soundness at the archived partition, outward logarithm/arithmetic enclosure and the complete original finite sum binding, or another sufficiently sharp proof of those same two endpoint inequalities. The modest new correction bounds do not replace any of that. No desired endpoint or equivalent internal estimate was added as an assumption. No mathematical contradiction in the manuscript was established.

## Installation and verification

Install the dictionary before the enclosure, at their stated `ImbalancedChen/` module targets. The enclosure's direct dictionary import is currently a draft path, recorded explicitly in REGISTRY. Production files and all older batches were read-only. REGISTRY pins every direct local import, the inspected production source chain, manuscript and producer/output evidence. It does not claim a new audit of the entire transitive import DAG.

The manifest pins Mathlib revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and toolchain `leanprover/lean4:v4.33.0-rc1`. The repository's `.lake/packages/mathlib` source tree is absent, so no local Mathlib file hash or elaboration result is asserted. FTC and interval-integral API use follows existing production source patterns. Verification here consists of manual mathematical/source inspection, declaration and forbidden-token searches, source presence and raw SHA inventories. Independent review, installation and compilation remain outstanding. The complete h7 task remains **OPEN**.

Independent pre-compilation review found a reversed equality in the new `scalarCorrectionKernel_intervalIntegrable`: `ContinuousOn.congr` requires the target scalar kernel to equal the known continuous regular kernel. The delivery now passes `(regularCorrection_eq hs.1).symm`. This is the only new `ContinuousOn.congr` use. The four new `intervalIntegral.integral_congr` applications retain the left-to-right integral identities, while the four `HasDerivAt.congr_deriv` applications discharge their derivative equalities algebraically. The reviewer also identified a preexisting reversed-congruence issue in imported `P5U7ComponentLeadingIntegrals.lean`; that production dependency was not edited and remains an inherited blocker. This correction has not been compiled and is pending review of the refreshed source hashes.
