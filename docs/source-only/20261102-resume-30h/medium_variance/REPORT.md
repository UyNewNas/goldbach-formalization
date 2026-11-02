# H / medium_variance — finite counted spectral polynomial

Status: **local source step complete; broad task incomplete; uncompiled; kernel_verified=false; formal_credit=0**. Author task selection: gpt-6-astra, xhigh, as assigned by TASKS.json. Independent review is pending. Only this H directory was written. No compiler, build, checker, finite-certificate replay, CI, subagent, or quota operation was run.

The genuinely missing step after G was the composition of its actual signed coefficient norm with its original scale identities. G had the multiplicity estimate, occupied-key geometry and isolated D1/D2 monomial identities, but no theorem paying the whole returned polynomial with the actual coefficient norm. H supplies that finite implication. It does **not** supply the analytic estimate of the physical kernel by this polynomial.

## Original source and exact scope

The authoritative manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Lines 127–156 give the restricted-medium hypotheses; lines 209–249 give the retained source, D0/D1/D2, common interval/phase and named classical inputs. The detailed module `distribution-medium-completion-20261010.txt` is SHA `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`:

- Lines 320–347: reciprocal-square source, positive f, signed h, nonzero y, coefficient norm (23), literal H/S geometry.
- Lines 349–380: the still-unproved analytic return (24) from the precise classical norm inputs.
- Lines 382–405: the returned polynomial (25), scale substitution, (26), and auxiliary nu sum.

The F independent review `docs/source-only/20261028-resume-30f/reviews/medium.md`, lines 116–145, was read. It accepts the earlier principal/outer Gram source step only and explicitly leaves E2 and the spectral return open. H does not overwrite that scope.

The imported current production `Part3DistributionTargets.lean` supplies the actual `MediumAtom` and `MediumAdmissible`: U,V,Q1,Q2,Q3>=1, x=UV, x>exp(exp 1), c0*x<=|a|<=x^(1+kappa), and the unchanged four strict geometric monomials. H uses theta=7/32 from G, takes sigma>0 and c0>0 in its final theorem, and requires no stronger parameter range. The broader original sigma<1/100 and 0<=kappa<=sigma/100 conditions may be supplied by the original caller; this finite step does not need to strengthen or alter them.

The exact source consumer is G `OriginalSignedCountingNorm20261028.countingNorm`, specialized to S=roughS k, H=keyRealH atom k and F=countingF atom=atom.U/atom.Q1. Its coefficient is the finite fibre sum of the current production reciprocal-square `atomCoeff`, with both fixed-unit gates and one output unit phase. The G theorem `output_eq_actual_square_output` proves the ordered relabeling to the current production `level/outputY`. The G theorem `physical_count_source_eq_grouped` places exactly that coefficient against the actual completed Poisson `physicalKernel`, retaining inverse(z), all m, and the c-unit gate. No fresh spectral norm or arbitrary estimate field replaces this coefficient.

The result is for this explicit dyadic f source, and for the fixed one-bounded lambda, omega and output phase allowed by that source. It does not assert that every lower f dyadic block, independent Lambda expansion, product-window difference or polarized endpoint has already been identified with this source. That full original-source dictionary remains an internal obligation.

## Delivered proof bodies

1. `Part3ActualOccupiedCountingScale.lean` proves `actual_H_le_countingH`, `sourceNorm_le_countingMass` and `exists_source_counting_threshold`. Define

   `loss = 16 * keyD k * (log x)^5`,

   `K = 1152 * divisorMaximum(S,H,F)^5 * harmonic(floor(2*S))`.

   From the actual occupied rough product `keyR<=4*R*S`, H proves literal `keyRealH <= loss*Q*R^2*S^2/V`. It proves F>=1 from the original strict Q<U*x^(-sigma), uses the existing signed multiplicity theorem only when H>=1, and uses exact emptiness when 0<=H<1. Its new estimate is

   `sourceNorm(nu) <= K * countingMass(loss) / nu`.

   The uniform threshold is selected before every atom, owner key and coefficient. Its actual H/S factor is paid by G's uniform geometry, with no rounded singleton and no added large-nu +1.

2. `Part3ActualReturnedPolynomialCompression.lean` compresses the full regular and improved exceptional polynomials from (25), not just their separate monomials. With U_spec/Z=D0<=1 and C<=B_spec*Z, the regular polynomial is at most `4*C*B_spec*Z^2+|a|*U_spec*Z`. The enhanced exceptional polynomial is at most `4*C^(1+2*theta)*B_spec*Z^(2-2*theta)`: the proof keeps the B_spec factor and combines all real powers explicitly. Normalization gives `loss^2*(4+|a|/x)*D1` and `4*loss^2*D2`. The distinct zero-Poisson monomial uses B_spec^2<=x and |a|>=1 to give `loss^2*D1`.

3. `Part3ActualCountedSpectralPolynomial.lean` consumes the source bound, rather than assuming it, in `normalized_regular_source`, `normalized_exceptional_zero_source`, `countedPolynomial_bound`, and `exists_countedPolynomial_threshold`. It preserves the regular packet factor `(|a|*nu)^theta` and proves `nu^theta/nu=nu^(theta-1)`. Let `Wnu=sum_(nu in nus) nu^(theta-1)` for any finite set of positive auxiliary indices. Then its final theorem is

   `(P^4/(U^2/Q)^4) * countedPolynomial`

   `  <= K*loss^2 * [ Wnu*(4+|a|/x)*D1 + 4*D2 + D1 ]`.

   Here P is the exact G `bareCauchyPrefactor=U/(Q*R*S*sqrt(S))`. `countedPolynomial` contains the entire regular sum, enhanced exceptional term, and genuine m=0 Poisson term with the actual source norm. The all-source norm is exactly nu=1. The final uniform theorem derives |a|>=1 from c0*x<=|a| and c0>0 and discharges all three geometry gates from the existing uniform threshold.

## What is eliminated and what is not

Eliminated locally, with implemented Lean bodies:

- Literal original keyRealH to the double-Cauchy counting mass, including the H<1 branch and F>=1 licence.
- The factor (1+H/S) in the actual finite coefficient norm, at one original uniform threshold.
- Compression of the full (25) regular/exceptional polynomials to the G monomials, keeping the moving-residue term and B_spec powers.
- Multiplication of those polynomials by the actual coefficient norm, with exact nu^(theta-1), D1/D2 and zero-Poisson normalizations; no count or polynomial upper bound remains a premise of the final theorem.

Not newly eliminated:

- The separate y=0 difference has the G identity `zeroDifference_normalization=loss*D0`; H does not claim a new physical zero-difference estimate or include it in the nonzero y count.
- Full source association from every actual retained-phase Abel endpoint, coprime color, independent st=d pair, product-upper difference and non-Hermitian polarization to the reciprocal kernel/count family, including all actual f dyadic blocks and coefficient costs.
- Derivation of the physical kernel bound (24) from the named classical inputs, including transform norms, common m interval/phase, dyadic height summation, the continuous quadratic form and coprime packet source identities. Equation (24), L51, P1/P2, internal K/PP and the bare-medium estimate have **not** been introduced as primitive assumptions.
- The uniform selectable-subpower bounds for K, loss and the original a-smooth auxiliary sum `sum_(nu|a^infinity) nu^(theta-1)`. They remain explicit finite quantities here; no finite set is asserted to be the full original auxiliary source, and no x^epsilon is silently inserted.
- Original two-square-root physical Cauchy assembly, bounded common m cutoffs and their losses, retained-phase x^(5*kappa+o(1)), original S2/S3 corrections, E2/dispersion assembly and the arbitrary-log medium conclusion.
- All predecessor installation, compilation and kernel verification. The G modules are source-only files, not installed under ImbalancedChen in this workspace. No mirror has been substituted.

There is no new classical input assumption in the H Lean signatures. The pending analytic step must use the precise foundational statements described in `final-classical-input-correspondence-20261010.txt`: normalized Kuznetsov at trivial character/level z/cusps infinity and 1; the regular cumulative large sieve; coprime ABL Lemmas 3.1/3.2 with R(n)=sqrt(|n|)rho(n), (a,z)=1, height-independent transformed coefficient 1_((n,a)=1)*beta(nu*n,z)*e(-n/z), cost (|a|nu)^(theta/2); the continuous formal Plancherel quadratic form; Kim–Sarnak theta=7/32; and Pascadi Theorems A/J with one common interval and additive phase. These are listed as pending foundational interfaces, not as a replacement for the internal derivation of (24).

No manuscript contradiction was discovered by this finite calculation. The strongest conclusion is the displayed finite counted-polynomial inequality. The failed condition for promoting it to (26) is the missing actual kernel-to-polynomial analytic estimate and full source dictionary, together with the remaining uniform subpower payments. The affected nodes are E2, the actual spectral return, the bare bound, and the final medium residual aggregate. The implemented repair route is the finite counting/normalization route; the remaining route starts with the exact primitive norms and actual coefficient/interval source association, not with a full L51 premise.

## Installation and validation scope

Install the three H sources, in filename dependency order, as `ImbalancedChen.<filename stem>`. First install the exact pinned G imports and their recorded source dependencies. REGISTRY records source paths and raw hashes; it does not license replacing a missing import with similarly named different bytes. Mathlib is pinned by lake-manifest to `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

The source was inspected mathematically against the displayed formulas. No Lean elaboration or execution occurred, and this report is not independent review. Source step completion is distinct from broad task completion and formal verification.

Delivered source SHA256:

- `Part3ActualOccupiedCountingScale.lean`: `e3fee2c3013e0487badfa0d778794512f63439b8479b4fe2a9e5a9188acdba78`
- `Part3ActualReturnedPolynomialCompression.lean`: `a89627fd962722afbb59c8e5197eabb89dcdd4aafe9ed79eb7d87a8bedd2d998`
- `Part3ActualCountedSpectralPolynomial.lean`: `ea393d6966f5638f3cc559d797612a8042ec338735a81961484172eb507dc6ce`

The report and registry hashes are provided to root separately to avoid a self-hash cycle.
