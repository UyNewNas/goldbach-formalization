# T05 independent zero-kernel contract review

Status: **PASS for exact existing-source reuse and locator mapping**, bound to T04 final `FREEZE.json` SHA256 `6ef2c30f642bce077971be1d35552098b0e0172b4a4897b0a10bbab7215cba99`. All 19 frozen files match. This is source-level review only, with no Lean, Lake, LSP, proof helper, compiled artifact, or kernel execution. The exact permission scope is recorded in `ZERO_KERNEL_REUSE_ALLOWLIST.json`.

## Inputs independently read

* Original manuscript `chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, lines 127–156 and 197–249, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.
* Detailed original argument `chen-imbalanced-semiprimes/proof-library/source/distribution-medium-completion-20261010.txt`, §7 lines 299–405, §8 lines 406–430, §10 lines 454–484, SHA256 `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`.
* Original normalization correspondence `chen-imbalanced-semiprimes/proof-library/source/final-classical-input-correspondence-20261010.txt`, lines 21–70, SHA256 `9604bfb8fdf7325205c8ebe431c7c5e977a3e5bea07e79b8d209548e1a4069db`.
* Genuine importer `docs/source-only/20261102-resume-30j/spectral_regular/Part3OriginalNonzeroCuspOneSource.lean`, SHA256 `d7ad7167a966bff0e7dee4cb706152330df1a71faff700da61b3c63e9b753230`.
* Existing provider `docs/source-only/20261102-resume-30i/spectral_eq24/Part3ActualZeroPoissonKernel.lean`, 12408 bytes, SHA256 `9b03b40126c13824722843f76fe2781a72165c5560d9ab01df233640c29e27e7`.
* The signed counting source, actual reciprocal-square and physical smooth Poisson sources; fixed cutoff definitions; Ramanujan special-case, multiplicative gcd, prime-power and general gcd identities; the exact `ActualLargeGCDBetaMass.sum_gcd_le` proof.

The two manuscript hashes and the provider/importer hashes above were recomputed locally, not copied on trust from a prior report. The unchanged mathematical arguments were read rather than executed.

## What the genuine importer actually needs

The importer opens `ActualZeroPoissonKernel20261102`, and its final theorem directly consumes only the definitions `smoothModuli` and `nonzeroKernel`. It does not use `zeroKernel_norm_le`, `actualZeroSource_sq_le`, an Eq. (24) estimate, or a spectral-return assumption.

The exact needed carrier is

\[
\mathcal C(C)=\{c\in\mathbb N:0<c\le\lfloor3C\rfloor\},
\]

and the exact nonzero branch is

\[
K_{\ne0}(C,D,a;z,y)
=\sum_{c\in\mathcal C(C)}\psi(c/C)
  1_{(c,z)=1}\sum_{m\in\mathbb Z,m\ne0}
   \frac Dc\widehat\psi(mD/c)S(m\bar z,ay;c).
\]

The Lean `tsum` is written with a zero-valued `m = 0` branch. It is not a finite truncation. The old provider has precisely these definitions, including the `c.Coprime z` gate and the unmodified `D/c` prefactor and Fourier argument.

The importer's final identity holds for arbitrary real C,D and integer a,y, with positive natural z. Every actual c in its finite carrier is positive. The matrix identity is applied only after the coprimality gate supplies `(z,c)=1`. No new hypothesis `(a,c)=1`, squarefree z, small a, positive y, or small residue is justified or required. Although the actual analytic application has positive C,D and nonzero ay, those extra hypotheses must not be added to this algebraic importer theorem.

The proof is termwise: finite-sum congruence, then `tsum_congr`. Therefore its absence of a summability premise is correct. It is not an interchange of two infinite sums. Its inactive noncoprime branch is the zero series on both sides.

## Manuscript normalization dictionary

The original §7 has the exact completed summand `(D/c) psihat(mD/c) S(m inverse(z),a*y;c)` at lines 351–352, and the zero term at line 353. The provider matches it literally.

The outer arithmetic q and its block anchor q0 from lines 299–312 are not the spectral level. After the reciprocal-square step the level is `z=s1*s2`, with signed `y=f*(h1*s1-h2*s2)`. The generic Poisson scale D is the b scale (`Bspec=N*R` at line 393); it is not the earlier divisor-decomposition scale called D in `E2=sum_d E3(d)/d`. No factor q, q0, d, z, or sqrt(z) can be inserted into this zero kernel by relabeling those variables.

For the nonzero cusp dictionary the normalized positive modulus is `c*sqrt(z)`. The old cusp-one matrix sum equals `e(ay/z) S(m inverse(z),ay;c)`, so returning to the physical sum multiplies by `e(-ay/z)`. The genuine importer has that exact sign. Restoring `1/(c*sqrt(z))` in a later trace formula is a separate operation and cannot modify the physical `D/c` here.

The original spectral specialization has trivial character, level z, cusps infinity/1, and spectral arithmetic singleton s=1. The ABL dictionary uses q_ABL=1, r_ABL=z, s_ABL=1, with `R(n)=sqrt(abs(n))*rho_ABL(n)`. Its transformed coefficient is `1_(gcd(n,a)=1) beta(nu*n,z)e(-n/z)`, requiring `(a,z)=1`. None of this is a premise of the elementary zero estimate; the source makes no claim to prove that packet transformation or its continuous analogue.

## Independent audit of the existing zero proof

Let `M0=norm(Fourier dyadicCutoffSchwartz 0)` and let `n=a*y != 0`. The fixed cutoff satisfies `0<=psi<=1` and nonzero support in `[1/2,3]`. For C>0 and a nonzero weighted term this gives `C/2<=c<=3C`. For D>=0,

\[
\left|\psi(c/C)\frac Dc\widehat\psi(0)c_c(n)\right|
\le\frac{2DM_0}{C}\gcd(c,|n|).
\]

`frequency_zero_eq_ramanujan` is exact: multiplication by m=0 removes `inverse(z)`, and inversion permutes the finite unit group, including modulus one. There is no residue approximation or coprimality assumption on a. The modulus coprimality gate is retained in the definition and can only decrease the norm bound.

The gcd mean used is the finite inequality

\[
\sum_{1\le c\le L}\gcd(c,|n|)\le L\,\tau(|n|),
\]

proved by the divisor majorant and `d*floor(L/d)<=L`; it requires `n!=0`. Taking `L=floor(3C)<=3C` gives exactly

\[
\|K_0(C,D,a;z,y)\|\le6DM_0\tau(|ay|).
\]

Thus the constant 6 is the support factor 2 times the carrier factor 3. It is independent of C,z,a,y. M0 is a fixed cutoff constant; it has not been silently set to 1. The proof remains valid for positive subunit C, including an empty modulus carrier, and for D=0.

The completed-kernel split requires D>0. The physical Poisson provider first proves absolute summability of the actual frequency series, and the zero module uses that result before isolating m=0. It supplies the unit assumption from `(c,z)=1`. This is a valid use of the complete physical series, not of a proposed trace formula.

The finite source is grouped on the actual ordered output `(z,y)` and retains the original complex tuple coefficient and output phase. The phase depends on `(z,y)`, not c or future m. The nonzero-difference carrier has positive f and nonzero difference, hence y!=0. Together with a!=0 it licenses the preceding pointwise bound. The final finite Cauchy inequality is

\[
|V_0|^2\le
(6DM_0\max\tau(|ay|))^2\,|\operatorname{outputCarrier}|\,B_{\rm all}^2.
\]

The implementation's `countingNorm ... 1` is exactly the all-output squared norm because 1 divides every integer. Arbitrary complex coefficients and output phases are allowed in this inequality; one-boundedness is needed only for separate counting-norm comparisons, not this finite Cauchy step.

## Boundaries and quantifier order

* Zero additive frequency and zero Poisson frequency differ. m=0 is treated here with ay!=0. If ay=0 then the Ramanujan sum is phi(c); replacing tau(|ay|) by `Nat.divisors 0` would be false. The theorem correctly excludes this case. The separate zero-difference diagonal remains outside this source.
* z=0 is not an actual cusp level. The zero estimate itself can be stated with arbitrary natural z because its gate remains explicit, but the importer's matrix/cusp identity correctly requires z>0.
* This module leaves `max tau(|ay|)` and output cardinality explicit. It does not by itself prove the final asymptotic `x^epsilon D^2 U Z B_all^2` for arbitrary S,H,F. The original dyadic support/cardinality and polynomial residue-size bounds are needed for that later conclusion. This is an explicit implementation boundary, not a newly found contradiction in the manuscript.
* For the asymptotic conversion, fix the desired epsilon and polynomial bound on |ay|, choose a sufficiently small ordinary divisor exponent, then the constant and large-x threshold. Do not take a uniform divisor constant independent of the chosen exponent, and do not assume a<=x^epsilon. The actual original bound `c0*x<=|a|<=x^(1+kappa)` gives a!=0 and polynomial size.
* The exact zero proof has no large-x threshold and no adjustable epsilon. The nonzero completion's finite Bessel/separation derivative orders must be fixed before its small exponents; the final tail order is chosen after the global cutoff allowance. Original §8 lines 417–419 explicitly places selectable classical epsilons after sigma and finite derivative orders. None is an extra hidden hypothesis of this zero module.
* The continuous spectrum is a later formal Plancherel quadratic form with `dt/cosh(pi*t)` up to the fixed Kuznetsov factor `1/(4*pi)`. Neither a single Eisenstein series as an L2 cusp vector nor an ordinary continuous mode is invoked by the zero module. Removing m=0 does not discharge the continuous/nonzero-frequency obligation.

## Reuse decision and classification

The requested interface already exists with exact old bytes. It supplies the manuscript's necessary zero/nonzero split and a valid explicit zero estimate. No new proof source, stronger bound, reduced domain, or replacement kernel is needed to fix this importer edge.

The failed T04 root locator `ImbalancedChen/Part3ActualZeroPoissonKernel.lean` is not evidence of mathematical impossibility. The archived path at that same immutable commit is present with matching blob/SHA/length, independently verified against the existing exact commit tree. Source installation-path mapping and the recursive custom dependency identity closure are now reviewable and approved within the frozen scope; no installation was performed. This approval does not imply that an importable source has been compiled.

The old source does not by itself close Eq. (24), the full original spectral return, or the full regular/continuous source graph. Those are separate unimplemented obligations. The current local blocker is an expression/provenance omission in the locator; no substantive mathematical gap was found in the zero-kernel calculation reviewed here.

## Final dependency identity audit

T05 independently recomputed the final 664 source records: 110 project modules at each of T04 and dca6, 435 modules from goldbach commit `09b97db5764ade1246bfb77206baa1b124760958`, and 9 modules from LeanArchitect commit `78dd66840d3efe8c824c699fc03381cec817c271`. Raw length, SHA256, Git blob SHA1 and the actual immutable Git tree all match. Initial imports were parsed independently with nested comment handling and support for `public meta import`; all match the final manifests. The authoritative final audit is `FULL_SOURCE_IDENTITY_AUDIT.json`. The earlier `PROJECT_BYTE_IMPORT_AUDIT.json` used a simple whole-line import regex and is superseded for import-list interpretation; its raw-byte and tree comparisons remain correct. No source was changed by correcting the metadata parser.

All 554 distinct custom modules are reachable from the zero-kernel target, with no unresolved custom import, conflicting identity, extra unreachable module or import cycle. The recursion stops at 202 distinct explicitly declared Mathlib/Batteries/Lean imports; those standard libraries were not recursively source-reviewed. Twelve committed configuration sources were independently hash/tree checked in `CONFIG_BYTE_TREE_AUDIT.json`.

The complete import chain enters `MathlibNt` through `Part3FactorFiberDivisor`, and another branch reaches `AnalyticNumberTheory`, `PrimeNumberTheoremAnd`, and `Architect`. These are actual custom dependencies. The old S04 exclusion statement cannot be extended to this chain. They are all included in the final 554-module identity audit.

The target selects Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, Batteries `41bd267b3f6b7252f6676af46d4ffc6783b64de9`, and Lean `v4.33.0-rc1`. Architect's own committed manifest instead names Batteries `31a49105f960721073a9adfc82b261f5d0f2ce1e`. This exact upstream/target distinction is disclosed in T04's frozen `PACKAGE_COMPATIBILITY.json`; compatibility with the target selection is unverified and must not be inferred from byte identity. This is not a zero-kernel mathematical gap.

T05's mathematical audit covers the unchanged zero proof, actual physical/Ramanujan/gcd proof route and true importer contract described above. The 554-node audit additionally certifies full custom source identity and import closure, not a fresh mathematical certification of every unrelated declaration reached by imports. No axiom dependency or elaboration audit was executed. The two `axiom` words at `PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean:172–173` were independently read in their enclosing documentation comment, so they are not executable declarations. Formal credit remains zero, and Eq. (24)/the full regular target remain outside this approval.
