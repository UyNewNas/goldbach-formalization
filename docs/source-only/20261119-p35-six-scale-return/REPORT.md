# P3.5: original six-scale return adapter, source-only handoff

## Baseline and packet

The independently continued branch is
`chatgpt/p3-5-bounded-chart-20261119-1734`, read at
`ab877300f283c9be9cf5bf4fbce88d56837a0080`. The enclosing commit is the
new SHA (a commit cannot contain its own hash). This packet adds only
`Part3OriginalSixScaleReturnAdapter.lean` and this report in
`docs/source-only/20261119-p35-six-scale-return/`.

Candidate source SHA-256:
`1e94070ffa9928c25fef31fd8ee6e738d53896083bf8b4617a2fb867923ffd11`.

## Actual deduction and its scope

`original_six_scale_returns` is a proposed candidate proof body connecting
already present sources, not a new proof of an ordinary or exceptional
spectral bound. For each fixed `eta>0`, its common real threshold is
chosen before `OriginalData`, x, the dyadic index, chart, row, signs or
the smooth scales. The original global cutoff is `globalCutoff D x
(eta/2)`; the actual common Poisson block must be nonempty. The row z is
in the original physical chart and the n carrier is nonempty at n, which
supplies the actual positive `nu=k.1`. Nonzero original residue supplies
`A=|a|>0`. Both chart choices are quantified.

For each positive scale pair `M,N` satisfying `M<=2*D.bScale` and
`D.cScale<=N`—in particular the six `(b,c)`, `(b,2c)`, `(b,4c)`,
`(2b,c)`, `(2b,2c)`, `(2b,4c)` pairs—the existing actual cutoff source
gives `V*M/N <= x^eta`, where `V=2^j`. Since M,N are positive,
`V <= x^eta*N/M`. This is derived from the common cutoff, not introduced
as an extra premise.

With `U=dyadicScale k.2.1`, `L=U/nu`, and `Z=fixedZ D upper`, the
candidate uses that same bound for BOTH the established literal ordinary
`regular_return_le_rpow_cutoff` and the established exceptional
`exceptional_return_le_rpow_cutoff` at the numerical exponent `7/32`.
Consequently their respective already-defined (24)-to-(25) scalar return
expressions are bounded by `x^(2*eta)` times their corresponding printed
polynomials. The outside Poisson factor `(M/N)^2`, full `A*V*U` term,
actual Z, signed row's U, and `L=U/nu` remain in place. No arbitrary
shared n sequence, packet energy estimate, oldform-removal estimate,
spectral gap, or assertion equivalent to (24) is assumed.

This is only the scalar adapter after the analytic expressions are
available. It does not supply those analytic expressions for the actual
trace, does not remove the `3/4` loss in the prior reduced-pair
candidate, and does not close all-cost 7/32 or (24). The two zero lanes,
actual truncated tail, `14eta` and `28eta` Fourier weights, `128C`
enlargement and their collective reserve are not paid here. The cutoff
factor above is squared `2eta`, distinct from those Fourier charges. No
claim is made that the candidate has passed Lean elaboration.

## Source and manuscript pins

* Existing `ImbalancedChen/Part3ZRegularSpectralPolynomial.lean`, Git blob
  `0b8a6d7cadb5e9bb0ca2e74ded243ba9e3d16e4b`: literal ordinary (24)-to-(25)
  comparison and `regular_return_le_rpow_cutoff`.
* Existing `ImbalancedChen/Part3ZExceptionalSpectralPolynomial.lean`, Git
  blob `ea8eefc108c76858f9ddce74eda8053ea1dc55b8`: exact exceptional return,
  polynomial and sharp/inflated cutoff algebra.
* Existing `docs/source-only/20261102-resume-30p/exceptional_j_eta/Part3OriginalAdditionalSpectralCosts.lean`,
  Git blob `e957c4985864f7ea8124d333cd9f7efb82363ada`: the actual common
  cutoff threshold for all six scale pairs and the exceptional `x^(2eta)`
  specialization. Its imports and the ordinary source need the frozen
  staging closure; they have not been installed or recompiled here.
* Existing `docs/source-only/20261102-resume-30q/automorphic_dictionary/Part3OriginalTwoZSourceAssembly.lean`,
  Git blob `62d248aa63bd5d66db39f681732ead8291d8c7ae`: actual two-chart
  `fixedZ`, chart carrier and positivity. Original occupied rows give
  the strictly positive nu through `nCarrier_positive_coprime`.
* Paper repository `UyNewNas/chen-imbalanced-semiprimes` commit
  `9731290e8f53cffda44129906cde6a965eaa869b`, main body blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, distribution module blob
  `19f9672bc9b6d455045213c5e23e10433a9569d2`, §7 (24)–(25). This is the
  same pin as the preceding packet. Original established external inputs
  remain recorded there: normalized Kuznetsov, Pascadi A/J, ABL 3.1/3.2,
  regular large sieve, and the separately normalized numerical gap. None
  is newly axiomatized or proved in this packet.

## Validation and pending work

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review of this new source: not done.
`UNEVALUATED`: yes, including inherited source-only imports.

The configured base pins were checked: Lean `leanprover/lean4:v4.33.0-rc1`,
mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native goldbach
`09b97db5764ade1246bfb77206baa1b124760958`. Neither `lean` nor `lake`
exists in PATH, and the source/compiled dependency closure is not staged;
no compiler ran and there is no compiler exit status or log. Shell stack
limit is 8192 KiB and virtual memory is unlimited; no resources were
increased. `sha256sum` produced the hash above; the exact token search
`rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1
(no matches). This is not proof checking. No CI, Codex, or user machine
was invoked.

Next stage the exact selected imports and check all three continuation
modules; inspect the transitive axioms and obtain independent review.
Separately connect the sharp actual same-level spectral products, oldform
and continuous return, full-range J, numerical denominator and all
original zero/tail/Fourier/outer fees. In particular use the published
unbounded-ratio J input at its precise common-phase normalization or prove
a payable replacement; the previous `3/4` transport is insufficient.
