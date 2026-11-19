# P3.5: direct fixed-level sieve on the unremoved signed n row

## Continuation and packet

Baseline branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`f3eae490b5cbdaafad4e264e67e44311c8ef6354`; the containing commit is the
new SHA. This packet adds `Part3OriginalRawNSieve.lean` and this report
under `docs/source-only/20261120-p35-raw-n-sieve/`. Lean source SHA-256:
`1a647b41b60c0db099f00ef068465e92adaa2c26a4b1c3503327bebdb7f6119f`.

## Candidate and manuscript deduction

For an actual `Row D k` at a positive integer level z, nonzero original
residue a, either physical chart and Poisson sign, original mark ell,
and **every** X>0, write G=|a| nu and L=U/nu=`rowLength k`. The proposed
candidate bounds the entire native strict exceptional basis at this one
level by

    sum_{i: 0<lambda_i<1/4} X^tau_i |N_raw(z,i)|^2
      <= sieveConstant * (1+max(1,X)) * (1+G L/z) * B_z^2,
    tau_i=2 sqrt(1/4-lambda_i),
    B_z^2 = sum_{n in nCarrier(z)} |blockBeta(z,decode(z,n))|^2.

The left side is the literal `originalNFunctional`: its frequency is the
composite signed `s G n` and its coefficient is the original
`traceBeta`, including its level-dependent phase. The sign s is the
source's composite sign, not just the sign of the primary y block. It
works for each level separately; the coefficient sequence may change
with z but is shared across the eigenvectors for this fixed z.

Proof: the actual carrier is nonempty by `levelCarrier_has_n`; its
source hypotheses imply nu>0 and hence G>0 and L>0. Reindex the
carrier injectively by m=G n, with inverse m/G on that image. Its exact
dyadic support is G L<m<=2 G L. The coefficient mass is unchanged
because the original cusp and Fourier modulation phases have unit norm.
`traceIndex_eq_principalTraceSign` identifies the reindexed Fourier
coefficient with the unremoved row, for either sign. Apply the existing
fixed-level `signed_row` with scale G L and range parameter A=X;
`X<=X max(1,z/(GL))` follows from X>0. This produces the displayed
explicit factor, with no new spectral premise or ABL removal. At X=1
the price is `2*sieveConstant*(1+GL/z) B_z^2`.

The penalty GL/z = |a|U/z can be much larger than the reduced-row
penalty L/z. The extra `1+max(1,X)` also grows with the requested
weight. These are explicit real losses, not an implied constant or the
manuscript's 7/32 oldclass cost. The theorem does not bound the actual
positive trace's `nativeWeight` numerator or cosine, nor the raw n
energy from the prior Cauchy lemma. Applying it there still requires an
actual transform-weight majorant and a valid matching X at every slot.
It is not a level average, full J, ABL, spectral-gap result or (24).

## Exact sources and boundaries

* `Part3OriginalExceptionalJInitialAverage.lean`, blob
  `d3b96d8b765d0167ae125accd5d20e67da8569a2`; the path is
  `docs/source-only/20261113-resume/resume-balance-policy/r14_09/avgj-next/Part3OriginalExceptionalJInitialAverage.lean`.
  Its `signed_row` supplies the fixed-level result at signed frequencies
  and preserves a single per-level coefficient sequence. This packet
  uses `signed_row`, not its initial level average.
* `Part3OriginalExceptionalPostRemovalPair.lean`, blob
  `a038900816ae4e167afb9f46ace2e142440d386c`, supplies `rowLength` and
  `rowMass`; its reduced row is not substituted for this raw row.
* `Part3OriginalPrincipalTraceRow.lean` supplies the original sign and
  `traceIndex_eq_principalTraceSign`; the exact raw functional comes from
  `Part3OriginalNativeCuspFunctionals.lean`, blob
  `88c3220e130f426f55f2f742d73b9572fb0faa8c`. The existing
  `norm_modulatedBeta` and `sourceCuspPhase_norm` keep B_z unchanged.
* `Part3OriginalPositiveRawCauchy.lean`, blob
  `02abfecfd6ee1307874b80808a42685845ebcb3b`, still carries the full
  native transform in its raw n factor; it is not asserted to follow
  immediately from this result. All these sources remain source-only.
* The body at manuscript pin
  `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
  was rechecked: blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`,
  matching the chain. Distribution module blob
  `19f9672bc9b6d455045213c5e23e10433a9569d2`, §7 (24), §10(vii).
  Pascadi v3 Theorem J and ABL v1 Lemmas 3.1–3.2 remain separately
  documented in the parent handoff and `AVGJ_APPLICABILITY.md`; this
  candidate introduces no new external input and proves no full-range J.

## Verification and remaining obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axiom check: not performed. Independent review: not performed.
`UNEVALUATED`: yes, including the inherited fixed-level candidate.
No Lean or Lake executable is in PATH and the precise import closure is
not staged. Thus no compiler command ran and no compiler exit code or
log exists. The repository pins were read: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed binaries and
versions cannot be verified. Stack 8192 KiB; virtual memory unlimited;
neither limit was increased. `sha256sum` returned the hash above;
`rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1
(no matches). Static inspection is not compilation. No CI was started.

Next stage the exact frozen import closure and compile/replay this lemma
and dependencies; audit transitive axioms. Connect a quantitative bound
for the actual native transform to the raw n energy and compare this
larger direct sieve price with the manuscript reserve, or instead prove
the correctly normalized eigenspace ABL return with its 7/32 expense.
Full J, regular/holomorphic/continuous channels, both zero lanes, the
actual truncated tail, 14eta/28eta, 128C and threshold/reserve order
remain separately open.
