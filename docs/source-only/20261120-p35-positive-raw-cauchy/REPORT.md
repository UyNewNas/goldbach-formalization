# P3.5: original positive exceptional chart, weighted Cauchy

## Baseline and files

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`a82b635469662066922a05c8388a52d3800fa1b9` (confirmed remote HEAD before
work). The commit containing this report is the new SHA. Added only
`Part3OriginalPositiveRawCauchy.lean` and `REPORT.md` under
`docs/source-only/20261120-p35-positive-raw-cauchy/`. Candidate Lean
SHA-256: `dfea60d036e575a6bfc72f97b903806f63ce6aebcf173fc2174ac8332a952f01`.

## Exact mathematical candidate

Let `A` be `Slots D k upper`, the union of both endpoint-corrected
physical-level pieces and the actual **strict** exceptional native
basis indices at each level. For the original common clipped m row
`M_a`, original signed and level-dependent raw n row `N_a`, and the
actual same-sign native transform `H_a = nativeWeight(z_a,
spectralTest(ell,Y),i_a)`, set `W=threshold(V,Z)=max(V,Z^2/V)` as in
the existing source, with `V=2^j`, and write `tau_a=2 sqrt(1/4-lambda_a)`.
The proposed Lean theorem is

    exists omega, for every r, negativeM, Y,
      (sum_{a in A} |H_a conjugate(M_a) N_a|)^2
      <= (2+log(4V+1))^2
         * (J_(Z/2)(W,j,omega)+J_Z(W,j,omega))/4
         * sum_{a in A} (|H_a| |N_a| / sqrt(W^tau_a))^2.

The same witness omega serves both printed `(Q,2Q]` intervals and all
exceptional multiplicities, and is chosen **before** r, the sign and Y.
The original m phase and truncation are carried by `mFactor`; the n
functional is not a level-independent sequence. The test scale may be
specialized to the actual chart scale. For the actual positive trace,
the appropriate original `Row`, sign condition and `Y>0` are required
by its trace theorem; they are not needed for this finite algebraic
inequality. The actual trace uses `dMark=star(M)*N` definitionally.

Proof: `threshold_pos` and positivity of real powers make
`sqrt(W^tau_a)>0`. Each summand has the exact factorization

    |H_a conjugate(M_a) N_a|
       = (sqrt(W^tau_a)|M_a|)
         (|H_a||N_a|/sqrt(W^tau_a)).

Finite Cauchy on the same sigma index bounds its squared sum by the two
square energies. The existing `original_chart_J_one_phase` bounds the
first energy by the two displayed complete native `pascadiJ` sums with
the same phase. The second remains precisely the raw weighted n energy.
Neither the transform numerator nor the native cosine denominator is
dropped; `nativeWeight` retains both. No oldform identity, fixed-level
inequality for a fictitious common n sequence, 7/32 input, or full-J
estimate is assumed. The deduction does not rely on the parent
`high_positive_zero`/cosine candidate.

This is a finite exceptional **discrete positive-sign** reduction; it
does not itself bound the second energy, restore oldforms, or identify
the resulting sum with the entire original trace. In particular the
existing reduced-n fixed-level sieve cannot simply be substituted for
this raw energy. Its transition requires an eigenspace-wise ABL
oldclass argument with the actual transform and its square weight, and
the precise quantitative cost; the continuous return is separate. The
opposite sign uses `8*kTransform` and is not covered here. The theorem
leaves the two full J values unevaluated and does not extend the
initial AvgJ range. It is not the completed (24) or the 7/32 result.

## Sources and normalization

* `Part3OriginalExceptionalPostRemovalPair.lean`, blob
  `a038900816ae4e167afb9f46ace2e142440d386c`: actual `Slots`, m factor,
  reduced n factor, original one-phase theorem application and 1/4 from
  native `rhoK=2R`. The present n factor is raw and distinct.
* `Part3OriginalNativeCuspFunctionals.lean`, blob
  `88c3220e130f426f55f2f742d73b9572fb0faa8c`: literal clipped m and
  signed original n rows. `Part3OriginalMarkedPacketLimits.lean`, blob
  `b70b3e02d9924fbe44f9841f25693b403f381380`: `dMark=star(M)*N`.
  `Part3OriginalPrescribedPositiveTrace.lean`, blob
  `18715c3a04c31b972749878339b042b88704f5cf`: exact same-sign trace
  integrability/summability and sign/scale conditions.
* `AVGJ_APPLICABILITY.md` at
  `49a6978d28dabbb7eacaa73c872bb15238e7b4af`, blob
  `e4a4e3e8b5798d9f4616a297b9e1082d4130e36c`, and fixed-level-a report
  were reread. The m J input and n fixed-level input have different
  ranges and coefficient dependence. Parent `a82b635` records the
  strict-exceptional cosine candidate and its validation limitations.
* Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, is the chain
  pin. Distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`
  contains §7 (24) and §10(v)–(vii); this candidate only matches the
  finite exceptional piece explained above.
* No new external theorem was added. Pascadi v3, arXiv:2404.04239v3,
  Theorem J (3.34)–(3.35), ABL v1 Lemmas 3.1–3.2 and the numerical
  gap have the source/version/normalization boundaries in
  `AVGJ_APPLICABILITY.md` and the prior reports; the full applicable
  Lean suppliers, especially the full J, raw oldclass and return, remain
  unproved. The first fixed-level estimate is not a level average.

## Validation and next step

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including inherited candidate proofs. No Lean/Lake executable was
found on PATH, and the exact import closure is unstaged: no compiler was
invoked, so there is no compiler exit code or compiler log. The branch
configuration was reread: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native goldbach
`09b97db5764ade1246bfb77206baa1b124760958`. Actual installed binaries
and pins could not be verified. Stack limit 8192 KiB and virtual-memory
limit unlimited; neither was increased. `sha256sum` returned the above
source hash. `rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'`
on the candidate returned exit 1 (no matches). Neither is compilation.
No CI was launched.

Next, stage exact imports and elaborate/replay, then prove the exact
oldclass return for the new second energy and its transform bounds,
without disguising it as `reducedN`. Pay the independent J bound and
handle regular, holomorphic and continuous channels. The two zero
frequency lanes, actual truncated tail, different 14eta/28eta weights,
128C enlargement, original N-threshold order and final reserve remain
separate obligations.
