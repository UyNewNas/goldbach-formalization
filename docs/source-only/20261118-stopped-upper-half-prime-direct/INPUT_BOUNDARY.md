# Input boundary — P1.4 actual stopped upper-half prime invoice

## Frozen pins
- Original manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`;
  `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Original coefficient constants `c=49044063/25000000`,
  `K=8452171/1250000`; upper exponent `rho0=19/96` unchanged.
- Lean `leanprover/lean4:v4.33.0-rc1`,
  mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
  native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.

## What is already implemented as source-only candidates
The full `a*(p::pre).prod` is used verbatim. `largeFifthRosserIndices`
remains the original filtered PLUS-beta index finset. `fifth.remainingAfter`
remains a List and therefore preserves repeated occurrences. The
`sharedRankFour` and `actualFifthSixthWithoutBoth` producers are
unchanged and continue using `receiverTest N` to generate events,
even when the arithmetic test F is specialized to the upper half.

The original receiver membership is reexpressed as the complementary
original additive prime `N-d`, subject to d≤N, primality and
`Nat.Coprime (N-d) N`. The strict full-q test X<d and strict
high-half condition N<2*d are both retained. The equality 2*d=N
goes to the lower half. This is not a new sieving source or a
claim that `N-d` is prime for all admissible d.

No theorem uses `w=N^(19/96)` as an actual producer fact. In
`roughPrimeUniverse N cap w z`, w is the LOWER endpoint and z the
UPPER endpoint. Its actual upper callsite remains to be proved.

## External inputs deliberately NOT implemented
- Name: frozen signed sharp-prime PP.
- Source/version: frozen manuscript above, anchors
  `eq:current-PP`, `lem:current-sharp-prime`,
  `eq:current-sharp-pi`.
- Accurate scope: original signed `rho`; complete primitive
  squarefree, N-coprime moduli q≤N^theta for theta fixed <1;
  smooth singleton/endpoint and exact H_N normalization, before
  N→∞. Its actual hypotheses and permissible test functions must be
  checked against the pinned manuscript at the specific callsite.
- Normalization: same frozen H_N and signed physical rho.
- Intended callsite: remaining lower-half full-q primitive
  discrepancy and eventual original same-rho signed payment.
- Status: REGISTERED_NOT_PROVED_NOT_CALLED; not a Lean axiom.

PNT, Mertens, BV, spectral estimates, independent compiler/density
reserve inputs, certified saved87 integral/numerical archives are
neither implemented nor assumed. Ordinary residual integral
identification, source-adaptation and reserve payment remain IN
SCOPE rather than being relabelled external.

## Evidence classification
New candidate source: SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Arithmetic diagnostic: 207345 exact (N,d) comparisons, no mismatch.
Lean, Lake and Elan local version commands: exit 127; matching
dependency closure unavailable. No kernel replay, transitive axioms
check, independent review or archive replay. No new CI or Codex.

Do not replace true signed upper-half prime counts by unrelated
unsigned prime bounds or infer an H_N gain merely from this finite
identity. Parent P1.4 stays YELLOW.
