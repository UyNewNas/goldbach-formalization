# P1.4 — exact upper-half ORIGINAL prime invoice in the actual fifth stopped signed tail

## Baseline and actual source inspection
Previous verified P1.4 HEAD: `40a86d315006e67349f08b5b9c842e3b3c3d72e2` on
`chatgpt/p1-full87-upper-endpoint-direction-audit-20261118-1710`.
New independent task branch:
`chatgpt/p1-full87-stopped-upper-half-prime-direct-20261118-1810`.

The predecessor's complete REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and
Lean source were read. Also read actual `ImbalancedChen/RoughPrimeUniverse.lean`,
`ImbalancedChen/ChenInitialPrimeSource.lean`,
`P4AOriginalFull87FifthSignedPrimitive.lean`,
`P4AOriginalFull87CommonSixthSignedKernel.lean`,
`P4AOriginalFull87PlusBetaPowerFilter.lean`,
`P4AOriginalFull87UpperHalfPrimeSwitch.lean`, and the frozen manuscript.
Root/docs/docs-source-only AGENTS.md do not exist at this base.

This packet deliberately retains the prior correction:
`roughPrimeUniverse N cap w z` has LOWER `w ≤ p` and UPPER `p < z`.
The manuscript upper exponent `rho0 = 19/96` must NOT be substituted for w.

## New exact arithmetic conclusion and why it matters
For the genuine target-deleted prime source `chenPrimeReceiverSource N`
there is an unconditional finite characterization, for all natural N,d:

  d ∈ chenPrimeReceiverSource N
    ↔ d ≤ N ∧ Prime (N-d) ∧ Coprime (N-d) N.

The original source is an injective image of additive primes P at N-P;
this is NOT a replacement or enlarged source. It explicitly keeps centre
prime deletion.

For EVERY full integer d with N < 2*d, the prior original-receiver
singleton theorem gives

  receiverTest N d = 1_{d≤N, Prime(N-d), Coprime(N-d,N)}.

The half-open complementary equality case 2*d=N is assigned to the lower
part. Consequently the exact PLUS-Rosser surviving summand on an original
fifth history `pre` and sixth-prime occurrence `p` is

  beta_plus(a) * 1_{
     X < a*(p::pre).prod
     AND N < 2*a*(p::pre).prod ≤ 2*N
     AND Prime(N-a*(p::pre).prod)
     AND Coprime(N-a*(p::pre).prod,N)
  }

where `a` still belongs to the original
`largeFifthRosserIndices N cap w X pre`; no double filtering and no
coefficient replacement.

`common_sixth_upper_half_prime_invoice` preserves the literal
`fifth.remainingAfter.map` (all occurrences) and the exact
`signedTreeCoefficient true fifth.massAfter`. This is a genuine stopped
rather than fixed-physical-rho invoice.

The principal new identity uses the ACTUAL fixed stopped event population
(the original `sharedRankFour`, `actualFifthSixthWithoutBoth` evaluated
with receiverTest, and unchanged policies):

  actualFixedSignedFifthTail(..., receiverTest N)
    = actualFixedSignedFifthTail(..., upperHalfComplementPrime N)
    + actualFixedSignedFifthTail(..., lowerHalfReceiver N).

This is exact finite algebra with original signs. It does NOT assert that
either half is small, that both independent reserves have been paid, or
that the actual dynamic-parent/saved87 work is complete.

## Finite checks and verification
Local Python diagnostic enumerated 207,345 (N,d) pairs for
0≤N≤600 and 0≤d<N+45. For each, it compared genuine target-deleted
receiver membership against the complementary-prime/coprime test, and
for N<2*d compared the original divisible receiver fibre count against
that indicator. Zero mismatches. This is a diagnostic, NOT Lean checking.

The pinned toolchain is not installed in the available worker:
`lean --version`, `lake --version`, `elan --version` each exit 127
(command not found). No dependency upgrade, fetching a different
toolchain, CI run, Codex, or remote workstation access was attempted.
The new source-only imports have NOT been staged as a compilable Lake
module. Therefore **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**.
Proof elaboration (especially the Finset image and sum rewrites),
kernel replay, transitive-axiom audit and independent review are open.
Static forbidden-token scan finds no new axiom/sorry/admit/
native_decide/unsafe escape; this does NOT prove kernel soundness.

## Frozen scope and remaining yellow obligations
- Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`;
  `paper/source/manuscript-body.tex`, blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
  rho0=19/96; c=49044063/25000000; K=8452171/1250000 unchanged.
- Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
  `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
  `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.
- The actual upper producer's distinct lower w and upper z parameters
  still require a source-level high-level caller mapping.
- Upper-half prime invoice still requires quantitative same-rho payment
  relative to H_N; the lower-half complete-modulus receiver, full
  primitive discrepancy and modulus-/centre-prime corrections remain.
- Ordinary residual integral, saved87 actualParent numerical archive,
  unfiltered sixth BOTH, RAW eighth, rank9 changed/tagged and independent
  compiler/density reserves remain OPEN.
- Frozen external sharp-prime PP is only REGISTERED, not called/proved:
  full primitive squarefree q≤N^theta at fixed theta<1, same signed rho,
  H_N normalization, smooth singleton and endpoint hypotheses.

## Next concrete proof operation
Using the exact sixth occurrence and original a-index, obtain a
quantitative upper-half original prime invoice (without replacing the
signed coefficient by a positive one) and compare with the PP-admissible
lower-half full-q band after exact prefix/coprime corrections. Prioritize
Lean elaboration if the matching pinned closure becomes available.
Do not promote the parent P1.4 status from YELLOW.