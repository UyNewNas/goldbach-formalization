# Current manuscript-to-Lean map

This checkpoint tracks the 10 October 2026 edition of *Imbalanced semiprime
representations of even integers* rather than the historical 8 October draft.

## Frozen source

- Manuscript repository: `UyNewNas/chen-imbalanced-semiprimes`
- Source commit: `ba6ec11d800eccc54406490631895e174de85766`
- Main body blob: `paper/source/manuscript-body.tex` at
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`
- Submitted PDF SHA-256 supplied for this run:
  `ef70ecef4b4c310449a43db1093859b5d3377e670d7c9dc9fa23619d7e54be9c`
- Constants: `K = 8452171/1250000`, `c = 49044063/25000000`

If the source commit changes, this map must be compared with the new theorem
statement before any later checkpoint is called current.

## Exact finite semantics

| Manuscript item | Lean interface | Status |
| --- | --- | --- |
| `eq:current-d12`, including `N-p > 1` | `Counting.D12` | Exact finite definition |
| `eq:current-db`, distinct additive primes | `Counting.Db`; `RationalPowers.RealDb`; `Db_eq_RealDb` | Exact for positive denominator |
| `eq:current-bb`, ordered bad factorization | `OrderedBad.badReceiver_iff_ordered_real_factors`; `CurrentMainTheorem.realBadReceiver_iff_realOrderedBadReceiver`; `RealB_eq_realOrderedBadPrimes_card` | Exact for rational and arbitrary real `b < 1`, including squares and strict endpoints |
| `sec:current-transfer`, finite ordered source and cutoff | `RealHalfProductSource.RealB_eq_realHalfProductSource_filter_card_add_small`; `realHalfProductPairs_card_eq` | Exact finite localization for arbitrary real `b < 1`; analytic pair-mass limit open |
| `eq:current-bad-mass`, `J_b = log (1/b)` | The finite source above is the input; no arbitrary-real mass-limit theorem yet | Open: prove the three geometric walls, uniform prime inputs and integral limit with no factor two |
| `eq:current-exact-subtraction` | `D12_eq_Db_add_B`; `Db_cast_eq_D12_sub_B` | Proved finite identity |
| `eq:current-normalization` | `SingularSeries.singularNormalization` | Product convergence, positivity and growth proved |

The current manuscript excludes receiver one from `D_{1,2}`.  Therefore its
terminal transfer uses `D12`, not the historical `D12Omega` interface and not
the receiver-one absorption lemma.

## Current terminal constants and Corollary 1.2

`ImbalancedChen/CurrentNumericalTransfer.lean` proves:

- `current_gap_74816964`, `current_gap_74816865`, and `current_gap_09` by
  kernel-checked rational arithmetic and Mathlib's logarithm-series bound;
- one conditional eventual lower bound for each of the three current
  exponents; and
- `current_corollary_simultaneous_of_manuscript_bounds`, which chooses one
  natural threshold before all later even `N` and returns all three claimed
  inequalities simultaneously.

These results close the exact arithmetic and terminal quantifier assembly.
They do **not** close the analytic hypotheses supplied to that theorem.

## Current main-theorem statement

`ImbalancedChen/CurrentMainTheorem.lean` extends the exact finite partition to
every fixed real exponent through `RealBadReceiver`, `realBadPrimes`, and
`RealB`.  The identity `D12_eq_RealDb_add_RealB` counts each additive prime
once and makes no rationality assumption on `b`.  `B_eq_RealB` proves that at
every positive-denominator rational exponent this is exactly the pre-existing
integer-power count `B`, rather than a parallel convention.

`current_theorem_1_1_of_manuscript_bounds` then states the literal lower limit
through all even natural numbers, with `1/2 < b < 1` chosen first.  It uses an
`EReal` liminf so no artificial global boundedness assumption is added to the
normalized count.  Its two analytic estimates remain explicit hypotheses.

For the arbitrary-real range of Theorem 1.1,
`realBadReceiver_iff_realOrderedBadReceiver` identifies the complement with
the literal ordered region
`r ≤ q ∧ (q : ℝ) ^ b < (r : ℝ)`.  Its converse checks both orders of every
prime factorization; `realOrderedBadReceiver_factors_unique` retains prime
squares and proves that sorting adds no witness multiplicity.  Consequently
`RealB_eq_realOrderedBadPrimes_card` is the exact finite input expected by the
remaining ordered bad-semiprime mass estimate.

`ImbalancedChen/RealHalfProductSource.lean` now continues this bridge for an
arbitrary real exponent.  For every real cutoff `T` and `b < 1`,
`RealB_eq_realHalfProductSource_filter_card_add_small` partitions `RealB`
into the inclusive half-product source after the literal
`m < N ∧ Nat.Prime (N - m)` filter and the complementary receivers `m < T`.
The filter preserves the manuscript's strict upper endpoint even though the
ambient analytic source uses `m ≤ N`.  `realHalfProductPairs_card_eq` counts
the unique ordered pair, including prime squares, so this reindexing adds no
factor two and no witness multiplicity.

This closes only finite reindexing and localization.  It does not yet choose
the manuscript cutoff `T_N = 2 N^(1-κ₀)`, prove its normalized small-tail
error, establish the required uniform prime-number and reciprocal-prime
limits, justify smoothing/partition of unity, or derive
`J_b = log (1/b)`.  Those later geometric and analytic steps use `0 < b`
(available from `1/2 < b` in Theorem 1.1), not merely the `b < 1` needed by
the finite complement identity.

## Remaining proof obligations

1. Formalize the restricted moving-residue distribution estimate with the
   actual common interval and common additive phase.
2. Prove the current positive upper weight and its density, yielding the
   coefficient `K` for the same physical source.
3. Prove the complete eleven-term lower-weight mean and paired deletion,
   including all `Y11` endpoints and repeated-prime errors.
4. Connect the adopted 17,572-cell same-mask-v2 certificate and the `7/3`
   refinement to the analytic functions; the superseded `12/5` gain must not
   be added.
5. Close the ordered bad-semiprime asymptotic with mass
   `J_b = log (1/b)` and discharge the three explicit upper-bound hypotheses.
   The arbitrary-real finite ordered-source localization and unique pair count
   feeding this estimate are now proved; the three real-coordinate walls,
   prime-distribution asymptotic and its uniform error are not.
6. Discharge the two explicit analytic hypotheses of
   `current_theorem_1_1_of_manuscript_bounds`.  The exact arbitrary-real-`b`
   partition and even-restricted liminf transfer are now formalized, but a
   conditional theorem or a zero-`sorry` finite core is not the complete
   manuscript proof.

The external `1.9728` lower coefficient belongs only to a withdrawn branch and
is not an input to the current theorem.

## External reuse audit (10 October 2026)

No checked repository currently supplies the complete arbitrary-real ordered
half-product mass theorem.  The closest exact reusable interface is
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/SieveTheory/Arithmetic/PrimeReciprocalLogScale.lean`:
`tendsto_primeReciprocalLogInterval` proves the genuine `Real.rpow` interval
mass `log (b / a)`.  At `a = b/(1+b)` and upper exponent `1/(1+b)` this is
exactly `log (1/b)`.  Its fixed-rectangle companion can support a finite
Darboux partition, but neither theorem supplies the moving product boundary,
the half-product fibre PNT step, or the required uniform error.

The dependency pin matches this repository.  Its underlying PNT and Mertens
results come from
`UyNewNas/analytic-number-theory-lean@88ee563ba0021702ea370b13bae7c7e7fec59657`,
whose audit covers those declarations with the standard three axioms.  Any
reuse here must still be minimally ported or adapted and re-audited
transitively.  Pinned Mathlib and the checked zeta-23 source do not contain a
drop-in half-product theorem; no relevant open branch, PR, or issue supplied a
more complete result.
