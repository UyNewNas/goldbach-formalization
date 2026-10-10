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
| `eq:current-bb`, ordered bad factorization | `OrderedBad.badReceiver_iff_ordered_real_factors`; `B_eq_orderedBadPrimes_card` | Exact, including squares and strict endpoints |
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
6. State and prove the even-restricted liminf form of Theorem 1.1 from those
   inputs.  A conditional transfer or a zero-`sorry` finite core is not the
   complete manuscript proof.

The external `1.9728` lower coefficient belongs only to a withdrawn branch and
is not an input to the current theorem.
