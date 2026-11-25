# Compact04 polynomial, stored-query and permutation repair

Status: source repairs prepared; the next actual strict Lean diagnostic is
pending. No Lean/Lake invocation, cloud job, Git staging or commit was performed
for this repair.

## Actual evidence and existing work

Actual P1 job: `job_4c8505b542074aefb7fd6d98b9dd55ad`.
Diagnostic source: `086696e51088eb93942abf2fcc1ce48e148ad842`.
Full log: `p1-compact-04.log`, SHA-256
`f015edcbd99538444447dea15cf96860121c0972e4724f30211f0d91ffee86dc`.

The existing 619-record registry, SHA-256
`ee57e2a55adbf4564ed184eda0c4b4641c359be4da1113ed4ca8b8c090ee9388`,
contains no row for any of these three modules. No reusable old record is
proposed and no complete-closure or physical-cache gate is bypassed. The full
CI source audit was not repeated.

## Manuscript and source boundary

Read the already frozen manuscript at
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/numerical-appendix.tex`, directed arithmetic and
  `num:log-enclosure`, delayed function propagation and whole-query support,
  and the original first integral and compact-third partition discussion.
- The same numerical appendix's ordered-domain restriction: an asymmetric
  kernel is bounded on its ordered simplex without assuming factorial symmetry.
- `certify_extended_prefix.py`, the six branch coefficient triples, whole-box
  active-plane tests and the existing treatment of symmetric rectangles.

These checks retain the original integral, interval endpoints, outward rounding,
finite state update, stored-reader prefix and block layout, query arithmetic,
branch priority and point permutation. All computational definitions are
unchanged, including the historical logarithm parameters used through the
existing imports. The polynomial order-16 radius and the original positive-log
32/256 parameter families are unchanged.

The failures repaired here are expression/API and strict-lint failures. Existing
finite-sum distributivity, triangle inequalities, monomial integration,
rational-cast monotonicity and vector projection lemmas supply the same proofs.
No new mathematical assumption or omitted analytic estimate is introduced.
The polynomial file's existing limitation concerning comparison with the frozen
U1 numerical payload remains unchanged.

## Changes

### P2FirstIntegralPolynomialEnclosure

The complete log contains the three API errors at original lines 173, 189 and
215 in addition to the six diagnostics listed in the task summary; line 190 is
downstream of the missing triangle-inequality identifier.

- Original 116: sequence the existing `field_simp` and `ring` normally.
- Original 122: use `Finset.sum_mul_sum` to expand the product with the same
  outer i / inner j order as `approximant`. The two pointwise finite-sum proofs
  and the monomial algebra are retained.
- Original 173 and 189: use the available `abs_add_le` triangle inequality.
- Original 215: use the root-namespace `integral_pow` theorem, and correct the
  corresponding documentation reference.
- Original 265 and 269: unfold the same rational/real expressions, push casts
  and normalize the numeric coefficients. This avoids leaving the coefficient
  equality as an unclosed disjunction after a general `simp`/`ring` sequence.
- Original 298: apply `Rat.cast_mono` to the already proved rational radius
  inequality and simplify the four explicit cast operations.

The fixed mathlib pin is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
Primary-source API checks:

- [Integrals/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean),
  blob `335df785f4a6b999c0836dc5a67c359f7766d56a`: `integral_pow` is declared
  after `end intervalIntegral`.
- [Ring/Finset.lean](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Algebra/BigOperators/Ring/Finset.lean),
  blob `cdd6f7f559520a37ac4bb25734ca70c2a8bddf8c`: `sum_mul_sum` preserves
  the two sum indices in the required order.
- [Rat/Cast/Order.lean](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Data/Rat/Cast/Order.lean),
  blob `8fecc133d644463ae0ec9cb521dfa4e000e7e1ea`: `Rat.cast_mono`.
- [Rat/Cast/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Data/Rat/Cast/Defs.lean),
  blob `1ab80b6d3c4eb970e53bd7a56d999ee26ff61088`: separate `cast_one`
  and `cast_ofNat` rules.

### ActualThirdOriginalStoredNodeQueryLookup

Original 62 and 64: expose the definitionally reduced initial `Nat.rec` state
with `change` before the existing prefix case split. Original 82: expose the
successor update's two conditionals and rewrite both with explicit `if_pos`
proofs, then use the existing prior-row congruence and local update equality.
No recurrence, initializer, block count, array length, integer interpolation,
query error or returned denominator changes. The module still does not
construct an all-block checked table.

### ActualThirdOriginalP4ASymmetricBranchPermutation

Original 114 and 187: add the existing `Matrix.tail_cons` and `Matrix.head_cons`
simplifications. The unresolved third vector component then reduces to `t 2`,
allowing the existing ring proof to compare the permuted expressions. This
does not introduce symmetry of the ordered kernel or change candidate order.

## Static checks and exact identities

All 69 theorem headers and all 26 complete computational definition blocks
are byte-identical to the preimages; all imports are unchanged. The source scan
found no executable `sorry`, `admit`, `axiom`, `native_decide` or `unsafe`, and
no linter option is disabled. `git diff --check` passed for the three files.
These static checks do not claim successful Lean elaboration or acceptance.

| File | Before SHA-256 | After SHA-256 |
| --- | --- | --- |
| `ImbalancedChen/P2FirstIntegralPolynomialEnclosure.lean` | `c5d48026fc64fdb6cd423bf5e4b2bbc2d0d8a49758e52c729ca495c883ab46f3` | `3ef11ce876aaee8f6f6511384d14869673e580736ef38a9ebb5b0f6909a7c49e` |
| `ImbalancedChen/ActualThirdOriginalStoredNodeQueryLookup.lean` | `afe493afb7de5ede2acf8b3269efa60ec68e48cd8b7b1d4a64bf1e9733b28c78` | `ec39ac7c0804f5c2aeb427c17c1a62ef358696859a1667c146fa603ede85ac65` |
| `ImbalancedChen/ActualThirdOriginalP4ASymmetricBranchPermutation.lean` | `f25c5f7fb2ea4f37b5bc3c90147b8a12443ef4c4465c80da125dbc09bb283176` | `55def5e7916095c36f505d960248a3183ee6abcda983c34a18b40c08a8bf049a` |
