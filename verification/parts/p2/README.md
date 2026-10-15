# P2 current source-only handoff

The current memory-failure repair is the lossless data split described in
[DATA_SPLIT.md](DATA_SPLIT.md). Use `split_paired_v2_certificate_data.py --check`
for the current frozen candidate. The prior candidate notes and producer below
are retained for provenance; the older producer targets the monolithic layout.

# Prior natural-sum candidate, 15 October 2026

Verification level: **SOURCE_ONLY**. No Lean, Lake, checker, environment audit or
CI was started by P2. The static producer check is not a formal proof receipt.

## Exact increment

`PairedV2NaturalSums` proposes these two unconditional finite identities, in
namespace `ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums`:

```lean
lower_numerator_sum :
  (∑ r : Row, (approximation r).lower) = 55858378943374979
upper_numerator_sum :
  (∑ r : Row, (approximation r).upper) = 55858409959907296
```

`Row`, `approximation`, the 17,572 witnesses, and `makeCertificate` are unchanged
from `1337e2db4712fb4a9f86add073f771f84b66d0c8`. The common denominator is 10^20.
These are the weaker, independently rounded natural witnesses already emitted
in `PairedV2FullCertificateData`, not the original JSON's Q160 endpoints.

The candidate consists of one generic row/list bridge, 12 independent numerical
blocks, and one assembly module. Each block holds at most 16 strips. Each
ordinary-kernel numerical theorem checks one strip's two natural endpoint sums,
with at most 191 rows. It sums the literal list directly, avoiding repeated
`getD` traversals. The generic bridge pays the list-length equality for all
186 strips and transports `Row`'s dependent finite sum to those lists.

The outer assembly uses a definitional ordered list partition and append-sum
identities. It does not make a 186-way dependent `fin_cases` dispatcher, reevaluate
all rows in one numerical decision, or add unproved assumptions. It preserves
all 186 strips, E0's 6,091 pairs and E1's 11,481 pairs, each exactly once.
The static manifest records these coverage checks; only successful Lean gates
can confirm the proposed formal identities.

## Recovery and resource rationale

The current workspace is a fresh cloud checkout. P0 confirmed on 15 October
that old user-computer-only Rows/Sums/Full drafts and the original failed sum
run are unavailable here. The published checkpoint explicitly excludes them.
No old draft or raw failure receipt has been claimed to be read or reused.
The 191-row pilot mentioned in the task is not a global success.

The existing strip checker source/receipt is retained unchanged. Its archived
receipt proves historical strict trust-level-zero compilation of all 186 row
checks, not acceptance of these new sums, a new replay, or an integral result.
The changed strategy is direct list sums plus independent modules and a small
algebraic assembly; no memory or thread limit is raised.

P0 should first compile `PairedV2NaturalSumRows` and `PairedV2NaturalSumsBlock11`
(the last block includes the longest 191-row strip), preserving its source
hashes and actual terminal/resource receipts. If that stage passes, compile
blocks 00–10 and the assembly sequentially at the standing -j2/-M4096 limit.
P0 must then obtain same-object kernel replay, complete declaration/type and
transitive-axiom/import-object audits before accepting the closure. A pilot
success is a stage receipt only; every block and the assembly remain required.

## Source regeneration and static checks

```text
python verification/parts/p2/generate_paired_v2_natural_sums.py
python verification/parts/p2/generate_paired_v2_natural_sums.py --check
```

The generator fixes the full certificate data, mask data and original JSON
SHA-256 values, checks that all parsed lists have the exact `firstU` lengths,
checks pair uniqueness and E0/E1 counts, and emits all 14 Lean files and a
per-strip/per-block manifest deterministically. It never invokes Lean and never
replaces the original data or original checker.

## Reuse boundary

The new finite assembly uses existing pinned Mathlib APIs. No external analytic
supplier or dependency upgrade is introduced. Pinned revision:
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, Apache-2.0, Lean 4.33.0-rc1.
The precise source was inspected at that revision:

- `Fintype.sum_sigma`: for finite `ι`, finite fibres `α i`, and an additive
  commutative monoid `M`, `(∑ x : Sigma α, f x) = ∑ i, ∑ j, f ⟨i,j⟩`.
  Source: <https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Data/Fintype/BigOperators.lean>
- `List.sum_ofFn`: for `f : Fin n → M` in an additive commutative monoid,
  `(List.ofFn f).sum = ∑ i, f i`.
  `Fin.sum_univ_succ` supplies the corresponding finite-sum recursion.
  Source: <https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Algebra/BigOperators/Fin.lean>
- `List.ofFn_comp' (f : Fin n → α) (g : α → β)`:
  `List.ofFn (fun i => g (f i)) = List.map g (List.ofFn f)`.
  Source: <https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Data/List/OfFn.lean>

The application is to `ℕ`, the exact existing sigma type, and unchanged list
entries; no integrability, analytic inequality or normalization premise is
hidden in this adapter. These are pinned-source API checks, not new audit
receipts for their imported proof-object closure. P0 owns that acceptance.

## Remaining work

After this finite layer is accepted, cast/divide its identities and combine
with the already existing full checker soundness and full strip checks in
`PairedV2FullCertificate`. Then pay the actual region/Buchstab/normalization
interfaces required by P1/P4. The existing local quantity carries K/80 on the
specified adopted fourfold fibres; it is not an upper bound on complete K.
The full eighteen-term same-policy coefficient, actual hLower/hUpper, and the
unconditional manuscript theorem remain open.
