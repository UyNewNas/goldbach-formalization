# Frozen receiver / adaptive minimum: static candidates

Status: **UNCOMPILED**. No Lean/Lake/compiler/kernel/type or axiom probe was
run. No live Member/main/P6/native/frozen source or build output was changed.
The sole Member source owner must adopt and validate these candidates.

`STATIC_RECEIPT.json` binds originals, candidates, complete declaration headers,
registered Git blobs, pins, and exact raw failure-log byte slices. Full source
copies are under `baseline/` and `candidate/`; `candidate.patch` has all edits.

| Module | Actual preimage SHA256 | Candidate SHA256 |
| --- | --- | --- |
| `P2FrozenReceiverCountActions` | `9ec450af567f8b2998d0bb1b28c8074f802cfba2d7515568509248072a5e222a` | `35011359884564111edf112be9ad59110895402185c4baa1671b730528f1a695` |
| `P5ZU11AdaptiveMinimum` | `96806dda28810b7461f4f9fd942a6960e8c1e8cfdb8a05333e063df51cb4a081` | `155130f7507a60e565eb45cd375dfde482d78aa48f479843403c2dc42646c040` |

All 53 complete source declaration headers remain byte-identical: 31 theorems,
21 definitions and one abbreviation. Every definition/abbreviation chunk,
import, numeric token, hypothesis and quantifier is unchanged. Both originals
and candidates use only LF line endings; line counts remain exactly 267 and
324 respectively. No public-header exception is needed.

## Existing-source search and preimage

The original Member sources exactly match their registered selected Git blobs.
Bounded exact-path history was checked before making the candidates; no existing
published fixed version was found. This is not an exhaustive all-repository or
all-history absence claim, and no previously excluded legacy families were scanned.

`P2FrozenReceiverCountActions` is selected from
`docs/source-only/20261028-resume-30f/certificate_enhanced/`, with the same
original bytes at published commits `c534093f` and `b2c20e78`. Main's canonical
path is absent; its physical docs source has the exact original hash.
`P5ZU11AdaptiveMinimum` exists canonically in main with the exact original
hash, also at `b2c20e78`. P6 has neither canonical source.

Only the original proof API applications are adjusted; no new counting,
analytic or recurrence theorem is introduced.

## Frozen receiver transfers

Both failures are untyped `have` applications of `markedChildren_sandwich`.
Its hypotheses determine `s` but do not mention implicit endpoint `t`, and
there is no expected proposition type from which Lean could infer that endpoint.
The candidate supplies `(s := s) (t := t)` in the two existing applications
inside `marked_actual_upper_transfer` and `marked_actual_lower_transfer`.
This is the same endpoint-instantiation repair already used for the analogous
`P2EnhancedActualBuchstabTransfer` calls, not a new source inequality.

The carrier, frozen receiver predicate `E a`, literal receiver prime labels,
marked-label multiplicities, original `Q`, strict child window and actual
child level are unchanged. The same signed remainder is retained; the file
does not claim uniform distribution for arbitrary `E` or license a table seed.
The original finite nonnegative marked sigma hypotheses are neither changed
nor extended.

Nov6 `sieve-appendix.tex:495–513` retains one positive marked family and its
common total level/physical child state. Lines 1054–1066 keep all finite
Buchstab consequences on those same counts. This candidate only supplies
the original endpoints to those already-written finite transfer proofs.

## Adaptive minimum, switched tag zero

The sole failure is in `weight_le_envelope`, tag-zero branch. The old
restricted simplification produces `if True then switched t else ...` but
does not reduce it. The candidate adds `ite_true` to that same `simpa only`
list. The pinned Lean source has
`@[simp] theorem ite_true (a b : α) : (if True then a else b) = a := rfl`
at `Init/SimpLemmas.lean:237`; its source SHA is recorded in the receipt.

All concrete switched/ordinary kernels, admissibility gates, bank, source,
cutoffs, original last-pair mask `E`, smallest-tag tie breaking and winner
cells remain unchanged. No local bound is replaced by a whole-U11 mean.
The switched option stays present even when the ordinary bank is empty;
overlapping alternatives are still compared by a minimum and partitioned,
not added.

Nov6 `argument.tex:755–763` compares the switched and admissible ordinary
kernels on one common four-prefix partition, with all full/selected square
conditions retained. The finite minimum and winner-cell accounting in this
file keep exactly that scope. It does not discharge the separately stated
analytic premises or full integral obligations.

The owner's next step is canonical guarded compilation, kernel replay and
all-public type/axiom validation. No such result is claimed by this package.
