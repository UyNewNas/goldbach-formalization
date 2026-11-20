# P5.6 → h34 — retained U4 overlap forces a global true-Fin collision-capacity deficit

Date: 2026-11-20.
Repository: UyNewNas/goldbach-formalization.
Continuing dedicated branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified incoming remote HEAD: `d028dd1f5c3fda6cf66bd6d7247d4d3640201cbf`.
Final corrected manuscript-internal Lean source commit: `42094a9fa2e7668aa43067ffbfc508428ce6749c`.
Source blob: `05b88771880f885f127df7527a86fc2b3b2b33d2`.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766`.
Pinned Lean: `leanprover/lean4:v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Why this is new

The prior `ActualFinTaggedCollisionExcess` packet established the exact finite
identity “retained original tagged arithmetic receipts = occupied true Fin
positions + q/tag excess”. It did not derive a strictly positive total excess
from an original arithmetic witness. The earlier `U4ActualFinDoubleTag`
packet proved that any *genuinely retained* original U4 overlap contains two
distinct original tags at one real Fin occurrence, but did not link that
witness to the GLOBAL observed-Q collision ledger.

This packet connects the two, while keeping the actual per-root physical Q,
real rank-two Fin position, and both distinct U3/U4 tagged arithmetic
receipts. The import is from those actual prior sources, not an invented
root owner, arbitrary count mask or new oracle.

## Exact source increment

File: `Part5OriginalH430U4GlobalCollisionCapacityObstruction.lean`
(151 lines, 3 public candidate theorem declarations and one private finite
Nat sum lemma).

1. `original_retained_u4_forces_fin_extra`: conditional on `2 ≤ N`,
   `x ∈ originalPairs N .U4`, and the actual `Sum.inl x` original tagged
   receipt being retained, there exists an ACTUAL rank-two Fin position at
   the actual slot Q with `extraTagged ≥ 1`. This uses the two-tag plus-rest
   theorem and the exact Nat-to-real multiplicity cast.
2. `original_retained_u4_global_extra_ge_one`: the same actual witness has
   `slot.1 ∈ observedReceiptQs`, so the full GLOBAL sum of q/tag excess
   over ALL observed physical Q and actual Fin positions is at least one.
3. `original_retained_u4_exceeds_occupied_fin_capacity`: combining the
   global strict excess with the prior exact conservation law gives:

       occupied_true_Fin_positions + 1 ≤
         retained_original_tagged_arithmetic_receipts

   This is a **strict one-owner-per-occupied-position capacity obstruction**.
   It demonstrates that merely identifying a retained history position
   cannot fully pay the original overlapping tagged source.

The witness is **conditional**, not proof that such a retained U4 pair
exists for every even N. “At least one” is a literal original tagged
receipt count, not a 7/2 root Euler mass, an integral, nor a quantitative
global bound sufficient to close h34.

## Engineering / validation facts

The connected GitHub repository grants push permission. Prior h34 source and
original request-admission REPORT/REGISTRY/EXTERNAL_INPUTS were read, along
with current branch head and related older source reports to avoid
regenerating already-covered tagged source or arbitrary-filter ledgers.

Source was committed by two fast-forward source-only commits:
`6a5dd88565f8744ddbbcd659798e2412344de5e6` created the candidate;
`42094a9fa2e7668aa43067ffbfc508428ce6749c` fixed a real-versus-Nat
inequality casting issue in the written proof body. The corrected source
blob is the authoritative candidate. Compare against `d028dd1f5c3fda6cf66bd6d7247d4d3640201cbf`
shows exactly one added h34-owned .lean file, +151/-0.

Runtime PATH was actually checked: no `lean`, `lake`, `elan`.
Native `git ls-remote` cannot resolve github.com. The pinned source-only
import closure is not staged locally, and no existing workflow was run
because its unrelated jobs would not compile this uninstalled module.
There is NO Lean parsing/elaboration, successful compile, kernel replay,
transitive axiom audit or finite certification for this packet. All new
declarations are CANDIDATE_UNCOMPILED; no green status.

Source-side checks only: additive owned path, Git object and branch compare,
simple balanced parentheses and forbidden-token scan. Those are not Lean
verification. Existing imported theorem bodies are likewise not promoted
to verified status.

No changes to P1.4, P3.6, production modules, fixed manuscript, c/K,
root norm 7/2, row norm 12, true alpha, same-Q, CI, Mathlib, toolchain,
430+11 budget or default branch. No new genuinely external theorem input.

## Remaining manuscript-internal debt / next exact action

- Install/stage pinned source-only import closure, incrementally compile
  this module and its two direct imports, then kernel-replay and audit
  transitive axioms; repair any real elaboration errors in owned files.
- Prove actual original full/selected/inherited causal owner, first exit,
  allowed multiplicities and root weight 7/2, distinguishing physical Fin
  position from tagged arithmetic receipt; determine the payable capacity
  covering the positive U4 excess, and bound the four outside-position
  rejection lanes with correct signed -1/4 orientation.
- Prove original U3/U4 selected-count identities, valid native-history
  mass, strict F CLOSED-CELL seed/base/all-action induction, correct
  feedback integral/Theta/count and manuscript PP/same-rho instances.
- Finish seven-integral strict >= 0.650 certification (previous candidate
  0.590), and one common 430+11 nested causal refinement. Unevaluated
  finite certificates remain UNEVALUATED.

**完整h34稿内证明仍未闭合。**
