# P5.6 → h34 — actual selected strict Q80 winning action

Date: 2026-11-20.
Repository: `UyNewNas/goldbach-formalization`.
Continuing h34 branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified incoming branch HEAD: `97b3109b25965a528c20114555643131c0e719e5`.
New source commits: `3389ef6dbbf8f4f48a8a889fc6f31296f0cb9867`, corrected `3221bbf93afa40fee73d751b2c130b09b7aff68a`.
Final candidate source blob: `c002aa94bf2bba3ecf7606cfa034baf8cf85dd85`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Fixed Lean: `leanprover/lean4:v4.33.0-rc1`; fixed mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT · SOURCE_ONLY · UNCOMPILED · UNEVALUATED · FULL_H34_OPEN.**

## Mathematical source increment

`Part5OriginalH430LiteralUniqueStrictWinner.lean` adds one provenance predicate,
five public theorem candidates and three private inductive helper theorem
candidates (260 physical lines including trailing newline). They use the
**actual** original `roundDecision`, `ordinaryDecision`, `offerRow`,
`scan`, `roundTable`, `iterate`, original 106 bank targets and
unchanged Q80 integer rounding. No substitute producer is introduced.

* `ordinary_origin`: actual retention/Buchstab decision starts from the
  predecessor integer and only switches on a **strict** improvement; the
  physical Buchstab cutoff remains upper `max 50 (i-49)` versus lower `i-49`.
* `bank_offer_origin` and `bank_scan_origin`: the authentic upper-only
  left-to-right 106 bank scan preserves the winner's selected origin and
  integer value. Losing candidate offers never become an extra chosen action.
* `literal_round_winner_origin`: the final decision is old-value retention,
  an enabled Buchstab suffix, or an actually targeted bank row, with a strict
  gain above the predecessor in either non-retained case.
* `literal_round_strict_iff_chosen_nonretention`: original cell numerator
  increases **iff** the final choice is not retention.
* `literal_round_strict_chosen_source`: a genuine increased cell has ONE
  final selected Buchstab or targeted bank row with exact winning numerator,
  rather than merely an arbitrary offered row that exceeds the old cell.
* `actual_increment_zero_iff_retained`: at every actual `g : Fin 430`,
  the Q80 integer increment is zero exactly when the final choice is retention.
* `actual_positive_increment_exact_chosen_delta`: a strictly positive
  increment is exactly the winning suffix minus predecessor, or the chosen
  original bank candidate minus predecessor, at the SAME physical cell.

This advances from the earlier existential "some increasing offer" test
(`97b3109`) to the **final winning** physical choice and its exact positive
numerator delta. The strict-choice invariant prevents crediting a losing
bank offer, a tie or retained mass as an additional generation payment.

## Essential mathematical boundary

The above is a **physical** Q80 producer ledger. It does NOT yet prove
original arithmetic selected U3/U4 q/tag source ownership or injection,
the original root weight, allowed repeated occurrence/payment multiplicity,
inherited/full/selected and rejection filters, or first-exit identification.
Nor does it prove the frozen analytic F upper envelope, all-action CLOSED-CELL
induction, valid seed/base payment, seven-integral strict >=0.650, manuscript
PP/same-rho, native-history, Theta/count, or one common 430+11 refinement.
The inherited 0.590 integral candidate is not a replacement for >=0.650.
No genuine external theorem is newly postulated.

## Validation and concurrency

* Checked repository write permission, continuing h34 branch HEAD and incoming
  REPORT/REGISTRY/EXTERNAL_INPUTS, source-only ancestry and original literal
  producer definitions before writing.
* Source committed in this h34 branch only. A source correction rewrites the
  authentic targeted-offer guard before proving bank provenance; it does not
  weaken or change any statement.
* After correction, the GitHub blob was read back as
  `c002aa94bf2bba3ecf7606cfa034baf8cf85dd85`; static source scan found
  **no** sorry/admit/axiom/unsafe/native_decide tokens in code; punctuation
  delimiter counts were balanced. The new file contains eight theorem
  declarations and one local definition.
* Current execution container: `git` available; `lean`, `lake`, `elan`
  absent; native GitHub HTTPS could not resolve its host. The fixed Lean
  import closure is not staged in this container. No compilation, kernel
  replay, transitive-axiom audit or finite Lean certification was executed.
  Every new proof is a CANDIDATE, not a verified theorem. Existing branch
  status checks do not certify these source-only bytes.
* No production file, CI configuration, toolchain, dependency, manuscript,
  c/K, root norm 7/2, row norm 12, alpha, same-Q, P1.4 or P3.6 was changed.
  No force-push or merge; no external proof implementation.

## Exact remaining next actions

1. Stage all fixed source-only ancestors under the frozen toolchain and
   compile the eight candidate declarations and imports. Fix real Lean
   elaboration errors and recompile, then replay in kernel and audit axioms.
2. Use the selected physical winner/delta to connect each admissible
   event with its original U3/U4 q/tag source, root weights, owner,
   first-exit/selected/full/inherited/rejected filters and exact permitted
   occurrence multiplicity. Do not charge every winning physical table
   cell as an arithmetic count.
3. Independently pay genuine frozen F pointwise ceilings, correct base/seed,
   actual Buchstab/bank positive branch bounds and the 430-step CLOSED-CELL
   induction, then PP/same-rho and the common 430+11 causal refinement.

**完整h34稿内证明仍未闭合。**
