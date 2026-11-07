# P5.6 → h34 — noninjective original rejection event fibres and literal root-event weights

Date: 2026-11-07 UTC. Repository: `UyNewNas/goldbach-formalization`.
Dedicated working branch: `chatgpt/p5-h34-request-admission-20261105`.
**Verified preceding HEAD:** `0980a27fac7f065a0b223613851d28df2684fb10` (not initial `0a3fa5a`).
**New Lean source commit:** `f0f54d98443184cf0ab85922b4cc339b3e9fe695`.
**Lean blob read back:** `6197e369c566d2b4bd91147cade953a6e6b0814b`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`;
body: `paper/source/manuscript-body.tex` (pinned; no version switch).

**Status:** PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

## Actual manuscript-internal increment

Added `Part5OriginalH430ReceiverEventFibreWeights.lean`, 230 text lines,
8 proposed Lean theorem bodies and 4 definitions/abbreviations.

This independently advances the previously unpaid fourth receiver-root lane.
Prior source yielded an individual historical rank-two rejected-event witness for
each `ownPolicyFail` receipt, but the original `(U3/U4,p,q)` source can have
several different q and overlapping U3/U4 tagged receipts with the SAME
historical event label `(p,ell)`. Summing one event per distinct label would
therefore erase multiplicities.

New declarations:
- `EventKey`, `receiverEventKey`, `eventFibre`, `eventKeys`,
  `mem_eventFibre_iff`.
- `sum_by_event_fibres`: for **arbitrary signed per-receipt** weights,
  exact reindexing of every literal receipt in a finite source into key fibres,
  without injectivity or nonnegativity.
- `originalEventMass` and `key_weighted_fibre_sum`: a weight constant on
  a key `(p,ell)` contributes exactly its **fibre cardinality** times that
  weight, rather than merely one historical event weight.
- `frozen_fail_event_mass_by_fibres` and
  `rejected_frozen_fail_event_mass_by_fibres`: instantiate the exact
  historical rank-two kernel `1/(p-1) * 1/(ell-1)` separately on BOTH
  original rejection rules. The bad-prime function of one lane is never
  substituted for the other.
- `frozen_fail_key_has_historical_event` and
  `rejected_frozen_fail_key_has_historical_event`: for each distinct key
  represented by a real `ownPolicyFail` receipt, prove a conditional
  historical `FirstExitDepthState` witness with actual prefix `[ell,p]`,
  parity `true`, and precisely this root/event mass. The real global
  cutoff `z0 ≤ cap` remains an explicit prerequisite.
- `original_two_fail_lanes_signed_fibre_sum`: both original cutoff sources
  simultaneously retain independent arbitrary signed per-receipt weights.

The exact weighted equality has the mathematical form

```text
sum_{z in ownPolicyFail} W(p(z),ell(z))
  = sum_{(p,ell) in image(eventKey)}
      |{z : ownPolicyFail, eventKey(z)=(p,ell)}| * W(p,ell)
W(p,ell) = 1/(p-1) * 1/(ell-1).
```

This is genuinely **noninjective** occurrence accounting: event-key witnesses
do not imply that historical event-occurrences are distinct, that their
mass can be charged once per receipt, or that a full/selected/inherited owner
exists for every original arithmetic receipt. Such actual payment is still open.

## Scope and precise remaining proof obligations

1. Original U3/U4 full selected-count source, real root base/seed weights and
   root ownership (including the rank-one presieve incompatibility when
   `omega ≤ a`); literal full/selected/inherited filtering.
2. A genuine signed **payment** matching these event-key fibres and their
   multiplicity to actual historical event occurrences; all blocked,
   carrier-outside, and policy-pass lanes remain unpaid.
3. Actual all-action arithmetic CLOSED-CELL predecessor induction; literal
   base/switched/seed application; preceding source-only floor credit and
   fixed/Buchstab payments do not close these obligations.
4. Feedback-to-integral and outer Theta-count normalization; manuscript-local
   PP/same-rho compatibility; native-history proper/equality/inherited
   mass; ONE common nested causal430+11 refinement.
5. Staging, Lean elaboration, kernel replay, full transitive axiom audit and
   finite numerical430 certification.

The original c/K, root norm 7/2, row norm 12, same Q, actual alpha,
scalar/specified-cell distinctions and all occurrence/payment counts
are unchanged. No P1.4, P3.6, production file, dependency, toolchain, CI
or manuscript modification. No invented conditional count licence,
custom axiom, sorry/admit or proof escape. No CI dispatched.

## Verification and next action

GitHub authenticated readback confirmed the SOURCE commit SHA and blob.
One added Lean path was observed in the compare against the verified prior
HEAD. Static forbidden-token scan passed and text-only delimiters were
checked. **NOT RUN:** Lean parser/elaboration, Lake compilation, kernel replay,
transitive axiom audit, numeric430 replay, independent mathematical review.
These eight candidate proof bodies are **UNEVALUATED**; no new green credit.

**Next specific action:** match each genuinely retained first-excluded
`(p,ell)` key to its real full/selected/inherited *historical occurrence
family*, and prove that actual payable event multiplicity dominates (or
otherwise compensates) the source-fibre count with the prescribed signs.
Do not mistake one existent event witness for one paid receipt, and do
not turn a count-source equality into an axiom. Then continue native
U3/U4 CLOSED-CELL base/seed and integral source matching.
