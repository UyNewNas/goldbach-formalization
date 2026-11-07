# P5.6 → h34 — real rank-two signed historical exit and receipt surplus

Date: 2026-11-07 UTC.
Repository: `UyNewNas/goldbach-formalization`.
Exclusive h34 branch: `chatgpt/p5-h34-request-admission-20261105`.
**Verified prior HEAD:** `00b30d9838d0f90dc5e178b99958ee29849ef91a`.
**New Lean source commit:** `c53946bdc67f9579ec9e00f628b78263cc035d69`.
**Source blob:** `71330c80672b6d6bdba1f50a5244e91ed77793a3`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`. No manuscript version, target, or parameters changed.

**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**

## New mathematical source

Added `Part5OriginalH430RealSignedExitPayment.lean`: **215 lines,
4 public theorem bodies, 1 private helper proof body, 3 definitions**.
This follows the previous actual `historicalRejectedEvents` rank-two capacity theorem, not
the original 20261105 seed, and does not duplicate the prior per-fibre bare mass ledger.

1. `actualRankTwoHistory` filters exactly the original recursively generated
   historical rejected occurrences with prefix `[ell,p]`, using the original
   `ordinaryRosserRetainedPolicy`, `roughPrimeUniverse`, parent sign=false and
   root weight `1/(p-1)`. No artificial per-q event is introduced.
2. `original_fourth_lane_key_unique_signed_event` uses the two existing
   conditional original source-event witnesses and the ACTUAL rank-two
   length=1 counts to identify the unique `FirstExitDepthState` for
   every key in the union of both real fourth-lane source sets. The original
   `z0≤cap` gate is not discharged or erased.
3. `original_fourth_lane_key_signed_euler_exact` rewrites the matching
   historical correction using the literal remaining suffix of that state:

       actualRankTwoSignedExit(p,ell)
         = - W(p,ell) * Prod_{q in actual remaining suffix} (1 - 1/(q-1)),
       W(p,ell) = 1/(p-1) * 1/(ell-1).

   The negative sign comes from `historicalExitValue` and the witness's
   actual positive event sign, not a guessed unsigned kernel. No Euler
   product is set equal to one, and no sign/size inequality for the
   product is claimed.
4. `two_source_signed_history_gap_ledger` and its
   `original_fourth_lanes_signed_history_gap_ledger` specialization
   establish an exact signed account for both original (tag,p,q) receiver
   sets. It separates (a) one actual rank-two historical signed
   correction per DISTINCT key, (b) the bare mass minus this actual
   signed correction for each key, (c) cross-lane repeated keys, and
   (d) within-lane `card-1` extra q/tag occurrences. All are real
   equalities; an overlap or surplus is NOT silently declared paid.

The new discrepancy `actualRankTwoExitGap` is an explicit book-keeping
difference, not an assumed analytical upper bound and not a new input.
In particular, the bare mass `W(p,ell)` alone does not pay the original
arithmetic receiver mass, because its historical sign and Euler tail differ.

## Precise outstanding manuscript obligations

- Prove a genuine direction-and-size payment for the **actual signed
  Euler correction**, using the literal original q-weight/count source,
  not a bare positive event mass. Resolve same-key within-lane q/tag
  multiplicities and cross-lane overlap without double use of an event.
- Link real historical events to the complete **full/selected/inherited**
  owner and gates. The packet's rank-two fixed root is not that join;
  `gateBlocked`, carrier-outside and policy-pass exceptions remain.
- Complete original U3/U4 `selected-count` source, true root count
  weights and presieve stage, native CLOSED-CELL arithmetic induction,
  base/switched/seed/floor and exact feedback-integral/Theta-count join.
- Complete manuscript-local PP/same-rho and native-history
  proper/equality/inherit mass, with one common 430+11 nested causal
  refinement. All of these remain INTERNAL, not external hypotheses.

P1.4 and P3.6 remain untouched. Original c/K, root norm 7/2,
row norm 12, original alpha and same Q, integer occurrence multiplicity,
specified-cell/scalar distinction and source sign rules are unchanged.

## Verification and exact next action

Authenticated remote commit/blob readback verified new source and
its single-file diff: 215 inserted lines, no deletions.
Static forbidden proof-escape scan and comments-aware delimiter scan
passed. Neither check is a Lean compiler or kernel replay.

**NOT RUN:** Lean parser/elaboration/build, kernel replay, transitive
axiom audit, numerical430 certificates, independent checking and CI.
Inherited finite guards are **UNEVALUATED**. Formal completed-green credit: ZERO.
No external analytical proof is expanded; no new axiom, sorry, admit,
unsafe/native proof escape, build upgrade or CI setting change.
Commit messages retain [skip ci].

**Next exact action:** use the true signed Euler-product event value
and the actual full/selected/inherited history owner to derive a
non-double-counting inequality against literal U3/U4 count weights.
Keep the new gap, q/tag fibre surplus and cross-lane overlap explicit
until a real bound pays them; do not create more bare-mass proxy owners.
