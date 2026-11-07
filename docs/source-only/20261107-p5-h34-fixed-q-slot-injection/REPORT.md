# P5.6 → h34 — fixed-physical-Q observed SLOT → actual rank-two LIST injection

Date: 2026-11-07.
Work branch: chatgpt/p5-h34-request-admission-20261105.
Verified prior head: 588122f6848b049fc1a610db6fd7d1a2f27c7473.
New mathematical source commit: fd45bcf10bda501e0564144495bced3765c7ebcc.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766,
paper/source/manuscript-body.tex (blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79).
Lean: v4.33.0-rc1; Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

PARTIAL_SOURCE_INCREMENT / SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Complete manuscript-internal h34 remains OPEN.

## Exact new manuscript-local proof coverage

New file Part5OriginalH430FixedQSlotInjection.lean (159 lines,
4 public candidate theorems, 3 definitions; Git blob 4ce133c5baa398ae6ba369795005c88383091760).
Imports only the preceding
ImbalancedChen.Part5OriginalH430PhysicalSlotListPositions.

Previously there was one actual Fin LIST position for each observed physical
(Q,p,ell) slot, but not a capacity injection across slots. This packet
restricts the exact finite observedPhysicalSlots to ONE actual physical
Q at a time. It DOES NOT assume U3/U4 roots share Q, and it does not
put distinct-Q frontier histories into one mass pool.

1. observedPhysicalSlotsAtQ: exact source filter by slot.1 = Q.
2. observed_fixed_q_slot_has_position: use the previous REAL
   observed_slot_has_actual_rank_two_position under the proved Q equality
   to obtain an indexed position in actualPhysicalRankTwoList N cap z0 Q lower.
3. fixedQSlotPosition / fixed_q_slot_position_prefix /
   fixedQSlotPositionMap: choose one existing bounded LIST position per
   source physical slot, and retain exactly [ell,p] as selectedPrefix.
4. fixed_q_slot_position_injective: if two chosen positions coincide,
   their [ell,p] prefixes coincide, so ell and p agree; both Q values
   are the same fixed Q. The original physical slot tuples therefore
   agree. This proves injection of distinct observed PHYSICAL SLOTS
   into literal Fin-bounded rank-two frontier positions.
5. observed_fixed_q_slots_card_le_frontier_length: derive the genuine
   finite per-Q cardinal bound via that explicit injection and the
   pinned finite-type/cardinality library.

No Nodup of the historical LIST is assumed. The injection does NOT imply
one unique list position per slot, and DOES NOT imply historical position
survival after the full/selected/inherited filters. Multiple original q
receipts and U3/U4 tags may still map to the SAME physical slot.
Earlier cross-tag and multi-q surplus ledgers are unchanged and unpaid.
The position map does NOT assign count weights, Euler signs, or owner mass.

## Source integrity and verification boundary

The source blob was fetched back from the GitHub object API.
The prior head was separately read from the branch git/ref before the
new source tree was submitted. Creation was a non-force fast-forward
with an expected-SHA lease. No production module, CI setting, Lean
toolchain, dependency, P1.4/P3.6 source, manuscript or earlier source-only
packet was modified.

Source-only static checks: candidate declaration presence, forbidden
proof-escape token scan, balanced raw bracket counts, and later Git
diff/readback. These DO NOT establish Lean parsing, elaboration, kernel
checking or mathematical validity. lean and lake were not available
on the current execution PATH; no local build or CI dispatched.
All candidate proofs and inherited numerical430 tables remain UNEVALUATED.
No transitive-axiom audit, kernel replay or independent verification.
No new green status and zero formal proof credit.

## Remaining exact manuscript-internal obligations

1. NEXT: inspect real full/selected/inherited history filters on actual
   bounded rank-two LIST occurrences. Prove which chosen indices
   survive and track deleted/rejected occurrences separately. Fixed-Q
   pre-filtered injection is NOT post-filtered owner capacity.
2. Match original (tag,p,q,ell) receipts and root weights to surviving
   owner positions, preserving every q occurrence, cross-tag collision,
   second-factor collision and signed payment multiplicity. Include
   physical z0, true lower/upper flags and phase consistency.
3. Keep explicit unpaid surcharge: surplus q, cross-tag collisions,
   cutoff, Rosser rejection, no-factor and non-event sources; establish
   correct signed Euler exit direction before allowing payment.
4. Complete request Buchstab/retention consumer and full-action
   CLOSED-CELL count induction, literal feedback/floor/base/switched/seed,
   integral/Theta/count matching, manuscript-local PP/same-rho and
   native-history proper/equality/inherit mass control.
5. Construct the SAME genuinely nested causal 430+11 refinement;
   later stage installation and Lean elaboration/compile, kernel replay,
   transitive-axiom audit and finite-table replay.

No new genuinely external theorem and no target-equivalent licence/axiom.
The frozen c/K, root norm 7/2, row norm 12, true alpha, physical per-root
same-Q history and original receipt-count multiplicities are unchanged.

完整 h34 稿内证明仍未闭合。
