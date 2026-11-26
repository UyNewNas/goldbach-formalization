# Task 2 fix 1 scoped source review

Reviewed `task-2-fix1-review.diff` and verified the revised source SHA-256 `f351018fd6ae22d26afd89a206f75aad454d41a29e5178c9bbc9ff7a8d9c17ea`.

**Specification preservation — pass.** The diff changes only two proof-body fragments of the second theorem. Both declaration types, witness choices, row coefficient, support cap and statement of the signed ledger are identical.

**Mathematical proof quality — pass.** At lines 148–150 the same target-normalized beta supplier is specialized to the same cap, policy and mesh. Its second projection gives the required signed upper bound. Rewriting the proved exponent identity `attachmentNu*(417/1360) = 417/5000` aligns its upper cutoff; the other names in `betaGap` and the physical row unfold to those same expressions. Removing the redundant simplification introduces no mathematical premise.

Lines 157–164 use `add_le_add` to add the two half-budget bounds. Each half is `(kappa/2)*singularSeries N/log N`; their sum is exactly the total budget by ring arithmetic. The ledger rewrites as `F − (V*loss + betaGap) ≤ D`. Since the sum of the errors is at most the total budget `K`, `sub_le_sub_left` gives `F − K ≤ F − (V*loss + betaGap)`. Transitivity produces the claimed lower bound with the correct sign. This conclusion does not require either signed density to be positive.

No further mathematical change requested. Strict elaboration, exact kernel replay and the complete inventory remain under the separate validation run.
