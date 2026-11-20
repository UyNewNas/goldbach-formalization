# P5.6 / h34 — external-input boundary, quantitative physical floor

Pinned manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Current source: `Part5OriginalH430FutureQuantitativePhysicalFloor.lean`.
New external analytic inputs: **none**.

This manuscript-internal module reuses the exact original Q80 round
and its inherited source-only lemmas:
- `second_round_all_400_exact`, `third_upper_new_35_actual`,
  `third_lower_new_56_actual`, `fourth_upper_new_7_actual`;
- `original_iterate_le_of_le` for the original retention/max scan;
- mathlib `Fin`, `Finset.sum_le_sum`, integer order/addition and
  arithmetic tactics `omega`, `decide`, `norm_num`.

No new PNT, Mertens, BV, sieve or distribution theorem is constructed
or assumed. The exact transitive assumptions of reused pinned modules
have NOT been audited by a Lean kernel.

**Not externalised:** manuscript-specific analytic F, PP/same-rho,
the source filter/owner/selected U3/U4 identity, closed-cell induction
and native-history 430+11 causal nesting. A per-cell physical Q80
LOWER floor is not a consumer of these remaining obligations.
