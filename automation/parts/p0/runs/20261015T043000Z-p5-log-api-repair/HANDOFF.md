# P5 LogDomain: bounded API/type repair

State: WAITING_FOR_P0. Request: REQUESTED. New source remains SOURCE_ONLY.

Frozen source SHA256: `b703f50531bc172dac4879da2aabc78898de248852eb097e79272d4c7a835f6d`.
Project closure SHA256: `14ba392f0c4ae326f038597698c4bb18ace058f002523e6a90744318dd156f00`.

The first strict compile failed in run 38680984398, job 116245255438, on source commit `178b018f86bd99dd016f3d5d09aa6ea90aa745b4`. The complete original compile log and exact P5 receipt are preserved here and bound by SHA256 in `REQUESTED.json`. The 34 preceding newly compiled modules succeeded; the target did not complete strict compilation, replay, or audit. No resource failure is diagnosed.

The complete log was read before editing. Each diagnostic is addressed:

- Deprecated `Set.mem_setOf_eq`: replace with the current `Set.mem_ofPred_eq` API.
- Unused density simp argument: remove only `one_div_mul_one_div`, as indicated by the linter.
- Rectangle integrability conversion: explicitly unfold the actual rectangle in the goal.
- Ambiguous product-form projections: annotate both `Fin 2` indices and both full continuous-linear-map types. The downstream elaborator recovery errors are not accepted proofs; no source `sorry` exists.
- Product wall application: explicitly simplify the concrete product form in the supplier result.
- Closed rectangle AE equality: expose the literal membership proposition before rewriting the proven rectangle equivalence.
- Loss-domain membership: expose the exact weak product inequality before simplifying subtraction by zero.
- Indicator domination: directly use `norm_indicator_le_norm_self` with the explicit strip set and actual reciprocal-coordinate function. The pinned Mathlib source and returned Git blob are saved in `norm-indicator-api.json`.
- Pointwise strip convergence: expose `eta < 833/2500 - (u+t)` from `eta in Iio ...` before `linarith`.

All 27 complete source declaration types and all direct imports are byte-for-byte unchanged against the first frozen candidate. The original candidate remains in the parent evidence directory. There are no new assumptions, changed constants or domains, disabled lints, weakened warnings-as-errors, or changed verification gates. The scope remains actual selector/log geometry and `1/(u*t)` boundary mass. Actual h248 kernel bounds, numerical coefficients, arithmetic means and hLower remain open.

Independent reviewer `/root/review_p5_log_domain_repairs` examined the entire error log, exact diff, new fixed-pin API and final source hash. It reported no static blocker. This is a read-only review, not compilation or kernel acceptance.

The producer performed only reading, source editing and ordinary static/hash scripts. P0 is the sole owner of the new strict compilation, original-object replay, full declaration/type/axiom audit, imported-object binding and publication. No Lean, Lake, checker, CI, installation, commit or push was run by this worker.
