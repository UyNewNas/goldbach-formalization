# P1.5 AF — AE actual acceptances and exact ReserveBranches proof repair

Original execution AE: `ca13f51c65d37870b96a6b1eb32ac30e92019fa2`. This publication preserves the two actual accepted owners and the original later4 partial failure, then publishes one proof-only correction. The whole P1.5 proof remains open.

## Actual accepted owners

| Owner | Owned / public | Original accepting run | Audit |
| --- | --- | --- | --- |
| `P5OriginalSingletonLowerTrimPaid` | 10 / 10 | AE `attempt-00000` | `e45153f0bb3e3268967a` |
| `P1OriginalSingletonAtlasTrim` | 11 / 9 | AE `attempt-00001` | `25adbe91b10ca6f615bb` |

LowerTrim first task `job_d3c60cd1867242fab3195258062e2290` passed normal, full-owned kernel validation and final stock. Later task `job_698d39e25f9d4800a912dc27a0bfe84b` reused LowerTrim, accepted AtlasTrim, then stopped on ReserveBranches. AtlasRoughPrime was not started. The later task remains exit 1 with no group final stock; AtlasTrim retains its original partial-run acceptance identity. All-owned validation includes private/generated declarations, and both audits reported only standard axioms.

The actual read-only collector `job_59ed19c844224b6482c5b5af45a84235` exited 0. It revalidated the accepted-prefix union of 153 sources / 151 dependencies and its 25 historical suppliers. The original first scope 119 and later4 scope 157 / 27 historical suppliers remain separate. Eight complete historical evidence trees, both owners' original six receipts, source-plus-five/full21 observations and ten extra original file pins were preserved. Its two public summaries are published without changing their source commit or accepting run.

## ReserveBranches correction and actual probe

The original normal failure was at line 43 of `trim_exact_product_zero`. An unrestricted `Real.rpow_sub hTR` rewrite matched the left-hand denominator before the intended right-hand outer power. The only proof change specializes the two explicit exponents:

```lean
Real.rpow_sub hTR 1 (1 - κ₀)
```

The actual installed mathlib signature was read from P1 as task `job_9884ec4a40624ae19797377fd15aafa2`; it takes the two exponents explicitly. The one import, eleven declaration headers and all premises are unchanged. No axiom, sorry or new target hypothesis is introduced. The source changes from 8183 bytes to 8197 bytes.

Actual whole-module no-output probe `job_27c97559f895492480be94780caf0551` exited 0. It submitted the complete candidate through the original serializer and guard, rebuilt no project modules, requested no output objects, and preserved both original AE owners, their 153/151 accepted prefix, the 157-source joint scope, 160 watched modules, 360 source slots, 3360 artifact slots, eight evidence trees and six inherited external evidence pins. This probe does not install the canonical cloud source and does not constitute normal/kernel acceptance.

`REPAIR_CANDIDATE_before_probe.json` preserves the original pre-probe metadata. `REPAIR_CANDIDATE.json` adds only the actual successful probe identity to that same source candidate.

## Next exact execution scopes

The next execution publication will bind the two original AE owners as historical priors and install only ReserveBranches. The selected first ReserveBranches closure is 140 sources / 139 dependencies, with 21 historical suppliers; the subsequent ReserveBranches + AtlasRoughPrime closure is 144 / 142, with 24 historical suppliers. Both watch 152 modules under the unchanged selected-run policy. The already accepted 153-source prefix is not a subset of those remaining scopes, so the updater must verify it separately and preserve the original 157-source union.

The after-collector checkpoint in `../p15-ae-status/CONTINUE_WORK_AFTER_COLLECTOR.md` records the exact 16/21 formal-target status before this new probe. Its older frozen checkpoint is also retained. The three proper-power owners, nineteen P3 adoption holds, missing original FixedM bytes and the literal historical medium supplier remain unresolved. Source-only residual/outer-payment work does not close those boundaries; `hSmoothSignedPP` remains a real premise in the compiled synthesis interface.
