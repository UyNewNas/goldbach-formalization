# AG entrypoint — two original AE acceptances

AG's local runner and manifest are frozen against the actual AF source
publication `b06429e9c2d8fbd5c654105d5f4e44f26c0865f4`. Seven focused dual-prior
tests passed. This prepares formal ReserveBranches execution; it does not grant
ReserveBranches or RoughPrime a new owner acceptance.

## Original identities remain separate

The unchanged predecessor is AE `ca13f51c65d37870b96a6b1eb32ac30e92019fa2`,
whose source anchor is AD `e91af3a5c407bdeea243af7dd3c4248949d83e9b`.

| New historical prior | Original accepting run | Owned / public | Own closure | Original group result |
| --- | --- | ---: | ---: | --- |
| LowerTrim@AE | `attempt-00000` | 10 / 10 | 119 | Successful; final stock retained |
| AtlasTrim@AE | `attempt-00001` | 11 / 9 | 153 | Partial failure; no final stock |

LowerTrim retains job `job_d3c60cd1867242fab3195258062e2290` and audit
`e45153f0bb3e3268967a`. AtlasTrim retains job
`job_698d39e25f9d4800a912dc27a0bfe84b` and audit `25adbe91b10ca6f615bb`.
Original later4 reused LowerTrim, accepted AtlasTrim, failed ReserveBranches,
and did not start RoughPrime. Its original source scope remains 157 with 27
historical suppliers; original first scope remains 119 with 3 suppliers.

The actual AE collector `job_59ed19c844224b6482c5b5af45a84235` jointly read
153 sources / 151 preserved dependencies and 25 historical suppliers. This joint
scope is separate from each own closure and the original run scopes. Both
public summaries retain their exact original RESULT/WORKER, context, six
receipts, source plus five outputs, and full21 artifact bindings. Revalidation
creates no new acceptance and does not rebind receipts to AF or AG.

## Frozen production candidates

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `run_selected.py` | 343325 | `0440906dfc3caa894ff7226e53ad42be54adda1d5879bd1a72cad578a3b3612d` |
| `SOURCE_MANIFEST.json` | 369103 | `21c0b14701a2123edab7353aa27dbb9c950427a805d75aaa3562c6033eb137f9` |
| `ae_prior_adapter.py` | 36376 | `1354bd2d2ac8b64251718da4f6fe9b1add2d52097f9cab1b6967ba5c1f3bb952` |

`build_candidate.py` derives exactly three functions from the existing U
dual-owner functions. The verifier reverses only fixed names, labels and joint
read scope to recover those U function texts exactly. Of AE's 64 functions,
**62 are byte-for-byte unchanged**; only `source_manifest` and `preflight` gain
the new classification/dispatch. The resulting runner has 67 functions.

The 14 older prior identities, 359 other source rows, all imports, 303 fixed
policies and 19 P3 HOLD dependencies are unchanged. Only ReserveBranches source
and its repair provenance change. Its single proof splice preserves 11 headers
and one import. The repaired source is 8197 bytes, SHA256
`d5945aa39ab54bc5c4aeb529a96299e7ab3bcf0c4fcb946296d3a697753a2bb7`;
probe `job_27c97559f895492480be94780caf0551` succeeded. The actual final repair
review and both public summaries are fixed to AF's published bytes.

## Actual next selections

| Selection | Sources | Dependencies | Artifact watch modules | Historical suppliers |
| --- | ---: | ---: | ---: | ---: |
| ReserveBranches first | 140 | 139 | 152 | 21 |
| ReserveBranches + AtlasRoughPrime | 144 | 142 | 152 | 24 |

Neither selected closure reaches LowerTrim or AtlasTrim. They remain registered
historical priors; the original scope rule performs live owner/audit validation
only for priors in the actual selected closure. No extra 153-source closure is
forced into these selections. If a new AE prior is active in another valid
scope, its adapter reads both fixed original runs, checks the unchanged reused
LowerTrim binding and original first final stock, then audits only the requested
active owner. The 16-prior registry does not select an accepted owner for a fresh
compile. Source installation remains with the separate updater.

## Verification scope and reproducibility

`test_new_adapter.py` ran seven tests, all passing; `TEST_RESULTS.log` contains
the real output. They cover both original owner/run/count identities, actual
RESULT/WORKER pins, fixed six-receipt/context changes, own and joint scopes,
selection and inactive-scope rejection before IO, successful-first versus
partial-later final stock, reading both runs while auditing only the requested
active owner, and cross-run reuse/source+5/full21 mutation rejection.

The control-flow fixture explicitly mocks unavailable original context/stock
command/log bytes and the generic audit operation. It checks actual pin
arguments and parsed identities, without claiming new runtime or kernel
validation. No old fixture suite or proof was rerun.

`AST_DELTA.json`, `MANIFEST_DELTA.json` and `LOCAL_VERIFICATION.json` record exact
whole-runner reverse restoration to AE, the original U control flow, source and
policy preservation, actual graph scopes and local AF packet byte matches.
`ae_prior_adapter.py.in`, `verify_delta.py`, `INPUTS_REQUIRED.json` and
`FROZEN_FILES.json` preserve the generation/verification inputs and fingerprints.
No cloud, Git or Lean command was run by this generation and verification.
Whole P1.5 remains open; the three P3-held proper-power targets and the separate
source-only/literal-medium/FixedM boundaries remain unchanged.
