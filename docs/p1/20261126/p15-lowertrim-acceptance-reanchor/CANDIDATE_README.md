# AE entrypoint — Synthesis@AC retained acceptance

The AE runner and manifest are generated and frozen against source publication
AD `e91af3a5c407bdeea243af7dd3c4248949d83e9b`. Seven tests specific to the new
Synthesis prior and exact function/manifest comparisons passed. This packet
prepares formal LowerTrim execution; it does not grant new Lean acceptance.

## Actual source and original accepting run

The unchanged predecessor is AC `9f2013ad9cb9caac9cec03cb213d9949c4443c65`,
whose source anchor is AB `60e6b6e18fbda5f6b0e997d15392b32100e854d9`.

Synthesis keeps AC's `runs/attempt-00000`, compiler job
`job_b4464fff4b944230927c0f40b7cd1632`, audit `2dd4c543e4398010981b`, and
**28 owned / 28 public** declarations. Its own closure is 112 sources / 111
dependencies, including two historical suppliers. The adapter retains original
successful final stock, six receipts, source plus five outputs, and all 21
artifact slots under the original accepting identity. Synthesis is excluded
from new compile selection.

AC's `runs/attempt-00001`, job `job_a108c4d7e2594e1fb5a674382db6600f`, reused
Synthesis, failed LowerTrim, and left three targets unstarted. Its 26 original
supplier bindings and absence of final stock remain fixed. The successful
actual collector was `job_a2fcafb46e5045c689422eda568d6212`.

LowerTrim's successful whole-module probe was
`job_abfb9ce81e7749c290d6f61c385aa749`, exit 0. Its repaired source is
**14655 bytes**, SHA256
`f26884610a2d205368b347ed5fd80947c91c5973a6750bc0b333cb57dcb42106`.
The single contiguous proof splice preserves eight declaration headers and two
imports. The final repair review is **1596 bytes**, SHA256
`45592035ce29e584e6b4783163e93edbb70d6495a1e0b94e46a06c8c7fb33d73`.
A successful no-output probe is kept distinct from owner acceptance.

## Frozen production candidates

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `run_selected.py` | 306454 | `2fac63da6dd93b54ded3a8c5c8542558f3a03a738092fcb43b2336ab8674705e` |
| `SOURCE_MANIFEST.json` | 364863 | `6c5c0b8795a2c6fa1265e5030b12a9e77500efe651b8796b11b748a0ed47ada5` |
| `synthesis_ac_prior_adapter.py` | 26934 | `4d51009db4c7f73ca08b8d5bfe481e0525fa2b2a0bdff89fbb3d232a0e61a835` |

`build_candidate.py` fixes the actual AD source/review and AC collector evidence.
It derives the three new functions from the existing Mean@AA adapter and checks
the result against `synthesis_ac_prior_adapter.py.in`. `INPUTS_REQUIRED.json`
records the completed actual bindings. `FROZEN_FILES.json` inventories the files.

Of AC's 61 functions, **59 remain byte-for-byte unchanged**. Only
`source_manifest` and `preflight` add the new classification/dispatch; three
Synthesis-specific functions are added. Reversing those exact edits and the
specified new adapter/anchor/manifest/header text restores the whole AC runner
byte-for-byte. The 13 older prior identities, 359 other source rows, all imports,
303 fixed dependency policies, and 19 P3 HOLD entries remain unchanged.

## Selection scopes

| Selection | Sources | Dependencies | Artifact watch modules | Historical suppliers |
| --- | ---: | ---: | ---: | ---: |
| LowerTrim first | 119 | 118 | 136 | 3: Endpoint@Y, Mean@AA, Synthesis@AC |
| Remaining four | 157 | 153 | 160 | 27 |

The four targets are OriginalSingletonLowerTrimPaid, OriginalSingletonAtlasTrim,
OriginalPrimeAtlasReserveBranches, and OriginalSingletonAtlasRoughPrime. Exact
names and order are recorded in `selection_guidance.subsequent_4_targets`.
Older selection guidance is retained as history; source installation remains
with the separate updater.

## Validation scope

`test_new_adapter.py` executed seven tests, all passing, with the real log in
`TEST_RESULTS.log`. Coverage is limited to the new prior: real first-run identity
and RESULT/reconstructed WORKER pins; source/closure/selection restrictions;
count, scope, path, and six-receipt mutations; original first final stock;
retained-adapter control flow; and rejection of changed later failure/reuse/pins,
source plus five outputs, or full21 artifacts.

The control-flow test explicitly mocks unavailable original context/log/command
bytes and generic audit IO. It checks original pin arguments and parsed
identities without claiming a new runtime or kernel validation.

`AST_DELTA.json`, `MANIFEST_DELTA.json`, and `LOCAL_VERIFICATION.json` preserve
the exact comparisons, relevant local AD publication-packet byte matches, and
test evidence. No old fixture suite or proof was rerun. No cloud, Git, or Lean
command was executed during generation or verification. Whole P1.5 remains open.
