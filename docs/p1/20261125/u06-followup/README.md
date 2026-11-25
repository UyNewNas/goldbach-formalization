# U06 exact source recovery followup

Five existing Lean sources have been recovered without changing a byte. On the previous U06 review's selected-source graph plus this scratch overlay, the unavailable-source frontier decreases from **17 to 16**. Canonical sources and the private compiler are unchanged; this is not build or theorem acceptance.

## Exact recovered chain

`CentreSqrtEnvelope` previously stopped at `CentreCoprimeDivisors`. The original source chain now resolves through:

1. `CentreCoprimeDivisors`
2. `CentrePrimeFibres`
3. `SignedSharpReceiver`
4. `OwnedPrimitiveLedger`
5. `EighthPrimeMeanLedger`

The last module imports the existing canonical `P4AOriginalFull87OwnedEighthSource`. The Coprime module also imports the existing `ActualSmallRoughAttachment`. These are the only project-source boundaries outside the five recovered files, and both current canonical files match source220 and the original U06 review's recorded head exactly. `Mathlib.Tactic` is the only other direct import in this recovered chain.

| Module | Original commit | Bytes | SHA256 |
|---|---|---:|---|
| `P4AOriginalFull87CentreCoprimeDivisors` | `d4a832ca76e3` | 8660 | `74b326d4d0e9f75baf8757e4ded51bd335dd65f540069b0a96ce2cc7b8381c5e` |
| `P4AOriginalFull87CentrePrimeFibres` | `4f4fb3f33aa3` | 9729 | `d418fa7947e6a0ac327e7fa16c775572c01c27cc210ce7af899951b5e72db5fc` |
| `P4AOriginalFull87SignedSharpReceiver` | `e2d88d41c827` | 10512 | `634fedb70cc81a5823b9f2bbdaea69c9e601b176a938ab93e2be66e25e9b6311` |
| `P4AOriginalFull87OwnedPrimitiveLedger` | `ee35ebc8fb52` | 9663 | `a6a4a3220952241aac5dcb9dce0b7a58d33733e796eec3ba11cb5c701adce75a` |
| `P4AOriginalFull87EighthPrimeMeanLedger` | `a023ae055d3d` | 10189 | `28e6e07dd3cb608f136997282e4786ebacd9d742b3938b28d83f09bb747c4a76` |

The first four files are pinned in `docs/source-only/20261112-resume/p-updates/INDEX.json`, at `/sources/41`, `/sources/48`, `/sources/53` and `/sources/58`. Their exact commit/path reads returned the indexed Git blobs; decoded source SHA256 and actual imports also match the index. No proof was recreated.

The fifth file was already available as Git blob `7ebef5ea7baf3a79180f4d086a6f05530c0eb827` in `/workspace/scratch/cb6959cc4223/p4a5`, so it was recovered with `git cat-file blob` without another network download. Its 10,189 bytes, SHA256 and blob match both `physical-reserve-next/REGISTRY.json` `/key_inherited_sources/3` and `ADDITIONAL_API_IDENTITIES.json` `/sources/12`. Both records bind it to commit `a023ae055d3d90738f6965a2848266aa13089faf`; the original commit tree itself is unavailable in that local cache, so this followup does not claim an independent local tree check.

All five exact payloads are cached under `/workspace/scratch/cba105ac8c38/u06-source-recovery/sources/ImbalancedChen/`. The four GitHub responses are separately retained under the same scratch root. These payloads have not been added to this Git report or installed in canonical paths; `SOURCE_RECOVERY.json` records their complete locators, byte counts, hashes and import edges.

## What changed in the frontier

Only `ImbalancedChen.P4AOriginalFull87CentreCoprimeDivisors` is removed from the prior unavailable-source set. Its four newly exposed project dependencies have also been recovered, and the resulting chain reaches the two existing canonical boundaries without introducing a new missing module. The exact remaining 16 names are retained in `SOURCE_RECOVERY.json` rather than repeating the prior large graph.

This count refers to recoverable source bytes in the reviewed graph. The old published `u06-reuse` review, current canonical installation and private-compiler observations are untouched. The remaining names are unresolved within the examined source selections; this report makes no global absence claim.

## Mathematical and verification boundary

The recovered Coprime receiver still requires a nonprime target and separate sixth/eighth sharp-prime-progression bounds. The CentrePrimeFibres and SignedSharpReceiver statements also retain those sharp-PP premises. OwnedPrimitiveLedger gives a finite owned primitive budget; EighthPrimeMeanLedger retains primitive, modulus-prime and centre-prime budget terms. Recovering these statements does not discharge their analytic premises or pay any reserve.

The index labels this material `SOURCE_ONLY_UNCOMPILED`. No Lean/Lake, compiler service, kernel audit, CI, source edit, canonical installation, resource change, staging or commit was performed here. Root can reuse the exact cached sources in a later adoption manifest while preserving the 16 outstanding source holds and the normal/kernel/full-owned verification gates.

## Subsequent cloud exact-name probe

The original probe `job_4621c500f2e148dd8b8f8fddffd43588` failed before scanning because the `rg` executable was absent. The read-only `os.walk` fallback `job_63833cad667b4e8f82a1aaa533fbc118` then succeeded (exit 0, 2.386805534362793 seconds): all 16 exact `.lean` basenames were searched under `/workspace`, with zero directory-scan errors and zero matches. It excluded `.git` directories and did not follow directory symlinks. `CLOUD_SOURCE_PROBE.json` binds the exact requested names, task statuses, complete untruncated output bytes and source-record hashes. This observation leaves the 16-name source frontier unresolved within that scope; it says nothing about renamed files, archive members, Git blobs or external storage. No Lean/Lake, source edit or new verification was performed. The frozen `REMAINING_FRONTIER.json` and `SOURCE_RECOVERY.json` are unchanged.
