# SDD ledger — plan: docs/superpowers/plans/2026-11-26-p36-normalized-density.md

Base: e99a028e3afe492c95e48d2b55023a0064d74d21.
Task 1: in progress; exact source/evidence review delegated to p36_evidence_audit; remote branch absent.
Task 2: in progress; source implementation delegated separately, root owns cloud scheduling.
Task 3: pending fresh strict compile, replay and full inventory.

| Interfaces | Producer | Consumer | Preflight result |
| --- | --- | --- | --- |
| Existing checkpoint / new source | Task 1 fixes e99a028e | Task 2 adds one owner | Publish immutable SHA; no shared-file mutation |
| Epsilon / rough reserve | Beta supplier fixes epsilon | Rounding supplier takes etaBox | Set etaBox after epsilon, never alter an old existential witness |
| Exact density ledger | A-C=loss, betaGap=V*C-D | Normalized row bound | Keep signed gap and same original coefficient |
| Owner / verification | Task 2 one new Lean file | Task 3 existing harness | Root only schedules cloud; no concurrent edits of source |
| Task 1 internal | existing evidence | remote SHA | Recheck hashes without rerunning accepted owners |
| Task 2 internal | exact requested theorem | proof body | Lean statement is test contract; no axioms or placeholders |
| Task 3 internal | frozen source | exact proof evidence | Do not claim acceptance from compile-only stage |

Ruling: Continue the existing dedicated local branch; author only locally, with cloud reserved for received-source execution.
Ruling: User explicitly authorizes publishing these commits to UyNewNas/goldbach-formalization; no new approval is needed.
Ruling: Universal Lean theorem statements plus strict/kernel/axiom validation are the applicable proof gates; mirrored unit tests would not add mathematical evidence.

Task 1: classical source d1db3a pushed successfully by P1 job_7c51099e56ac4b8e99a154d4d1fad1c8. Full e99a028 delivery pending P1 job_346b3385c7774145bd42d54acff4f460.
Task 2: candidate source SHA256 85fbf4beafe45c12a8dbcf90e06c090abc4a001e44e1fc0cc708eb30ce6e77a5; compile snapshot 5fcae986fde9f27b008f0d952dcd97f88d5060a2.
Task 3: P1 job_c5dce1d52a124e689eddbe4a190c94dd running new normalized owner, memory budget 16000 MiB.
Task 4: independent implementation assigned to p36_evidence_audit; own file RoundedPairDensity only.

Task 1: complete — exact e99a028e3afe492c95e48d2b55023a0064d74d21 published by job_346b3385c7774145bd42d54acff4f460, no force, independent API and git readback matched.
Task 2: fix round 1/5 — two expression failures; redundant dsimp removed and exact half-budget ring identity made explicit. New owner SHA f351018fd6ae22d26afd89a206f75aad454d41a29e5178c9bbc9ff7a8d9c17ea; compile snapshot 0a9e557dd2d1827a2902f1293e80f9497c5b2f8b. Awaiting covering strict/kernel/inventory run job_db5c3193fc1740e9a066ce5c34458134.
Task 4: source and independent review pass, formal run job_3dd12781d3a7440a806ec9523fcd4eac pending.

Task 5: candidate complete (two theorems), source SHA 0d4edbffaefc714db6aa50b12ecc2135b263e92e8c5f439abcf696d6e39b8d97; compile snapshot 67c4768f21fd7066e88a77205a83e9c1869e9870; gate job_de0f22152f0841aea8a82bf197432560.
Pre-flight Task 5: row reserve supplies arbitrary positive κ/H0 and common ε/τ/N0; existing pair harmonic limit supplies eventual H0>0; pair-density identity handles signed rows with original fullModulus. No circular positive-mass input.

Task 4: full original gate PASSED — job_3dd12781d3a7440a806ec9523fcd4eac, report20261126T023255.410537Z, strict9.922s/replay8.246s/inventory585.457s, project closure156. Export review pending correction.
Task 2: fix round2/5 removes a redundant ring rejected by strict unused-tactic lint; type/options unchanged; SHA2029ef38300b157d72cb45cabe8cd1024f2b855f8dbfae5b99daf7fd2067fc3d, snapshot658b9ff7480b4380ac00f948be7d1dcee326599f.
Task 5: first scheduled job cancelled during preflight after its row dependency failed strict lint; zero owned credit and no target compile/replay performed. Retry runs only after the revised row owner fully verifies.

Task 3 evidence tooling: independent review rejected first exporter (6 important,2 minor). Fix round1 resolved6 items; scoped rereview identified two residual byte/provenance classifications. Fix round2 is limited to lake-manifest export-time classification and tracked SOURCE_SELECTION own-byte Git binding, with targeted regressions. No real evidence accepted via a rejected exporter.

Task 2: revised source2029ef38 fully VERIFIED_OWNED in job_521a510d13c54da8a13b740e194baaf6, report20261126T025135.937253Z (SHA13a1c8ffd9d16a731da275b999c837aa453909c2f16d4a70644674265678504f); strict10.89s, replay9.063s, inventory596.481s, closure284. Runtime six-tool before/after binding preserved independently. Await export/local acceptance.
Task 3: exporter residuals corrected in SHA d2a13e3fa2d4e290b49682d222f6d288ac416bc99e25ccdd2f8dd7d37b55d692; root checked82-line diff and independently reran the two targeted regressions (2/2,5.520s). Actual export queued; original runner and auditor unchanged.
Task 5: original singleton gate begun at report20261126T030430.336140Z after row full success.

Task 3 real export: rejected original reports solely because historical cache writer hashes differ. Independent diagnostic pinned16 prior reports and their three writer versions; original current-run driver and full gate unchanged. Known historical runner input-key, compile command, object hash and reuse predicate implementations are identical at the recorded Git commits. Limited compatibility fix preserves exact source/compiler/import/key/object/command/log checks and archives the original reports.
Ruling: Permit only the16 independently pinned historical reports from older compatible runner versions to establish existing dependency compilation lineage, while keeping the current new-owner driver, strict/replay/inventory gate and every exact dependency guard unchanged. If this compatibility judgment were wrong it would weaken provenance for reused dependencies; fixed whole-report hashes, preserved source history and independent review are required.

Task 5: final fixed source737f3c89 fully VERIFIED_OWNED in job_51eebdb3c9014e3caf3784cb107e2c87, report20261126T030845.042019Z (SHA5e27a6d36a698b50ad4d0e9cdf221d52935d047fd1f34949b66cb40d6e676d20). Strict10.871s/replay9.797s/inventory626.702s, project closure286. Separate runtime before/after tool binding captured.
Task 3: final exporter SHA003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5 passed independent limited compatibility review and all19 regression tests. Original29 existing tests were already passed and their implementation is unchanged.
Task 3: all3 real archives exported, recovered with original size/SHA pins, and locally verified exit0/PASS_LOCAL_EVIDENCE_VERIFICATION. No local Lean reruns. All3 explicit source hashes agree with frozen snapshots.
Task 3: independent inventory+original-terminal check PASSED; old4 plus new3 groups contain27 distinct defining modules and414 unique declarations,317 theorem records+97 definitions. New26=7 explicit mathematical theorems+19 generated helpers/equations. Each new singleton original command-end sequence agrees with its archived report; all9 owned compile/replay/audit logs and exit0 records match.
Integration: old accepted sources and original verification files unchanged relative to e99a028. OWNED_SCOPE_STATUS and NEXT_DENSITY_BOUNDARY updated to current accepted increment; whole_p36_closed=false and currentVerified=false.
Deferred minor findings: none. Parked load-bearing findings: none. All earlier source/tool review findings are covered by their retained fixes and reviews.
Final whole-branch review and authorized continuation push: pending.

Final whole-branch review: GPT-6.2 Astra reviewed e99a028..0cfdb6b read-only; no critical or important issues, Ready for authorized push: Yes. One minor finding asks for a durable restore ref instead of FETCH_HEAD; bounded docs-only fix applied by p36_evidence_audit. No declined-to-judge items. Scoped re-review pending.

Final scoped re-review: GPT-6.2 Sol reviewed0cfdb6b..56e3577; one minor finding ADDRESSED, no new breakage or out-of-scope observations. All final review findings resolved. Proof sources, exporter and evidence payloads unchanged after their covering gates.
Finish: user already chose authorized push to existing work branch; retain dedicated worktree, do not merge or add P3.6 to closed-node PR. Exact evidence and source gates already cover the final bytes; only review/publication documentation changed afterwards.

Publication completed: original reviewed increment46858c5a9bb80a28041567d6b42a0fdfd038377b fast-forward pushed from e99a028e3afe492c95e48d2b55023a0064d74d21 by P1 job_4cfc2e48d4454aa785c155115a2dfd9d, exit0. Root independently confirmed the exact remote SHA via GitHub API and local git ls-remote.
Transport recovery: the shared bare lacked521 historical baseline blobs; target and baseline missing sets were equal and no new delta object was missing. Two pre-push stops are retained. A fresh empty object repository fetched the exact521 IDs, then the original full-repository fsck, base/artifact/target/delta checks and all79 changed-file SHA checks passed before the successful non-force update. No proof gate was changed.
Final delivery: append this successful publication receipt as a documentation-only commit and fast-forward the same work branch; all mathematical sources and verified evidence remain unchanged. P3.6 stays open and excluded from the overall closed-node PR.
