# P4A.4 registered early G1 same-schedule source selection — phase 24

Baseline `b912f502e5be53ba0c88d4a354da2fc4d0072d45` on `chatgpt/p4a4-fine-audit-20261119-1645`. The commit containing this handoff has that baseline as parent; its tree identifies the handoff and new source blobs. SOURCE_ONLY: YES. COMPILED: NO / UNCOMPILED. KERNEL_REPLAYED: NO. TRANSITIVE_AXIOMS: NOT CHECKED. INDEPENDENT_REVIEW_THIS_RUN: NO. Finite proof bodies: UNEVALUATED. This phase authors no new Lean theorem and changes no proof body, statement or assumption.

## Exact resolution of the previous source-selection uncertainty

Phase 23 identified the Fine early-G1 import chain terminating at `P1OriginalFourthUniformCutoffLicence → P1OriginalFourthSameScheduleLicence → P1OriginalFourthActualQuantizedLicence`, with the latter two present only as isolated candidates. The source directory at `71b47b30928600386237323d4f6a1f0c332edfbe:docs/source-only/20261110-yellow-closure-10t/t02_full87_volume_integral/successor_fourth/` contains three **specifically named** author registries not identified in the earlier bounded search:

- `UNIFORM_CUTOFF_REGISTRY.json`, Git blob `f98bdd6d3978dd6dc285613cbc601fc304385463`, records the already selected uniform-cutoff source and explicitly names `same_schedule_source` SHA-256 `588cca0cc5b387699e9c314a9cd6e602a80ad816077b804b8e1ceaecf3ab3766` and its `SAME_SCHEDULE_REGISTRY.json` SHA-256.
- `SAME_SCHEDULE_REGISTRY.json`, Git blob `497c5e5e511ef549b11652e2a35360ce6a7d8aec`, identifies that exact source, its install module and import of the quantized source, and names the exact `QUANTIZED_SUPPLEMENT_REGISTRY.json` SHA-256.
- `QUANTIZED_SUPPLEMENT_REGISTRY.json`, Git blob `f28e877172c441404a402e0bc223e6dc5813df37`, identifies exact quantized source SHA-256 `bb3241c135ee5650f34e19852acc10b20ed1c0368a371199db3a9447e7c0168f` and four exact support dependencies.

These explicit author records resolve the *particular source-identity/selection question* left open in phase 23. They are themselves marked `SOURCE_ONLY_UNCOMPILED_UNEVALUATED_AWAITING_T09_AND_REMOTE`; they do not certify elaboration, full compatibility, final independent review or a complete All22 proof. The same-schedule candidate retains the registry's coordinated one-line repair `hu.trans_eq hwin`; it does not reintroduce the earlier `width n≤2e` premise. The genuine `2e+2*width n<commonMargin`, original attained winner, own selected mask, strict old-cap condition and original q-before-target schedule remain literally in the source. The quantized helper keeps its own narrower `width n≤2e` theorem; it is not substituted for the stronger same-schedule terminal.

Six exact pre-existing source blobs are staged at their previously absent task-packet `ImbalancedChen/` module paths: the two registered G1 modules and four explicitly recorded support sources. `P4AOriginalFull87DataPolicy` and `P4AOriginalNewFifthUnion` match their selected full87-manifest entries and the 62af/Fine/baseline origin blobs. `P1GuardFrozenFiniteCapAlgebra` and `P1QuantizedActionLicense` are read from their registry's exact historical commit `be2efd01c561080672e6c0ad0ba21638837afe4c`; those historical paths are not present at the Fine head, so that distinct provenance is preserved. The full source bytes, hashes, import lists and receipt links are in `SOURCE_SELECTION_PHASE24.json`. This is source-only packet placement, not proof that the full transitive imports, historical data, 11 other provisional variants, or generated object files are installed. The two phase-16 copies remain available unchanged as provenance; no candidate is claimed kernel accepted.

- `ImbalancedChen.P1OriginalFourthSameScheduleLicence`: SHA-256 `588cca0cc5b387699e9c314a9cd6e602a80ad816077b804b8e1ceaecf3ab3766`, Git blob `61698ecbd29aac1f755616fd3b2c7524d8bd8323`
- `ImbalancedChen.P1OriginalFourthActualQuantizedLicence`: SHA-256 `bb3241c135ee5650f34e19852acc10b20ed1c0368a371199db3a9447e7c0168f`, Git blob `14688bbdfd2730507e69d46c25ee29dd9663a42e`
- `ImbalancedChen.P4AOriginalFull87DataPolicy`: SHA-256 `c3ca1ff72dfa0c38bd0ee0d8b132fd641cab33479f21225ef41b8eff9b19d006`, Git blob `501743ebb0b2cbac47cb9a79e5c86f0cb687cb48`
- `ImbalancedChen.P4AOriginalNewFifthUnion`: SHA-256 `38f3b4355416baf67f60ddd42ddb07d4770c192c550b529b6cf7a0d253ef0417`, Git blob `2158b9f294b8b8324acfd328998939fb55ab623d`
- `ImbalancedChen.P1GuardFrozenFiniteCapAlgebra`: SHA-256 `8f13f4a65365a852442ee5d5d53ee772cd537d04a0b670291b898e5f004dad27`, Git blob `e052b72ad4da8933bf50beb5db96602401be22cc`
- `ImbalancedChen.P1QuantizedActionLicense`: SHA-256 `edbecced0c22573ff56f3c7f853c17d6bb8e16602554d738001c7467138a9149`, Git blob `8dbda2675372cb3d846478777090359104d181ab`

## Scope of existing Fine, manuscript and reserve

The original Fine/cofinal report, final registry and selection at `71b47b...` were checked; phase 23 traces the actual P4A.5 consumer to that Fine theorem and its exact constant-in-delta Q/rho with one q/beta/k. This source-selection repair does not reselect q, beta or k, does not add a new coefficient, and does not re-prove hdensity or P4B.4 PP. The phase-21 original four-positive/22-saving endpoint map and one G7 replacement remain unchanged. The existing compiler reserve, separate density reserve, actual presieve correction and finite signed errors are not paid or removed here.

Manuscript entry `9731290e8f53cffda44129906cde6a965eaa869b:paper/source/manuscript-body.tex` returns blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching the inherited pin. Its current-upper passage retains actual ancestors and successive new-minus-current-parent differences; there is no promotion of unrelated gain estimates. The configured Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958` pins were reread from configuration. Fixed c/K remain `49044063/25000000` and `8452171/1250000`. No new external mathematical theorem is introduced; existing PNT/Mertens/BV/spectral provenance, version, conditions, normalization, call site and verification status remain in inherited registries.

## Validation and remaining work

`python3 /tmp/p4a4-phase24/verify_phase24.py` exited 0: checks the three registry Git blobs, their cross-linked SHA-256 values, exact length/SHA-256/Git blob of six staged sources plus the existing uniform-cutoff source, the registered dependency links and literal winner/precondition markers. This is source identity and lexical checking, not Lean parsing or proof acceptance. `lean --version` and `lake env lean` on each of the two selected G1 candidates exited 127 because Lean/Lake were unavailable; see `LEAN_CHECK_PHASE24.log`. Runtime versions cannot be independently verified. Stack 8192 KiB; Python 3.12.14. No resource increase, CI action or user machine was used. Applicable root/docs/source-only/packet AGENTS lookups returned NOT_FOUND.

Changed-file SHA-256 (this handoff is identified by its containing Git tree):
- `SOURCE_SELECTION_PHASE24.json`: `6bc5c81ee397dda424e266e9a483e11ac4830c3fd2e2f461b1c70effea648617`
- `verify_phase24.py`: `39c5dd054fb0338852dfb3518e896fc1be5c64ff0dc18f7ac1bf9242ad1efbe0`
- `SOURCE_CHECK_PHASE24.log`: `dfd7f7d244117b04ac40404b711ae7eea87139ed663879faebb484b766b26f0e`
- `LEAN_CHECK_PHASE24.log`: `033458b025b81a5091964eeef744530a339d587b8d6de9793c005635895fee19`
- `ImbalancedChen.P1OriginalFourthSameScheduleLicence`: SHA-256 `588cca0cc5b387699e9c314a9cd6e602a80ad816077b804b8e1ceaecf3ab3766`, Git blob `61698ecbd29aac1f755616fd3b2c7524d8bd8323`
- `ImbalancedChen.P1OriginalFourthActualQuantizedLicence`: SHA-256 `bb3241c135ee5650f34e19852acc10b20ed1c0368a371199db3a9447e7c0168f`, Git blob `14688bbdfd2730507e69d46c25ee29dd9663a42e`
- `ImbalancedChen.P4AOriginalFull87DataPolicy`: SHA-256 `c3ca1ff72dfa0c38bd0ee0d8b132fd641cab33479f21225ef41b8eff9b19d006`, Git blob `501743ebb0b2cbac47cb9a79e5c86f0cb687cb48`
- `ImbalancedChen.P4AOriginalNewFifthUnion`: SHA-256 `38f3b4355416baf67f60ddd42ddb07d4770c192c550b529b6cf7a0d253ef0417`, Git blob `2158b9f294b8b8324acfd328998939fb55ab623d`
- `ImbalancedChen.P1GuardFrozenFiniteCapAlgebra`: SHA-256 `8f13f4a65365a852442ee5d5d53ee772cd537d04a0b670291b898e5f004dad27`, Git blob `e052b72ad4da8933bf50beb5db96602401be22cc`
- `ImbalancedChen.P1QuantizedActionLicense`: SHA-256 `edbecced0c22573ff56f3c7f853c17d6bb8e16602554d738001c7467138a9149`, Git blob `8dbda2675372cb3d846478777090359104d181ab`

Next inspect and supply the remaining exact transitive imports/data and reconcile the other provisional variants without changing pins. Under the existing pinned Lean environment, elaborate the two G1 modules and the complete selected early/Fine downstream; inspect generated types and transitive axioms, evaluate finite guards and kernel-replay. Do not treat these matching source hashes or the historical T09 coordinated fix as a green build or independent full review; do not infer a new mathematical estimate solely from unavailable toolchain or uninstalled dependencies.
