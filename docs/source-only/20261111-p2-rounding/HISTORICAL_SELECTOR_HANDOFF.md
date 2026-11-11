# P2 historical third selector and strict-chord integral (2026-11-11, round 7)

SOURCE ONLY; UNCOMPILED.
Parent: 81e70e406229f3167277cd778c4b485f74ec948c.
Branch: chatgpt/p2-integral-rounding-20261111.
Source: ImbalancedChen/Certificates/P2HistoricalThirdSelector.lean (221 lines, 19 explicit entries including two anonymous Decidable instances).
No Lean/lake/Elan, numerical producer/checker, Codex service, user computer or CI run. No workflow, pin, public root or existing source is changed.

## Freshness, ownership and evidence

- The P2 head remained at the prior integer-guard request. Read its INTEGER_GUARD_HANDOFF.md, exact source and request: source 28ef507855759943387b38c75f0347b62cb6906b, blob 95e4009b1759bcb77dd71f6baf001ce7e37285e1. Request remains REQUESTED / WAITING_FOR_EXISTING_COMPILATION_REPAIR_FLOW. No exact-source run/acceptance was observed.
- Existing compilation-repair branch was read at eedb1361edec9c28f2ec56166bd719250b7e7e05 (numeric private audit-name syntax repair). The prior request is absent at that snapshot; source registration is not queue selection. This round does not dispatch or duplicate that work.
- Read current manuscript map (c8c93a71f00811284d0aef149aa5efa7c66bc413), external reuse audit (1611b2ba26eef96bf9d9a7b7e54718fd41b69c2f), historical review, unchanged lock and toolchain. Historical limited receipts do not certify this new source or its full imported objects.
- Manuscript master remains 3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e. Body d529bea2ecfcc74d64fc1664ac770a3becaa7c79 and paired JSON 49499697cca96de5f7b779e95077874ce5f9d119 are unchanged; adopted paired scope remains 17572 rows / 186 strips. No paired finite checks were repeated.
- Complete nonrecursive ImbalancedChen tree 4269bf659a68eee472c707ce03fb113d1365954e has 3138 entries, truncated=false. The Certificates root cb597cc34956de1fefbc7c41ad5beb630a974e06 was also read completely (94 entries, truncated=false); it contains no equivalent historical-selector adapter. Absence checks did not rely on the contents endpoint's first 1000 entries.
- P4 current handoff was read at eea9486f7b101d484e2938e97499c1d77cc1a67a, its early-frontier/rounding work and complete tails remain separately owned. P1 actual-parent branch remained 1006a047bd5dea9ebad05478b806e6232ec6b96b. Full87/history, fourth payload and All22/tail routes are not modified.
- New writes are confined to P2 Certificates/** and its documentation/request paths.

## A concrete selector mismatch, now isolated

The frozen manuscript producer verification/data/certify_extended_prefix.py (blob 0bfb625747ac4ab4d4ccbbce5436540ab36e276c) was read directly. Its affine_cap_lower below-mu branch:

1. Enumerates tents x,y,xy,xyz,xz,yz, choosing rise before fall in each two-plane active-min test.
2. Appends B LAST.
3. Applies the plane upper-range<=NT*denominator root filter.
4. Computes each coordinate midpoint by integer (lo+hi)//2.
5. Compares affine plane values at that midpoint by exact numerator/denominator cross multiplication, replacing best only for a strict improvement. Ties retain the earlier candidate.

The existing P160 Lean FiniteSelector instead uses B FIRST, x,y,xy,xz,yz,xyz and rangeLow+rangeHigh. That source remains a valid mathematical choice of an admissible plane, but it is NOT a verified identity with the historical Q80 selector. Prior references to that existing originalMinorant must retain this distinction. Different source order/score is a concrete ABI mismatch; no claim is made that every actual saved cell has a different winner.

The new module adapts only these differences. It reuses sourcePair, rootTest, rangeLow and firstMax. The historical score is rangeLow at identical INTEGER midpoint corners, so the existing literal plane formula and its positive denominator are retained. No real midpoint, midpoint-cap approximation, OLD-chord optimization or post-guard replacement of the winner is introduced.

The producer's above-mu early-return branch is not covered accidentally: checked_below_mu proves 128*lo.x<25*DEN from strict width and hi.x<=mu, even when the upper corner equals mu.

## Reuse and why a new adapter is needed

Independent source review established:
- The existing sourcePair has exactly the producer's active-min priority: rise at delta(hi)<=0; otherwise fall requires delta(lo)>=0. The two-plane p-q coefficients are (-50,256*b,256*c,256*d), so no branch test is re-proved.
- Existing rootTest is the exact affine maximum test: rise uses hi, fall uses lo, B uses lo.z.
- firstMax_mem_max and firstMax_priority already prove membership, maximum and first-tie behavior for any list/score. They are called unchanged.
- The membership adapter only reorders the same candidate propositions; it reuses tent_mem_sourceRaw_iff to derive branch guards.
- ordinary_B_literal_root already proves the positive-cell B root guard. It proves the new selector is nonempty after the changed order/score without another numeric proof.
- ordinary_B_stored_integer_upper_of_grid and original_selected_tent_stored_integer_upper do NOT require the old selector. They need geometry, same reader, exact branch/root, residual and OLD low>=2 guards. The historical selector now supplies the correct branch/root facts directly.
- P2OrdinaryIntegerGuard supplies all real geometry/ratio/log fields from finite integer checks; P2OriginalThirdSecondDecay supplies the complete existing P160 pre-mean fallback.
- No equivalent historical midpoint/B-last adapter with these actual integral consumers was found in the inspected current tree. Unavailable local/unpublished work remains unverified. No new outside-manuscript analytic theorem is formalized.

## New semantic chain and exact scope

- select uses the producer's historical below-mu order and floor-midpoint score through the reused firstMax. selected_first_priority preserves strict earlier-score inequality and permits ties only after the winner.
- selected_tent_tests derives actual branch/root guards from selection. checked_select_ne_none consumes the existing B root proof.
- ChordUsable is a POST-selection rational/integer test: B uses its literal Q OLD low>=2; tents use the original integer residual and literal Q OLD low>=2. The same fixed candidate is tested. No alternative plane is selected when it fails.
- selected_chord_integral_upper consumes the existing actual B/tent analytic suppliers. All coordinate, ratio, log and query facts are paid by the existing suppliers, not assumed as an integral inequality.
- selected_combined_integral_upper joins the same selected candidate's chord high with the complete raw/clipped/first/second-decay fallback. It keeps min BEFORE multiplication by that candidate's full mass and the final original UP.
- checkedChordUpper_sound derives the true actual compact-leaf integral bound from a returned Some charge. Factor four, original compact intersection, full mass and normalization are unchanged.

checkedChordUpper is explicitly a PARTIAL STRICT-CHORD CONSUMER, not the complete Python enclosure function. It returns None for invalid geometry, early-return/crossing or failed selected residual/low guards. Checked ordinary geometry proves the selector itself has a winner. The API does not pay early or crossing cells by ignoring them in a tree/total: every original occurrence still needs its own applicable rule.

The table is still a CheckedBlockTable with its actual source/object/recurrence obligations. Numeric mass, log and query arithmetic here is still the EXISTING P160/P112 source family. Correcting the geometric selector does NOT prove historical Q80 query/rounding/cost equality, a literal Python-runtime equivalence, numerical acceptance or the complete historical final charge.

## Data-access audit

The exact independent160 producer bytes remain unverified, but a concrete public source was located:
- Manuscript verification/full-numerical-source-manifest.json, blob 1dd86c8a72faea1ef390f6df873dacb53401c99a, lists numerical-third-compact-independent-20261010.py, 9385 bytes, SHA256 005fcc24c3431753e2530ab90f70e80d2256b3691cd45d14e13eb9191b0caa7c. The manifest explicitly is not a compact-package contents guarantee.
- Public release v2026.10.10 has chen-numerical-evidence-20261010.zip, asset 626620833, 323605374 bytes, digest SHA256 8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1. Its README describes the full evidence archive.
- The current GitHub interface is UTF-8 only. ZIP contents/central directory were NOT read or extracted, so the exact file is not claimed retrieved merely from release metadata.
- Current formalization proof-continuation-data has fifth-original/fourth-original, not a third payload directory in the inspected nonrecursive listing. Other third hybrid/fallback witnesses are different routes and were not substituted.
- Original adaptive tree/complete matching charge data remain unverified, not declared nonexistent. P1's existing fourth binary is not reimplemented.

## Verification and remaining obligations

Two independent reviews checked the producer mapping, branch/root priority, finite instances, list membership, casts, direct B/tent API calls, min/UP and Option None/Some proof. No definite source or mathematical error was found. Fixed Lean v4.33.0-rc1 List API contents were read:
- src/Init/Data/List/Basic.lean blob a45b3110afdf9a53be21f7051742b2f364d8dd49.
- src/Init/Data/List/Lemmas.lean blob 519a54b75079a3acb036a212f7303f8d497ecba1.

Static proof-escape/comment/delimiter/import checks passed. No actual selector result, original grid list, checker acceptance, table arithmetic, cost or integer total was evaluated.
Lean/Lake/Elan, exact elaboration, kernel replay, complete generated/private/instance declaration/type inventory, transitive axiom audit, audit replay and CI: NOT RUN. Source presence is not acceptance. No blue or green promotion.

Still required:
- Exact-source compilation and full imported-object acceptance under all existing gates.
- Actual historical coordinates and complete per-occurrence guards/charges; full cover and adopted total.
- Same reader identity and complete historical Q80/P160 operation/rounding comparison or a complete independently validated replacement under the exact adopted allowance.
- Early/crossing/rejected-mean, boundary, symmetric, above-mu and zero-width branch integration, without dropping any original leaf.
- Complete certificate-to-integral/error/normalization chain; P2.4 and all P2 remain OPEN.

## Existing compilation flow and next entry

Target: ImbalancedChen.Certificates.P2HistoricalThirdSelector.
Direct import: ImbalancedChen.Certificates.P2OrdinaryIntegerGuard.
A following P2 request records exact source SHA, blobs and key dependencies. Serialize with previous work and reuse accepted exact objects; do not start a duplicate run. Compile the full actual import closure, preserve current strict/resource/trust settings, then same-object kernel replay, complete expanded compiler types/inventory including anonymous/generated/private names, transitive axiom audit and audit replay.

Pins unchanged: leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; goldbach 09b97db5764ade1246bfb77206baa1b124760958; LeanArchitect 78dd66840d3efe8c824c699fc03381cec817c271; Batteries 41bd267b3f6b7252f6676af46d4ffc6783b64de9.
lake-manifest.json remains 86cb11a7a4b1c8ee3cd1d583985b4c7877933a4f; lean-toolchain fd85b262bf1c734663aa8292b0101f672168788f.

Next: use this historically ordered selector to connect existing early/chord/None dispatch while retaining post-selection rejection. Obtain the exact archived producer/actual tree and resolve the remaining reader/rounding/charge differences before claiming historical finite acceptance. Do not repeat the existing log, Jensen, P1-history or P4-tail proofs.
