# P2 checked zero-geometry entries in the original tree ledger (2026-11-11, round 10)

SOURCE ONLY; UNCOMPILED.
Parent: 72b658c315f95aff51433e79cedef7b1d3071900.
Branch: chatgpt/p2-integral-rounding-20261111.
New: ImbalancedChen/Certificates/P2ThirdZeroGeometry.lean (80 lines).
Updated: ImbalancedChen/Certificates/P2HybridThirdChargeLedger.lean (183 -> 196 lines).
No Lean/lake/Elan, numeric producer/checker, Codex service, user computer or CI run.
No workflow, dependency pin, public root or other route's source was modified.

## Latest source, manuscript and ownership

- Latest P2 head remained the R9 request. Read HYBRID_LEDGER_HANDOFF.md, source bf7d292e263aba5052b9daa627f8e3c66d0c5658 and old hybrid blob 53d2293e0a560006166fd04d6fc2ac002a73d03c. The request remains REQUESTED / WAITING_FOR_EXISTING_COMPILATION_REPAIR_FLOW; no exact-source run/acceptance was observed.
- The existing compilation branch remains 5db345d60c12ce03457a0a6174e0be7c8a65f1d6, a bounded StoredBlock000-004 configuration explicitly not full T01 acceptance. The R9 request is absent from that snapshot. This round does not dispatch or duplicate that work.
- Rechecked map c8c93a71f00811284d0aef149aa5efa7c66bc413, external reuse audit 1611b2ba26eef96bf9d9a7b7e54718fd41b69c2f, historical review e7600f8a4819fdd5eb2ddaefec09f415dae269f9 and unchanged pin files.
- Manuscript master remains 3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e; body d529bea2ecfcc74d64fc1664ac770a3becaa7c79 and paired JSON 49499697cca96de5f7b779e95077874ce5f9d119 are unchanged. Adopted scope remains 17572 paired rows / 186 strips. No completed finite checks were repeated.
- Complete nonrecursive ImbalancedChen tree c92f343f10a32dcf1001e91282f6b68bf6ace8d5 has 3138 entries; Certificates has 97; both truncated=false. No first-1000 contents truncation was mistaken for absence.
- P4 handoff remains eea9486f7b101d484e2938e97499c1d77cc1a67a; P1 actual-parent branch remains 1006a047bd5dea9ebad05478b806e6232ec6b96b. Full87/history, original fourth data, All22 and full tails remain separately owned. New writes are confined to P2 Certificates/** and its report/static/request files.

## Existing zero results are reused

P4AOriginalZeroLeafSuppliers.lean, blob 13800bb76d1686b0ff0931bbf41bfa21829bd0d9, already proves the actual compactKernel integral zero for below-cutoff, above-rho, x/y or y/z reversed order, collapsed/reversed coordinates and root-cube gate boxes. Its coordinate-face and actual kernel-zero proofs are used unchanged. No measurability, integrability, null-face or zero-integral premise is supplied by the new certificate.

The specific outside seed 15-20 finite proofs and forest already exist and were NOT repeated. No generic finite integer checker or hybrid zero case was found in the inspected current root/Certificates interfaces. Inaccessible local/unpublished material remains unverified.

The existing positive original DEN and decodeCoordinates are reused from P4AClosedTreeCoordinatePropagation (blob 6001168a68966f5c847d915e168ae6bd3b48e675). Only integer-to-real division order and exact fixed endpoint dictionaries are adapted. The Fin3 existential uses fixed Mathlib/Data/Fintype/Defs.lean, blob c9fab2c73ea097b3d5765e9b81817977bdd75f82, Fintype.decidableExistsFintype.

## New integer check and actual zero connection

Geometry(lo,hi) is the disjunction of these six finite integer tests:
- hi.z <= 480*2^24.
- 9500*2^24 <= lo.x.
- hi.x <= lo.y.
- hi.y <= lo.z.
- Some Fin3 coordinate has hi.j <= lo.j.
- 481573208064 <= lo.x+lo.y+3*lo.z.

The Decidable instance and Bool check precede the noncomputable section and contain no real predicate, reader, log or cost evaluation. The exact scaling is H/DEN=1/100, R/DEN=19/96 and T/DEN=299/500, with DEN=805306368000. The checker is intended as a constructive finite program; its compiler/execution acceptance is still NOT RUN.

check_integral_eq_zero translates each accepted condition to its existing actual compact integral supplier. It needs neither positive width nor coordinate positivity from the caller, so it also handles reversed and zero-width cells. All endpoints remain non-strict:
- Equality at cutoff/rho/order/collapsed coordinates is paid by the existing null-face theorem.
- Equality at the root cube is paid by the existing actual kernel identity.
Neither is described as an empty set merely because its integral is zero.

The root-cube condition is Theta <= x+y+3z. It is NOT selected OLD/minorant <=2. The latter is the prior early NEW-only mean bound and can have positive correction. This source does not confuse the two.

These are genuine Lebesgue compact-kernel zero integrals. They do not assert that arithmetic prime boundary atoms vanish; those remain in P1's separate transfer/reserve work.

## Minimal mixed-ledger extension

The previous hybrid source gains one no-data Source.zero constructor:
- Its Valid clause checks ZeroGeometry.check on the CURRENT original tree bounds and requires the stored integer charge to be EXACTLY zero.
- Its real upper is zero.
- Its local integral supplier calls check_integral_eq_zero; zero then equals the original Q80 zero charge.

The existing BoxGuard and ordinary branches are unchanged. The original Forall2 positional relation, length theorem, exact closed-leaf map, scalar aggregation, adopted sum and tail transport proofs are unchanged. Empty, duplicate, zero-width and closed-face occurrences remain in the list; a zero entry pays its occurrence instead of deleting it.

This is an additive source change to an UNCOMPILED prior module. Source.zero changes the inductive and generated declaration closure. The updated hybrid must be rebuilt/replayed/audited at its NEW exact blob; an old R9 module object is not interchangeable. Upstream exact accepted objects may still be reused under the existing gates.

## Executability audit and remaining boundary

A separate read-only audit found an important cost-evaluation boundary. The existing pure-integer mass/log ABI can remove mass's Real log/floor, but it does not by itself make the full reader/cost executable:
- OriginalNodeArraysV1/DataCore.lean, blob 3c8cb466e40a188e4f48f960fc31885689998828, explicitly declares NodeTree.read and assembledRawRead noncomputable.
- CheckerCore.lean, blob b64c67e2c3130672412f18027ddefedd63d22b68, explicitly declares assembledRead noncomputable.
- Fixed Lean v4.33.0-rc1 src/Lean/Elab/PreDefinition/Basic.lean, blob c31e13045fd34779db5fbbe3efc03909af17432a, excludes an explicit noncomputable declaration from compiler code generation.

Their integer recursive bodies may still reduce in the kernel; compiler code and kernel reduction are different issues. No alias, implemented_by escape, source-flag removal or executable whole-cost claim was added. The mass ABI and full cost bridge were only inspected, not reimplemented in this round.

The zero checker is independent of those readers. The mixed ledger as a whole remains a noncomputable semantic Prop because its ordinary branch remains value-semantic. No actual original zero check, entry list, cost comparison or adopted sum was evaluated.

Still unpaid:
- Exact-source compilation, actual import-object/kernel/type/axiom acceptance, and zero checker code-generation validation.
- Actual original tree/coordinate/charge identities and complete per-occurrence validity.
- Ordinary executable cost ABI or another valid concrete comparison method, actual integer domination and the original sum.
- Full-cap cancellation and other boundary/symmetric/above-mu cases not covered by the six zero tests or current ordinary rule.
- Remaining adopted certificate-to-integral/error/normalization chains. P2.4 and whole P2 remain OPEN.
- The public archive/exact independent producer/tree bytes remain unverified; no user-host or Codex service was used to obtain them.

## Verification and exact compile delivery

Two independent reviews found no definite source, mathematical direction, scale or endpoint error in the 80-line checker and 196-line updated ledger. They verified the six branches, Fin3 decision, root-vs-minorant distinction, current-position/zero-charge binding and unchanged positional aggregation. New imports form no additional cycle.

Static proof-escape/comment/delimiter/import and explicit-name preservation checks passed. The prior hybrid explicit names remain, but generated declarations and definitions have changed and need fresh full audit.
Lean/Lake/Elan, numerical check execution, kernel replay, complete compiler declaration/types including all Source.zero and structure/generated/private entries, transitive axiom audit, audit replay and CI: NOT RUN. No blue/green promotion.

Targets:
1. ImbalancedChen.Certificates.P2ThirdZeroGeometry.
2. ImbalancedChen.Certificates.P2HybridThirdChargeLedger (UPDATED SOURCE).

Direct helper imports: ImbalancedChen.P4AOriginalZeroLeafSuppliers; ImbalancedChen.P4AClosedTreeCoordinatePropagation.
The hybrid retains its prior imports and adds the helper. A following request binds BOTH source blobs and the replaced hybrid blob. Compile/audit the helper and then the updated full import closure through the EXISTING serial compilation-repair flow; do not duplicate any old run already working. Preserve exact object hashes, current strict/resource/trust flags, same-object kernel replay, complete types/inventory, transitive axiom audit and audit replay.

Pins unchanged: leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; goldbach 09b97db5764ade1246bfb77206baa1b124760958; LeanArchitect 78dd66840d3efe8c824c699fc03381cec817c271; Batteries 41bd267b3f6b7252f6676af46d4ffc6783b64de9.
lake-manifest.json remains 86cb11a7a4b1c8ee3cd1d583985b4c7877933a4f; lean-toolchain fd85b262bf1c734663aa8292b0101f672168788f.

Next: bind actual original zero-fee leaf occurrences to this finite check; address the explicit reader/code-generation and remaining cost ABI before calling the mixed ordinary ledger executable. Reuse the existing mass/log and zero analytic suppliers; do not redo seed finite checks, tree aggregation, P1 history or P4 tails.
