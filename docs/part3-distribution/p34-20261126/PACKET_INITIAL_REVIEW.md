# Independent Task 1 review

Reviewed candidate `40a5b28303c652450da65e740fd5a4e70c902391` against `f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e`. Its verified local Git tree is `71a58b967f16454be2b73ab25e42265f9de8e962`. The root agent identifies `88aba6a6d0276bd25e893958252b11fe07a1f05f` as the published commit with this tree.

## Spec Compliance

**Changes required for acceptance.** The Lean interfaces and moved declarations meet the mathematical task. The existing full local receipt fails the required declaration and transitive-axiom inventory for the 13-module scope.

## Task Quality

**Changes required in the auditor.** The source moves preserve the intended public signatures and semantics, the proof repairs are narrow, and the audit fails closed. The new audit needs to reconcile its two inventories on the actual coefficient module before this unit can receive acceptance credit.

## Findings

- **Critical — complete audit fails.** At `verification/P34CuspPacketAudit.lean:66`, the per-module multiset comparison of names from defining-module lookup and serialized constants fails for `ImbalancedChen.Part3CoprimePacketCoefficients`. The existing local log `.lake/p34-packet-acceptance/axioms.log:2` gives that exact diagnostic. The comparison precedes the per-declaration traversal at line 72, so there is no completed inventory or transitive-axiom receipt. The local report identifies the reviewed commit, 13 successful strict builds, 13 successful bundled replays, 14 successful parsed import commands, a successful import-scope regression stage, and exit code 1 from the audit. Identify the discrepant names and account for the actual serialized declarations, including generated and private declarations, before rerunning acceptance on the repaired source. The diagnostic alone does not identify the discrepant names.
- **Important —** No additional finding.
- **Minor — provenance pointer.** The module note at `ImbalancedChen/Part3CuspPhaseCore.lean:5` names only the previous relocation ledger. The source of the newly moved `norm_e` at line 16 is documented in the 20261126 ledger. A pointer to both would make its provenance discoverable from the module.

## Source checks

- Independently read all 15 ledger entries against the baseline Git blobs and candidate source. All donor file and donor block SHA-256 digests match the specified inclusive ranges. Each recorded signature occurs in its indicated donor block and candidate target, and 14 entire blocks are byte-identical. The sole changed moved proof is `norm_e`, whose new proof evaluates the norm of the exponential directly.
- The packet retains its positive level, coprime residue/level, multiplier and original beta. The coefficient gate is `Nat.Coprime n d.residue`. The modulated packet updates only beta and uses indices 2 and 3 on the respective variables divided by U and Z, each with factor 1/64. The pairing at `ImbalancedChen/Part3ActualCuspPacketPairing.lean:59` contains the full gated scalar entry, including its zero branch.
- The new signed corollary at `ImbalancedChen/Part3OldformCuspPhase.lean:33` uses the correct signs, a positive level, a positive height and the explicit Gamma0 invariance predicate. The referenced coefficients at `ImbalancedChen/Part3ActualCuspFourierSection.lean:180` and line 186 apply the genuine circle Fourier coefficient to the old and new sections. The scalar calculation supplies no oldform coefficient map. The diff adds no replacement original data or fixed block and makes no claim that the four staged consumers are proven.
- Both verifier catalogues and the new Lean audit list agree with their intended scopes. The shared verifier preserves the seven-module defaults, checks its exact compiled-mode HEAD, clean tree and configuration pins, hashes the new entry point and ledger, gates parsed imports on freshly rebuilt or locked objects, and invokes the checker from the compiler sysroot. The old acceptance evidence and archived source paths do not appear in the changed files.

## Evidence limits

The independent cloud result for the published commit had not been supplied at review time. Its Git object was unavailable in this local clone, so the published commit-to-tree mapping above is attributed to root. This review inspected existing receipts and ran no compilation or acceptance suite. The local failure establishes the candidate's outstanding acceptance defect.
