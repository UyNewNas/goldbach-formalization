# P1 continuation: source publication before cloud compilation

Status: **SOURCE ONLY — the four P1 terminal modules have not yet passed normal compilation, independent kernel replay, or the complete owned-declaration audit.** The existing 325 accepted supplier receipts remain historical prerequisite evidence; this commit does not increase that accepted count.

This checkpoint implements the user's instruction to publish the code first, pull the exact commit into the existing cloud environment, and compile there. It materializes the already selected 1,771-source P1 dependency closure at canonical module paths so an ordinary checkout can build the four targets directly. Existing source proofs are reused byte for byte according to SOURCE_SELECTION.json; no alternative proof of the primitive suppliers was written.

## Four terminal targets

- ImbalancedChen.P1OriginalFinalPolicyRawBound
- ImbalancedChen.P1OriginalFinalPolicyStructure
- ImbalancedChen.P1OriginalFinalPolicyAncestorReads
- ImbalancedChen.P1OriginalCompleteFormalProof

The complete endpoint uses one cofinal q, one beta/k selection, the literal finalPolicy, and the same physical coefficient. It includes the complete raw bound, compiler reserve, integer majorant, nonzero support and actual rough-factor ancestor reads. The matching signed distribution error remains explicit; this is not a proof of the separate prime-product distribution input.

## Changes requiring compilation

The four terminal source bodies are reconstructed thin compositions of existing manuscript suppliers. Two exact previously published suppliers, EarlyDefectCounting and CofinalCoefficient, are reused. PPSchedule changes only its unused PhysicalSelected import to the existing Count import; its declarations and proofs remain unchanged. P5JointNativeSignedRegroup changes only the comment text `+U6/-U10/-U11` to `+U6, -U10, -U11`, removing two accidental nested-comment delimiters. The declarations and proof text are unchanged.

SOURCE_SELECTION.json fixes the complete canonical dependency graph and every source SHA256. recover_p1_sources.py records the provenance recovery from the unchanged R03, Density, Full87 and 325-supplier registration at the baseline commit. It is not required to regenerate sources already materialized by this commit.

## Existing cloud environment

The cloud checkout is /workspace/p1-mcp-20261124. It already has the pinned Lean 4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native Goldbach 09b97db5764ade1246bfb77206baa1b124760958 and LeanArchitect 78dd66840d3efe8c824c699fc03381cec817c271 dependencies. Reuse those dependencies and the original 357 verified numeric inputs. Those inputs are available in /workspace/p1-stage-20261124 and the required sibling data directories; copy only any exact missing data into the checkout before building, or continue in that prepared stage after pulling and synchronizing this manifest's sources.

Run the existing guarded standard Lake command for these four targets:

```sh
lake build ImbalancedChen.P1OriginalFinalPolicyRawBound:olean ImbalancedChen.P1OriginalFinalPolicyStructure:olean ImbalancedChen.P1OriginalFinalPolicyAncestorReads:olean ImbalancedChen.P1OriginalCompleteFormalProof:olean
```

After a successful normal build, run named-module leanchecker for each terminal, enumerate and audit all environment-owned declarations including private/generated declarations, check transitive axioms, and finish with the corresponding standard no-build command. Do not mark P1 complete from this source publication or from the existing supplier count.
