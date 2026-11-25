# Independent review of the fixed-width reuse packet

**Result: byte preservation and source dependency checks passed. This is not Lean acceptance.**

Reviewer: `/root/p36_source_recovery`. The review read the prepared packet and fixed Git objects at `c6b89774822580c731a236ac66dcd7466ac8a0e6` in the P15 donor. No source, manifest, runner, or remote task was changed during the checks. This report records the completed checks without rerunning them.

## Exact source preservation

Five original Git paths were read at the fixed commit and checked against both the recorded Git blob IDs and SHA-256 values. All six prepared files also matched their recorded byte lengths and SHA-256 values in `PREPARED_FILES.json`.

The original `P1OriginalFourthMovingPrimeIntervalBound` blob is `9257f9732dcaef76ea7ab19a122edb7b3f54e597`, with source SHA-256 `530d01fcacccbde865f8e1b2e15efce8e7141a743483c625df073209ffdfa0d8`. Its byte range [861, 3316) contains exactly the two declarations `one_add_reciprocal_sum_le_euler` (private) and `exists_uniform_reciprocal_interval_bound` (public): 2455 bytes, SHA-256 `65182c851f5adcff9dcbfff8a946b9ef6c2654ceea617903470160480c60b6c3`.

That complete block occurs unchanged in the new `P1ReciprocalPrimeIntervalCore` source, SHA-256 `ecdd92cc98d0a1ab993e70a256333ba6e568aab248bef2032f074bbf2fa3edfe`. The public namespace remains `ImbalancedChen.P1OriginalFourthMovingPrimeIntervalBound`. The private helper is used only inside the extracted block; the compatibility file and downstream interval/slab files call the public theorem. The fixed supplier lemmas `roughPrimeFinset_odd_of_even` and `roughPrime_eulerProduct_le_inverseProduct` remain provided by the existing `RoughAbsoluteDensity` module.

Removing the new core import from the compatibility file and reinserting the exact block at the recorded position reproduced the entire original file byte for byte. The compatibility file preserves the remaining declarations and original imports.

The prepared `P1ActualMovingPrimeIntervalEnvelope` differs from its fixed original only by replacing its one import of the old full module with the new core import. Reversing that substitution reproduced the original bytes. The prepared `P1ActualMovingAffineWallMass`, `P1ActualMovingCoordinateSlab`, and `P1ActualMovingAffineSlab` files are exact copies of their original fixed-commit bytes.

## Independently recomputed dependency graph

The review rebuilt the target graph from the actual 57 selected project source files, checked every file hash, and compared every import list with `DEPENDENCY_PREFLIGHT.json`. The graph matched exactly, with no missing project source and no cycle. The old full compatibility wrapper is not reachable from the new target.

The additional selection contains exactly six modules: the new interval core, the four existing interval/affine/coordinate modules, and the fixed-width candidate. Relative to the selected baseline, the only new direct external import is `Mathlib.Data.Fin.Tuple.Basic`.

The baseline manifest contained 274 selected modules, with SHA-256 `f77468ef3bbc9f49294df0242079a58594ceae0679cc5d4d038c3f12a2861d4d`. Its bytes were checked before and after the review and were identical. Every overlapping source hash matched the baseline selection.

**Only the new 57-module graph was independently recomputed here.** The 205-module original closure is a previously recorded historical preflight result; this review does not claim to have rerun that older graph.

## Acceptance boundary

No Lean process, bundled kernel replay, full declaration/type inventory, or transitive axiom audit was run for this packet by this review. The extracted declaration bodies are byte-preserved source; successful elaboration in the reduced import context remains a later verification gate. No complete P3.6 result is claimed.

