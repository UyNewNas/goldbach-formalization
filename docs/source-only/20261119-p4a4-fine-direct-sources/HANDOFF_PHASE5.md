# P4A.4: atomic R17 source and finite-input boundary

SOURCE_ONLY / COMPILED: NO / KERNEL_REPLAYED: NO / TRANSITIVE_AXIOMS: NOT CHECKED / INDEPENDENT_REVIEW_THIS_RUN: NO / FINITE CERTIFICATES: UNEVALUATED.

Baseline 70a0de842b7f08832bba69d79f0efc0a55b58c32. This phase stages all four registered R17 postimage sources together and the independently preselected FullPolicy API postimage. They are existing proof candidates, not new Lean proof bodies; the original compiler/count conditions and all underlying pins are unchanged. The SOURCE_SELECTION_PHASE5.json records the exact Git/SHA-256 preimages, postimages, source paths, imports and data-boundary evidence.

## Actual staged semantics

Four preimages were read from the immutable registered origins and matched their Git blobs; the four postimages were read at the baseline and matched their registered Git blobs and SHA-256. Their byte diffs show:

- The literal comparisonChart cases 15–18 change from 0 to 3.
- For chart 3, the selected comparison is R17(t) = 57/64 - 3*(t 0+t 4)/2. The source includes source_r17_above_r0 under the existing Source and chart hypotheses.
- The affine program adds the matching fourth branch; the square-row candidate uses that result to handle the >1/2 comparison gate.
- These four files are a semantic group. The former R0-based versions are not interchangeable objects for the corrected source environment.

The FullPolicy preimage blob 79d8a7c3e92e240aeb818e3a972d026ca7f4234c was read from the baseline. Its registered PUBLIC_API.patch blob 7c789fb4d7055de569d9f6cccadc4731b525646f changes the existing open declarations to take finiteMax and producerEligible from P1OriginalVariableFourthContinuation. Applying that exact single textual change in the isolated stage produced blob 6e2ef067b5e2e1a1a5f52e5f6d81c4b353ca4c9c and SHA-256 01f09fb673c06fb7950c3eff48dbe9dc815c9dc983afe6f61341a171475a2324, equal to INSTALLATION_OVERLAYS.json. This is a source-postimage identity check, not Lean elaboration. All five postimages are included in the packet at distinct canonical module-relative paths.

The 99-file packet plus historical v3 import metadata yield 1698 reachable named project sources, of which 99 are physically staged and 1599 exist only as manifest entries in this check, with 17 unresolved names in that union and 232 external import names. This incomplete syntactic graph does not verify actual loaded modules, coherent full closure, or object reuse. The historical v3 registry identifies 140 R17-affected active modules and prohibits restoring their old objects; that is its historical declared scope, not a new compilation receipt.

## Q96 and data boundary

LATER_PAYMENT_REGISTRY.json at blob 25854e6dab94664785036e96738f67d6b7255b59 records 10 witness JSON files and five navigation JSON files by length and SHA-256. None of their basenames occurs in the 335 rows of the older full87 v3 data_inputs table. This is a comparison of two recorded tables; it does not establish that files are absent from every archive or that each is required by Lean at compile time. The current task workspace search for .npy, .npz, witness JSON and .bin returned no files (rg exit 1), so those fixtures' bytes were not verified here.

For the R17 nonsingleton source, the later registry and R17 registry both record sixth-nonsingleton-freecap-20261009.witness.json, 1,175,936 bytes, SHA-256 18b38a75557fbd2633f95ff6a482d9fd8fd6d03ae33c6ca64d5e5d2eb21be8ae. These are recorded identities, not freshly checked data. G7's source registry records eleven cells, 2,631 simplices, eight Q80 factors per row, and the selected numerator 1208544915921356327515701/2^96 replacing 1201130581437641342320905/2^96; no finite computation or certificate replay was run. The fuller fixture list and recorded hashes are in SOURCE_SELECTION_PHASE5.json.

No K-ledger/radial variant was changed; the original Fine-selected versions and their alternative reference copies remain separately recorded in prior handoffs. The original same-policy F/Q/rho, separate compiler/density reserves, actual presieve correction and signed error are not altered. This packet neither establishes full All22 nor pays signed PP.

## Verification / continuation

Python and git byte/hash checks and four `diff -u` commands were run on the isolated staged files; all observed pre/post identities matched the registered blobs, and the diffs exited 1 because the documented changes exist. No numerical guard, Lean/Lake, kernel replay, axiom audit, new independent review, CI or user-machine access occurred. The runtime executables remain unavailable. Exact sources/data/overlays outside the packet are unverified; do not treat a source-only R17 selection or a slot-specific CI success as full closure.

Next bind the genuine later witness inputs to the exact selected consumers and compute actual compile-time requirements; complete source and overlay provenance, retain the explicit K/radial variant choice, then compile/replay the precise Fine terminal and its downstream consumer in the pinned existing toolchain environment.
