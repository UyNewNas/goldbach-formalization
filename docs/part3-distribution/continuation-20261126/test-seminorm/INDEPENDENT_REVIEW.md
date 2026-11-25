# Independent review of the P3.5 test-seminorm increment

**Ready to publish the acceptance receipt for the two owned modules.** This review covers all three commits from `5285d4f5d8c40eddf92c108b492c909de8b43cef` through `0ef2ad29bfa30917b3b9ec7008cb831ad1af9408`, together with the receipt and its original evidence. The exact mathematical tree is `b1072977ab2148625553ace3110ef3f743b8d794`. The supplied full diff matches Git's diff between those commits byte for byte. P3.5 remains open.

## Mathematical review

The terminal theorem `ImbalancedChen.Part3.ActualSpectralTestSeminorm.actual_uniform_testSeminorm_budget` uses the original period-64 coefficient of `normalizedF rho sigma` and the test `spectralMode ell (q/Y)`. The phase of that mode is the native positive exponential at frequency `ell 0 / 64` and the lattice is `Fin 4 → ℤ`. I checked these definitions against the unchanged reconstruction and weighted-budget sources and read the fully elaborated terminal type in the original audit. [Seminorm source](../../../../ImbalancedChen/Part3ActualSpectralTestSeminorm.lean) · [Compiler types](theorem-types.txt)

For a fixed mode and order, evaluating at zero witnesses nonemptiness. For positive `Y`, multiplication of the existing pointwise bound by `Y^n` bounds the entire real range. These facts justify both conditional-supremum inequalities and give nonnegativity. Summing over `0 ≤ n ≤ d` costs one Fourier weight of degree `d` because its base is at least one. The witness `finiteTestJetConstant d * A` uses the positive `A` supplied by `actual_uniform_weighted_l1 d` before introducing `rho`, `sigma` or `Y`. Nonnegative comparison first derives summability and then bounds the infinite sum by `C * (1 + rho)^(4 * (d + 3))`. Every mode and order has its own supremum over all real test points. The argument includes `d = 0` and `rho = 0`.

I checked the frozen appendix at lines 705–717, 757–776 and 1025–1028 against the local text with blob `7cf3bbb16cd8924565eb439e474e0674f04631da` and SHA-256 `e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`. The theorem supplies the fixed-order Fourier payment in A.5. The external transform estimates still require matching the tests, signs, normalizations and sufficient order. The code leaves the order arbitrary. The cumulative energies, uniform transform envelopes and actual Y04 row interfaces remain open. ABL, Kim–Sarnak and Pascadi remain external inputs. [Manuscript correspondence](MANUSCRIPT_BOUNDARY.md)

## Evidence independently checked

| Item | Result |
| --- | --- |
| P3 execution | Task `83126d04315b4091805fa85e6da8d6e7` records success, exit 0, 167.09 seconds and peak process-tree RSS 5,730,811,904 bytes. Its command, exact head, group and finished report agree with the receipt. |
| Source and environment | All 107 SHA-256 entries match both their blobs at the verified head and the checkout. Package revision logs match the lockfile and the recorded package and project status checks are clean. The increment adds only the two owned Lean modules to the proof sources and preserves the pins and existing proof files. |
| Logs and archive | All 35 stage commands, return codes and log hashes match. The ZIP has 35,063 bytes, SHA-256 `4941a7950ca6850f7f6e922f435db473b22c2f2379b0161582a131feef14ae67`, valid member CRCs and 39 unique members. Every member is byte-identical to its extracted peer and matches the member manifest length and digest. |
| Strict compilation and replay | Each owned source has a strict single-threaded compiler command with warnings as errors. Each bundled checker stage records its owned module being replayed. The two strict object digests in the receipt agree with the original report. |
| Inventory and types | The saved audit program has SHA-256 `0dc43439d66eaaf4fed6db100ebfa321e33d59cc57ebad6e271dc723a9a5d48e`. It retains the existing full serialized/environment inventory comparison and transitive collector, with just the two owned modules selected. The raw audit log reproduces all 40 unique declaration records, including complete types and axiom lists. Jets owns 27 and Seminorm owns 13. All 32 theorem entries reproduce the full theorem-types file byte for byte. The remaining eight records are definitions with types in the declarations file. The union of transitive axioms is exactly `Classical.choice`, `Quot.sound` and `propext`. |

[Original report](report.json) · [Original ZIP](p35-test-seminorm-0ef2ad29.zip) · [Task metadata](CLOUD_TASKS.json) · [Inventory](declarations.json) · [Receipt](RECEIPT.json)

## Source provenance and review findings

I read the M, R20 and S22 donor blobs from Git at `52098e403ac4b28c72ec5958fd738ae93d785ac5`. Their recorded blob IDs, lengths, SHA-256 digests and all six exact line ranges match. Five supplier excerpts occur uniquely in the frozen extraction and the S22 excerpt occurs uniquely in the consumer. The 33 written declarations comprise 22 selected declarations and 11 new ones. The original public names are preserved. The additional phase smoothness proof matches the reconstruction source after renaming the mode variable and adjusting indentation. The historical scope patch has its registered blob ID. Regenerating the unified diff from the extraction and final supplier reproduces the entire recorded repair patch. The verifier now binds the excerpts to the intended files as requested by the earlier review. [Donor excerpts](DONOR_EXCERPTS.json) · [Repair patch](SOURCE_REPAIRS.patch) · [Scoped rereview](PROVENANCE_REVIEW.md)

I independently traversed the imports from the two project roots and matched all 55 project files, import lists, Git blobs and SHA-256 digests across the base, mathematical head and donor. These imports retain their existing trust boundary. The new source files contain none of the five prohibited proof escapes. [Dependency closure](DEPENDENCY_CLOSURE.json)

Both editorial findings are resolved. The first build reported an unknown identifier for `abs_ofNat`, and the corrected README describes the lemma as unavailable. The README also maps the historical handoff's `jet-supplier-closure.json` to the published `DEPENDENCY_CLOSURE.json` and identifies the clean mathematical checkout required by the reproduction command. The final text edits leave the verified sources, provenance manifests, verifier, workflow and pins at the reviewed commit.

## Limits of the verdict

This independent review used the saved compiler evidence and local Git objects. The ZIP carries the compiler-reported hashes for the two strict objects. It does not carry the object binaries, so those particular bytes could not be rehashed locally. The P3 report records their hash checks after the audit. No Lean run, kernel replay, cloud job or duplicate acceptance was performed in this review.

P1 completed its current-workspace filename inventory. It enumerated 15,040 directories and 144,311 files in the documented search scope, found no candidates for the six exact Y04 basenames and reported no traversal or file-read errors. The complete output was 1,714 bytes. The P2 inventory was still queued at the 17:08 UTC update. Availability outside the searched P1 scope remains unresolved, as do the sufficient derivative order for Pascadi and the remaining P3.5 interfaces. [P1 inventory](P1_SOURCE_RECOVERY.json) · [Recovery scope and P2 status](CLOUD_SOURCE_RECOVERY.md)
