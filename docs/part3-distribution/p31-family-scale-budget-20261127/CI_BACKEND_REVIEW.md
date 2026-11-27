# Independent review of the family-scale CI and build-backend selection

**Disposition:** No Critical or Important findings. Suitable for an exact-head CI run. The reviewed verifier SHA-256 is `e2b6fe25dbe2e7d594b1f21eaff8aaefec5f990c04b8d14eb3bffaca27228f91`, and `.github/workflows/p3-1-family-scale.yml` is `b295caf55be522b978281ab0b3b4aad3b220fe5598e2f2eb78945088ccf8d8d3`. The direct builder remains at the independently reviewed `daeaa30d55219213064905d4e3033bff0164ffa9311865785eb92be5b78f0631`. This review was read-only and did not launch any remote run.

## Critical / Important

None. In particular, a matching Lake cache, passing source-only preflight or successful build of prerequisite artifacts cannot set the verifier's proof result to `PASSED`.

## Minor

- The module-level verifier docstring describes only the default Lake backend. The new option's `--help` correctly identifies the explicit direct mode.
- Addressed during review: the original workflow's two terminal-specific path filters could skip a future provider-only change. The final workflow uses `ImbalancedChen/**/*.lean` on the same designated branch. Restoring the original two lines reproduces the complete initial workflow digest, confirming this was the sole follow-up change. The final YAML parsed and the family source-only verifier recorded the new workflow digest.

## Verification route

- Compared the shared-verifier diff against `96d8c62e`. The default is `lake`. Explicit `pinned-direct` is allowed only for `family-scale-budget` and fails during argument validation for every existing group, prior to creation of the output directory. Historical group tuples and their default build command remain unchanged. The family report identifies the requested backend and hashes its workflow file.
- Both family backends run the same source validation, 85-provider freeze, clean project, exact expected HEAD, toolchain paths/version, package revision and clean dependency checks. Only the prerequisite build command diverges. After that branch both collect the common project-object snapshots, delete and strictly recompile the two terminal modules, replay both terminal modules individually, run the exhaustive declaration/axiom audit, verify provider immutability and recheck the final source/object hashes and working tree. Both scope flags remain false.
- The workflow runs on the selected proof branch and checks out the submitted SHA with full history. The final verifier receives `--expected-head "$GITHUB_SHA"`. The toolchain installer is separately checked out at an exact revision, verified, then moved out of the checkout before final verification. The job requests read-only repository contents and only uses full commit-pinned checkout, restore and upload actions.
- The primary cache key identifies base commit `96d8c62edc5f8e4c196441ab680bcf34b1dcbe8a`. Its two `hashFiles` components were independently recomputed from the local toolchain and manifest using the individual-file digest followed by the overall digest. Its `.lake` path and key shape match the previous `lean.yml` cache writer. A compatible same-platform/architecture/toolchain/manifest prefix is available on exact miss. It still fetches the pinned Mathlib cache and invokes the full formal verifier after restore. Cache hit, actual bytes and GitHub-hosted build success must be read from a future real job.
- `always()` uploads the entire fresh runner-temp verification directory (including ancillary logs). The portable ZIP separately includes all verifier products, including stage logs, generated audit, report, declaration inventory and theorem types when produced. Its only exclusions are installation and Mathlib download logs, which remain in the artifact. The portable mechanism also works on partial failures, so consumers must inspect `report.json` and the job outcome. A separate local three-chunk ZIP round-trip recovered exactly the expected bytes and validated the emitted SHA-256.

## Independently executed checks

- Parsed the workflow YAML and checked each embedded shell step with `bash -n`.
- Ran the actual family verifier in source-only mode twice in isolated temp output directories, once with the default and once explicitly using `pinned-direct`. Both reported `SOURCE_ONLY_NOT_COMPILED`, identical source hashes, 85 old providers, the correct workflow-file hash, and both scope flags false.
- An invocation of the old `actual-mass-budget` group with `pinned-direct` returned code 2 without creating its output directory.
- Exercised the workflow's actual portable packaging shell/Python against three sample verification files, including nested and multi-chunk data. Validated chunk ordering, decoded the SHA-checked ZIP and compared all three files byte-for-byte. Both ancillary logs were excluded as designed. No formal proof receipt was available or inferred in these checks.
