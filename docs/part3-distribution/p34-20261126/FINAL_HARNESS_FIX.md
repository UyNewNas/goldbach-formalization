# P3.4 verifier and provenance repair

The repair commit is `78576ae50703e5c7c8af259d46ab258741093bac`, tree `fca71215e562bfe8ee5a48c0de3d59589a94b2e2`. The parent is the reviewed source `57feba1f98b8411e39f50589d05f649b70c94dc5`. The checkout was clean after commit. The isolated verification checkout was also clean at the exact repair commit before and after the covering runs.

## Findings addressed

1. The three import regressions now compile two tiny Init-only fixtures once under an ignored, automatically removed `.lake/p34-import-test-*` directory. Each subprocess replaces the inherited `LEAN_PATH` with the fixture directory. The real pinned `lean --deps` parser supplies all dependency paths to the unchanged production validator. The indented and same-line negative cases identify the precise rejected fixture object, and the positive case requires both objects in the result. Only the resolved toolchain library remains an external root for this test.
2. Both verifier modes observe Git HEAD and `git status --porcelain --untracked-files=all` before enforcing the requested exact HEAD and its descent from the baseline. The preview preserves the prior ability to scan dirty sources for proof escapes and pin drift. It records the actual porcelain output alongside the observed HEAD and the working-tree source hashes, with status `SOURCE_ONLY_NOT_COMPILED`. Compiled mode requires a clean tree and retains the final working-tree and source/object hash checks.
3. `docs/part3-distribution/p34-20261126/README_PRESENTATION_SUPERSESSION.json` binds the original README bytes at `7596a3cbfba48f0764676ea2b1803caa20260b7c` and the presentation revision introduced at `f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e`, verified at `57feba1f98b8411e39f50589d05f649b70c94dc5`. The old digest is `336360ed33356480f83449075ab74b48b19c5df9692abe1e3208355948f1390d`. The current digest is `55970070f35e0ec4f34abca0e82c3160b617454ba4f396e8d75ee2cf64703169`. The historical manifest is byte-identical to the manifest at the original binding, all 55 archived verification artefacts match the original manifest and Git bytes, and the other eight supporting-file digests match.
4. Staged `/workspace/library-files/p34-evidence-staging/PRIMARY_ACCEPTANCE.md:28` now says “arbitrary natural-number labels,” which agrees with `∀ qf v : ℕ` in `ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean:50` and line 77.

## Reproduction and verification

Logs are under `/workspace/library-files/p34-evidence-staging/final-harness-red.s1RDK0`. The old isolated checkout had only Lean sources and an empty project-object directory. These commands used the fixed runtime on that checkout at `57feba1f98b8411e39f50589d05f649b70c94dc5`.

```bash
source /workspace/library-files/p34-runtime/env.sh
export LEAN_SYSROOT="$(lean --print-prefix)"
export LEAN_PATH="$PWD"
python verification/test_p34_import_scope.py -v
python verification/verify_p34_cusp_normalization.py --source-only \
  --expected-head fa22a56829ee880404516a36d498ce27dcb32f92 \
  --output-dir .lake/final-harness-wrong-head
python verification/test_p34_source_provenance.py -v
```

The old parser run exited 1 with two failures and one error at missing project object paths. The old wrong-head invocation exited 0 and reported `SOURCE_ONLY_NOT_COMPILED` with no `head_commit` or `working_tree`. The provenance tests copied into the old worktree exited 1. The wrong-head assertion saw exit 0, and the matching-head positive control found the observed HEAD field absent. See `parser.log`, `wrong-head.log` and `provenance-regression.log`.

The exact repair commit was checked out in the same isolated workspace. The fixed compiler reported version `4.33.0-rc1`, compiler commit `62eed1db4d67327ec8120be05f1a1b0847d74561`. Both project-object checks below passed. The complete Python regression discovery run passed **5/5** in 0.943 s, recorded in `green-exact-head-suite.log`.

```bash
source /workspace/library-files/p34-runtime/env.sh
unset LEAN_PATH LEAN_SYSROOT
export LEAN_SYSROOT="$(lean --print-prefix)"
test -z "$(find .lake -name '*.olean' -print -quit)"
env LEAN_PATH= python -B -m unittest discover -s verification -p 'test_p34*.py' -v
test -z "$(find .lake -name '*.olean' -print -quit)"
revision="$(git rev-parse HEAD)"
for scope in primary_arithmetic primary_dyadic; do
  python -B "verification/verify_p34_$scope.py" --source-only \
    --expected-head "$revision" --output-dir ".lake/final-harness-$scope"
done
```

The primary and dyadic entry points returned `SOURCE_ONLY_NOT_COMPILED` with the exact observed head, an empty working tree and the three successful Git stages. Their catalogues contained four and nine modules respectively. With an untracked `final-harness-dirty-probe.txt`, the primary source-only command stayed successful and reported that filename in the porcelain output together with the source hashes. The same command without `--source-only` failed before Lean with the matching dirty status and recorded diagnostic in `green-dirty-compiled.log`. Removing the probe restored a clean checkout. An extra matching-head provenance probe supplied an unrelated root commit to `main(baseline=...)` and produced `FAILED`, with exit 1 for `baseline-ancestor` and no Lean stages.

For the presentation mapping, `git show "$revision:docs/part3-distribution/p34-20261125/README.md" | sha256sum` reproduced each of the three revision bindings. Each archived verification entry was independently checked by SHA-256 against both the manifest and `git show` at the historical binding. The full historical directory tree ID is `200e6a18a323576b08b6323b9e71e25ffdc6fb68` at both the presentation edit and the frozen parent.

`git diff --cached --check` passed before commit. The commit changes only the shared verifier, its parser test, the focused source-only provenance test and the new presentation mapping. The staged prose edit is outside the source commit. The Lean sources, audits, ledgers, frozen toolchain and package pins, and historical receipts are byte-identical to the reviewed parent. Only the two test fixture modules were compiled locally for this repair. The clean dependency-only compiled receipts for the four- and nine-module scopes remain with the root agent.
