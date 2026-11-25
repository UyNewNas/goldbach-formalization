# P3.6 pinned native research source resolution

Status: runner regression tests pass; no new Lean compilation, kernel replay,
or mathematical acceptance is claimed by this change.

## Exact source provenance

The warm closure's existing `ImbalancedChen.P2EnhancedSortedDwellMerge`
imports `MathlibNt.Wu2008DoubleSieve.ReboxingSorted`. The required source is
tracked by the already pinned external `goldbach` repository:

| Field | Value |
|---|---|
| Repository | `https://github.com/subfish-zhou/goldbach-lean.git` |
| Required commit | `09b97db5764ade1246bfb77206baa1b124760958` |
| Tracked path | `research/wu2008/src/MathlibNt/Wu2008DoubleSieve/ReboxingSorted.lean` |
| Git blob at that commit | `774e5a76b3945481df4472bc334ea1a38d1446e9` |
| Source SHA-256 | `ee014d80c24906c74d62d0330f66df0b3c7604e0d91178f4c7bba18b2c2a5af8` |

The local pinned checkout contains this source at the nested path; its
top-level `MathlibNt/Wu2008DoubleSieve/ReboxingSorted.lean` path is absent.
The source SHA-256 matches its entry in
`goldbach/research/wu2008/source-manifest.json`. That manifest labels its
historical object binding `matching_object_imports_rebuild_required`.
The historical object hash is not an accepted build receipt here.

The external repository's top-level Lake configuration uses the ordinary
library roots. Its separate `research/wu2008/build.py` compiles research
sources with `-R research/wu2008/src`. The P3 direct runner previously looked
only below each package root and consequently reported this tracked source
as `missing_module`.

## Resolver and audit change

The fallback is fixed to package `goldbach`, namespace prefix
`MathlibNt.Wu2008DoubleSieve.`, and directory `research/wu2008/src`.
It is used only when the ordinary package-root source does not exist.
No arbitrary nested source roots are discovered.

The node keeps `package = goldbach`; its shared cached-object path remains
`goldbach/.lake/build/lib/lean/<module>.olean`. The node's `source_root`
becomes the nested source directory so direct Lean compilation receives the
correct `-R` argument. New objects still belong to the runner's own output
directory. Existing top-level sources and exact flattened aliases retain
their previous lookup precedence.

The native source audit uses `packages/goldbach` as its Git root, independently
of the selected Lean source root. A nested source is therefore checked using
its full package-relative tracked path. An untracked source at the registered
nested path is rejected. Existing flattened aliases must still match the
corresponding tracked research source exactly.

Dependency pin checks, checkout-cleanliness checks, selected-project-source
hashes, source snapshots, recursive import signatures, object-sidecar checks,
namespace-shadow rejection, fresh strict owned compilation, kernel replay,
and the owned declaration/axiom inventory are unchanged. The native source
is not copied into the project or relabeled as project-owned. No dependency
package or Lake configuration is modified.

## Regression verification

Before changing the implementation, the three new focused tests were run:

```bash
python3 -m unittest -v \
  test_compile_p36_local.RunnerTests.test_pinned_nested_native_sources_keep_external_ownership \
  test_compile_p36_local.RunnerTests.test_nested_native_audit_uses_package_relative_paths_and_checks_aliases \
  test_compile_p36_local.RunnerTests.test_unregistered_nested_native_roots_remain_missing
```

The result was exit 1 with four expected assertion failures: missing nested
source, lost source binding for a cached nested module, missing transitive
nested dependency behind an existing flattened alias, and an incorrect Git
audit root. The unregistered-root negative test passed.

After the implementation and the additional untracked-nested-source audit
case, the complete runner suite was run from `verification/p36`:

```bash
python3 -m unittest -v test_compile_p36_local
```

Result: exit 0, **15 tests passed**. The suite includes cached and uncached
nested resolution, external ownership and `-R`, existing flattened-alias
precedence, alias-content drift rejection, untracked nested-source rejection,
and rejection of unregistered package/namespace roots. Its existing cache,
sidecar, namespace-shadow, and fresh-owned-verification tests also passed.

| File | SHA-256 |
|---|---|
| `verification/p36/compile_p36_local.py` | `be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709` |
| `verification/p36/test_compile_p36_local.py` | `5966bf838488f51ade30d690c5021b49184e8059e7c7624dba5dce1d704d416a` |

An independent read-only review confirmed the package/source-root split and
that the existing preflight snapshots and recursive signatures capture the
nested source, including when an external cached object exists.

Read-only resolution of the real local source selected the expected native
file with the recorded SHA-256. A local recursive graph inspection found
4,695 nodes and 329 blockers; the first reported blockers were missing
Mathlib cache objects in that local runtime. This was not a successful full
preflight and says nothing about the remote cache inventory. The research
module's broad actual dependency chain still requires the ordinary remote
preflight, compilation, kernel, and axiom gates when a consumer reaches it.
