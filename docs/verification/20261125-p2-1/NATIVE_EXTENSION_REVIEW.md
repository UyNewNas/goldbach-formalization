# P2.1 Buchstab native extension review

This is input qualification tooling, not mathematical proof acceptance. It is
needed because the selected 515-module snapshot does not contain the three
existing upstream Buchstab modules used by the manuscript's omega interface.
It preserves the original snapshot and all project compilation/audit records.

## Fixed scope

The only source compilation targets are
`MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction`,
`MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds`, and
`MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation`, from the existing goldbach
commit `09b97db5764ade1246bfb77206baa1b124760958`. No theorem body is edited.
The producer binds original Git blobs, the qualified input closure, compiler
identity, actual loadable object paths/facets, and unchanged inputs before and
after each successful source compilation. It reuses an earlier provider only
when that full context, its outputs, and its log still match.

The private MathlibNt overlay links the complete qualified namespace and adds
only the successful new providers. Missing standard-library/Mathlib input
bindings cause failure rather than new acceptance. Standard sources recovered
from a pinned checkout behind an object overlay retain their original frozen
hashes and each source's exact Git blob check.

## Review corrections and regression evidence

Independent source review identified premature final snapshot publication.
The final script first validates a candidate through `ExternalSnapshot`, then
atomically publishes the same verified bytes and the separate success marker.
A second review removed a fallback-root cache that could bypass subsequent
per-file Git blob checks. Neither correction changes a Lean source.

The saved regression command was run on the final script:

```sh
PYTHONDONTWRITEBYTECODE=1 python verification/part2/test_extend_p21_buchstab_native_snapshot.py -v
```

Result: three tests passed. The cases cover the implicit Init/transitive input
closure and changed-input rejection; a frozen Batteries source whose checkout
is absent from the object search path; and rejection before either final
snapshot or final success marker is published.

Final extension SHA-256:
`622d78e654602c00e94a56ed72c1c5f9fde811924c001b62f85184a4ce841b4e`.
Regression source SHA-256:
`c5882ce54b8e08c8392527b64dfcdcfbf77063f479e033edf55990465be894c5`.

This report does not claim that the remote extension has run. Its snapshots
always retain `compile_credit=false` and `kernel_credit=false`. Independent
kernel replay and complete owned-declaration/transitive-axiom audit remain
separate requirements for the project roots that consume these inputs.
