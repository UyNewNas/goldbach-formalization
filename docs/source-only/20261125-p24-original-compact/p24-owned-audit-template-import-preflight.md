# P2.4 owned-audit template import preflight

Status: read-only finding; no template or gate change, no new compilation or
audit credit. Canonical symbolic task `bb4d0ea087c8466b945c36f6e68a2b04` remains
pinned to `ed3b16671f377f1e122db28baaae321cf667a597`. Its queued state was checked
at 2026-11-25 18:28 UTC (2026-11-26 02:28 Asia/Shanghai).

## Trigger and scope

A bounded read of bytes 0 through 4095 from the preceding P2.1 task
`2ce03fb36f3345d3951f1f3d7aa1b9e5`, source
`c9ed46169c349545e67045e39c23ce8caee9f876`, reports owned-audit failures for
`OriginalNodeArraysV1.Block00Data` and subsequent data blocks:

```text
Audit.lean:11:15: error: unknown namespace `Command`
Audit.lean:12:0: error: to use this command, include `import Lean.Elab.Command`
```

Those data blocks are not in the current P2.4 closure. Within the current
324-module closure, the complete project ancestry of exactly one target uses
only Std/Init: `ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore`.
Its sole direct import is `Std`, its project closure has one node, and its
source SHA-256 is
`ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d`.
The other 323 targets have external mathematical imports in their ancestry;
this observation establishes neither their audit failure nor their success.
DataCore's own audit in this P2.4 checkout has not yet run.

## Template dependency

The existing `winner9_private_audit_template.lean` has SHA-256
`2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b`.
Besides its target it imports `Lean.Util.CollectAxioms`, while its body uses
`Lean.Elab.Command`, `run_cmd`, and `liftTermElabM`.

At the fixed Lean commit `62eed1db4d67327ec8120be05f1a1b0847d74561`,
[CollectAxioms.lean](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Util/CollectAxioms.lean)
explicitly imports `Lean.MonadEnv` rather than the command elaborator.
[Command.lean](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Elab/Command.lean)
defines the missing namespace and `liftTermElabM`.
The bounded review of existing local templates and related historical
owned-audit files found no already corrected equivalent template. This is
not an exhaustive search of unseen branches or artifacts.

Adding `import Lean.Elab.Command` is the smallest identified candidate for
the observed missing API. It has not been compiled here, and this finding
does not establish that it resolves every audit elaboration requirement.
No proof statement, mathematical definition, checker, template, or receipt
was changed for this preflight.

## Preserve existing evidence before deciding a repair

Keep the current symbolic run and subsequent strict finite gates unchanged.
After the full 324-module strict closure is accepted, first run the existing
evidence exporter as specified in `p24-finite-and-owned-audit-execution.md`.
Retain the exact accepted historical receipts and identify the actually
unselected targets before changing any audit input or scheduling work.

If DataCore still lacks accepted evidence, handle its audit explicitly and
retain any real diagnostic. A template repair must carry a new source and
template identity, preserve the complete original audit body and all checks,
and undergo actual targeted verification. Do not edit old receipts or claim
that an audit under the old template ran under a new template.

The original gates still require exact owned-inventory agreement, full types,
no unsafe/partial/axiom declarations, the same project import closure, allowed
transitive axioms only, and unchanged physical inputs before and after audit.
An added Lean core import does not itself prove those gates passed.
Existing valid compilation and stable independent replay remain reusable
only through the original rules; replay reuse does not depend on the template
hash alone. Resolve the actual historical-receipt coverage before choosing
the repair and audit batches, rather than invalidating useful work in advance.
