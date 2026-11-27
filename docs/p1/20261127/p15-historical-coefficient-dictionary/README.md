# Historical coefficient dictionary: exact if-neg proof repair

## Observed failure and minimal source change

The actual AM whole-source probe ran in
`job_b852fda8ce794982b7938d5f29b5a9a8`. Original D288/W58 acceptance preparation
completed, direct-import no-build readiness passed, and the complete candidate
was submitted once without output artifacts. Lean returned exit 1; the final
preservation checks passed. The retained RESULT is **88801 bytes**, SHA256
`af4e73221e1e2ed9ea923673a335a4a97eb88b4326d505eacca2e0f98a82e707`.

The diagnostic has one remaining goal in `trueDDeltaRho_mul`, for the policy
case `fresh=false`, `old=true`: negate an `if` expression versus the same `if`
with each branch negated. Both sides use the same original condition
`0 ≤ ArithmeticFunction.moebius b`. This is a proof-closing gap; it does not
require changing the coefficient or choosing beta with a negated Möbius value.

The old concluding proof line is:

```lean
    simp [roughMaskDelta, attachedMobius, hnew, hold, signAttachedCoefficient]
```

It is changed to:

```lean
    simp [roughMaskDelta, attachedMobius, hnew, hold, signAttachedCoefficient] <;>
      split_ifs <;> rfl
```

The source grows from **9079 to 9107 bytes**, exactly 28 added bytes. Reversing
this one edit recovers the complete original AK file byte for byte. All
declaration headers, definitions, imports, hypotheses, support conditions,
remaining-modulus masks and the original Möbius beta selector are unchanged.
The new source SHA256 is
`eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff`.

The corrected file is to be published at:

`docs/source-only/20261127/p1-historical-coefficient-dictionary-if-neg-repair/P1OriginalHistoricalCoefficientDictionary.lean`

The original AK source-only path is retained with its original 9079-byte
contents. The old local eight-file AM package and the old unbound formal draft
were not modified. No corrected-source Lean command has been run by the author.

## Version 2 probe and exact stager

The new probe and stager use the same package paths in a new descendant
publication:

* `docs/p1/20261127/p15-historical-coefficient-dictionary/probe_dictionary.py`
* `docs/p1/20261127/p15-historical-coefficient-dictionary/stage_dictionary.py`

The new probe is **29728 bytes**, SHA256
`4ff5139a3c9eacd16f29e11a99da8cee7c20541a284ad9538458b3caaf4ea8c4`.
The stager is **5075 bytes**, SHA256
`072845e198a316fc5f95189612348858ec7ac9c50a03275d568978198c632ebd`.
Both enforce the exact original-to-repaired source delta, not only a changed
source fingerprint.

The new result schema is
`p15_historical_coefficient_dictionary_whole_no_output_probe_v2`. It records the
new publication/source origin separately from the original AK source and the
original failed AM result. It preserves the real failed AM identity; it does
not rerun, overwrite, relabel or rebind the AM attempt.

`failed_probe_snapshot` reads the original cloud RESULT from:

`/workspace/p1-complete-proof/20261127-p15-historical-coefficient-dictionary-probe-v1/45e8de70fb3045b04f3ef3ad2ff364c7ee2f390c/runs/attempt-00000/ACTUAL_DICTIONARY_PROBE_RESULT.json`

It checks the exact 88801-byte fingerprint and the original failed schema,
source, scope, exit-1 status, completed original dependency preparation,
successful direct readiness, single whole Lean submission, empty rebuild list
and passed preservation. It captures the **entire original AM probe root**,
including staging and the complete run evidence. This tree is included in both
new before/after snapshots, so any change in old evidence prevents success.

The D288/W58 accepted-supplier/fixed-pin route and the 6048/1218 artifact-slot
protection code are unchanged. The version-2 candidate still has no canonical
source installation and no normal/kernel acceptance. The new probe uses a fresh
publication's attempt; any existing attempt is held for inspection.

## New boundary checks and acceptance status

Seven local checks, limited to this repair, passed. They verify the exact
reversible 28-byte proof edit; refusal of statement/selector drift; the real
AM failed RESULT fingerprint and fields; full-AM-tree preservation; refusal to
relabel the failure as success or as the new source; and the stager's exact
new-source/probe pins. The fixture is the actual losslessly recovered AM RESULT.
No old test suite, old worker, Lean command or cloud command was executed.

The mathematical repair was independently reviewed as a split on the unchanged
Möbius-sign condition, followed by reflexivity in each remaining branch. The
corrected source still requires its own actual whole-source probe and later
independent normal/kernel/full-owned acceptance. The older formal draft remains
unbound and pins the superseded 9079-byte candidate; it must be revised and
bound to actual repaired-source evidence before use. P1.5 remains OPEN.
