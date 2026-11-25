# Saving19 Parse00 v3: success-tag proof of the unchanged goals

## Scope and status

The two public statements remain exactly:

```lean
theorem geometry_parse_00 :
    geometryParse (0 : Fin 13) = .ok (geometry 0)

theorem moment_parse_00 :
    momentParse (0 : Fin 13) = .ok (moments 0)
```

The candidate only changes their proof representation and adds three private
declarations. It imports the existing ArchiveCore alone. It changes no loader,
string, decoder, field, record, default, Q80/Q96 value, or definition in Core.
Neither the real archive candidate nor its closed guards has been compiled or
evaluated locally. `archive_complete=false` and `only_cell00_proved=false`.

Root reported that job `job_36f736b122a8476ba8566218264d0074` fully accepted
ArchiveCore v2, then the old Parse00 normal hit `memory_exceeded` under a 16,384 MB
cap, with peak 17,183,985,664 bytes. Reported total job duration was 323.67 seconds.
That failure does not establish whether parsing, payload equality, or elaborator
reduction accounted for most of the memory. This candidate tests a narrower
computational obligation without changing either theorem.

## Exact proof mechanism

The generic lemma, with an arbitrary fallback and no equality instances, is:

```lean
theorem eq_ok_getD_of_toOption_isSome {ε : Type u} {α : Type v}
    (p : Except ε α) (fallback : α) (h : p.toOption.isSome = true) :
    p = .ok (p.toOption.getD fallback) := by
  cases p with
  | error e => cases h
  | ok a => rfl
```

It is proved by constructor elimination. In the error case the Boolean hypothesis
reduces to `false = true`; in the successful case both sides are the same
constructor containing the same value. It needs neither `DecidableEq ε` nor
`DecidableEq α`. In the actual candidate it is private and used with the existing
`Geometry`/`Moments` defaults.

Two private closed guards prove
`(geometryParse 0).toOption.isSome = true` and
`(momentParse 0).toOption.isSome = true`, using **`by decide +kernel`**.
The public statements apply the generic lemma to those proved guards. The
definitions of `geometry` and `moments` are exactly the lemma's `getD` expression.
No success assumption or external check result is supplied.

This follows an existing repository pattern, rather than proposing a different
archive meaning: `P2OriginalSaving16OriginalArchive.lean` defines
`parsedCellSuccess`, proves `original_parse_success_tag`, and recovers
`original_parse_success` by eliminating the `Except` constructor. Its comments
explicitly distinguish eliminating payload equality from avoiding the parser.
Similar local patterns exist for other saving archives. No fresh claim about
those modules' acceptance is made here.

## What is actually avoided

The checked Lean runtime defines `Except.toOption` by inspecting only the
`Except` constructor, and `Option.isSome` by inspecting only the option
constructor. The corresponding branches discard the payload. The recovery
lemma likewise never traverses or compares it.

The old goal used `decide` on an equality of `Except String Geometry` or
`Except String Moments`. Batteries' `Batteries/Lean/Except.lean` derives
`DecidableEq` for `Except`; the archive records also derive decidable equality,
and their fields include arrays of rational records. The new Boolean guard
does not request the final whole-record equality decision. It can also avoid
forcing rational arithmetic that is only needed to compare returned payloads.

The `+kernel` option has a separate benefit. In the pinned
`Lean/Elab/Tactic/Decide.lean`, ordinary `decide` first performs elaborator
weak-head reduction of the decidable instance and then returns a compact proof
that the kernel checks again. The `+kernel` branch passes that proof to
`mkAuxLemma` and uses its checked/cached lemma. It is distinct from the native
evaluation branch. The candidate uses no native evaluation or new axiom.

## What is still required

The exact same `geometryParse` and `momentParse` computations must reduce far
enough to expose their final `Except` constructors. `SourceJson.parse` still
reads the complete selected string, checks its trailing input, and constructs
the JSON result. Its array/object parsing and the decoder's `mapM` traversals
must still establish that every required field and element decodes successfully.
Rational denominators must still parse and pass the original nonzero test.

The candidate is not a parser cache or a textual shortcut. It does not prove that
the real parse will fit within 16 GB. Kernel replay remains a separate required
check and may itself repeat reduction of each closed guard. The change removes
the final payload-equality decision and the ordinary-decide elaborator pass; it
does not justify a literal promise of one parse across all compilation and
verification stages. Actual P1 resource measurement remains necessary.

## Independent local validation performed

The diagnostic uses the existing Lean 4.33.0-rc1 runtime
`62eed1db4d67327ec8120be05f1a1b0847d74561` and exact Mathlib commit
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. It compiles only a generic helper and
a small independent probe. It imports no project Core and loads no original
fixture. All output files are under this candidate directory; P34 caches are
read-only inputs.

Successful current-source results:

| Module | Normal compile | Independent leanchecker |
| --- | ---: | ---: |
| `P2OriginalSaving19ExceptSuccess` | exit 0, 0.867 s | exit 0, 1.625 s |
| `diagnostic.ExceptSuccessProbe` | exit 0, 0.917 s | exit 0, 1.419 s |

The probe includes a payload containing a function, with no decidable equality
instance, and a closed `decide +kernel` tag guard. The generic recovery and
same-shape wrapper goals pass. All printed axioms lists are empty. Failure cases
of `Except` are also checked to have a false success tag.

Two diagnostic mistakes are retained in the evidence: the first leanchecker
invocation could not find `lean` in PATH, and an initial probe tried `+kernel`
with a free local function variable. The PATH was corrected without recompiling
the already successful generic helper; the probe now separates generic `rfl`
checks from its closed `+kernel` guard. Failed logs are not acceptance evidence.

Complete local command/source/object/log records are in `local/DIAGNOSTIC.json`.
This is not P1 acceptance and not proof of either real archive success guard.

## Strict P1 runner and reuse boundary

`run_archive_diagnostic_v3.py` selects only the new Parse00 owner. Its source and
manifest come from a new explicit source commit under
`docs/verification/20261125-p26/archive-v3/`.

All **219 project dependencies** stay bound to the accepted commit
`508d757913ea9c536c0d4f95abb35c090b940a29`. Core comes from that commit's
`docs/verification/20261125-p26/archive-v2/ImbalancedChen/` path; the other
dependencies come from their normal production paths. Every source has an
explicit commit/path origin. The new commit is identified only as the selected
Parse00 owner's provenance, never as the entire project dependency tree.

The runner loads the old v2 driver at its fixed SHA
`fdfcb29fd4c2a40c5b9566979b96df2abd322634a9676b8556f8034941a35a56` and reuses its
unchanged Core validator. The old Core binding, frozen driver, normal evidence,
full audit, successful wrapper result, and all 26 actual input snapshots must
still match. `normal_valid` and `audit_valid` receive **the old commit** for Core.
No Core normal or audit command is rerun. The new Parse00 owner uses unchanged
Batch13 normal/kernel/full-owned acceptance, serializer, guards and runtime
configuration review.

Only Root may back up and replace the known failed Parse00 source
`8550c64fea8f8716042df6509d9cdb29b93a77eb3fd74ca212398b9ce3cb430d`.
The runner accepts an absent target or exact new bytes only; it cannot perform
an arbitrary replacement. Production Archive remains at `f48ba6e6...` and Core
at `df9c1855...`. The v2 evidence is never rewritten or relabelled.

The independent v3 evidence root is
`/workspace/p1-complete-proof/20261125-p26-archive-diagnostic-v3/`.
Even on complete success, the result still reports `archive_complete=false` and
only the two original cell-00 parse statements are credited.
