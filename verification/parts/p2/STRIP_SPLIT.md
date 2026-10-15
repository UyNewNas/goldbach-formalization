# P2 lossless strip-check split and balanced assembly

Verification level: **SOURCE_ONLY**. P0 is the sole execution and acceptance owner.
This is an independently authorized source increment, not a prerequisite claim
that the pending natural-sum request has passed. No Lean, Lake, checker, proof
environment audit, CI, commit or push was run by this producer or P2 worker.

## Frozen input and exact migration

Input commit: `541edd4d626a29bdb4bf7ff5dbef1e9d469057e6`.
Original `PairedV2StripCertificates.lean` SHA-256:
`1b1b9df07b02f151e82c25716df1c95ce9b9fc7f4d846afd4d91f1d6e854c402`.

The 186 original declarations `strip326_checked` through `strip511_checked`
are copied as byte slices, including their complete names, types, `decide +kernel`
proofs and original separating whitespace. Each leaf preserves the original
namespace and option context. The original public `strip_certificates_checked`
name and complete type are unchanged. Its old linear `fin_cases` proof is
recorded for historical reconstruction and replaced by a closed composition.

The complete map is in `strip-split-source-manifest.json`: old/new file and line
spans, independent declaration/type/proof SHA-256 values, original ordinal and
actual row count. For every strip k, the new leaf is Block floor((k-326)/16);
the original declaration starts at line 11 + 4*(k-326). Blocks00–10 hold16 strips;
Block11 holds10. Group ranges and row counts are:

| Block | Original strips | Original Fin186 ordinals | Rows |
|---|---|---|---:|
|00|326–341|0–15|129|
|01|342–357|16–31|377|
|02|358–373|32–47|636|
|03|374–389|48–63|904|
|04|390–405|64–79|1160|
|05|406–421|80–95|1416|
|06|422–437|96–111|1686|
|07|438–453|112–127|1946|
|08|454–469|128–143|2217|
|09|470–485|144–159|2484|
|10|486–501|160–175|2757|
|11|502–511|176–185|1860|

All17,572 canonical grid pairs occur exactly once: E0=6,091 and E1=11,481.
Original `Row`, `firstU`, `indices`, `approximation`, `makeCertificate`, all data
values, the logarithm scale10^15 and endpoint denominator10^20 are unchanged.
The43 existing generated sum/data/bridge sources are byte-for-byte frozen at
the input commit. Their individual acceptance levels are not upgraded here.

## Balanced proof-side composition

The only new shared source is `PairedV2StripCertificatesAssemblyCore.lean`.
It defines `StripAssembly.StripChecked i` as the complete original ∀j check
proposition, a generic `joinChecked` proved using `Fin.addCases`, and twelve
proof-side embeddings. These embeddings compose `Fin.castAdd` and `Fin.natAdd`
exactly along their ancestors. They are not replacement data selectors.

The tree is 186=96+90, 96=48+48, 90=48+42, each48=16+32, each32=16+16,
42=16+26, and26=16+10. It has12 leaves and11 binary nodes; depth is at most4.
Each leaf appends one closed `stripBlockNN_checked` proof. It performs
`fin_cases` only on a local Fin16 (or Fin10), then references every corresponding
original `stripNN_checked` without re-running a new checker. It does not first
introduce a dependent j and enumerate the global Fin186.

The original entry file contains11 named binary compositions, ending with
`allStrips_checked : ∀ i : Fin186, StripAssembly.StripChecked i`. Its public
original theorem simply applies this result to i and j. The generic composition
lemma's left/right inputs are supplied by closed child proofs all the way to the
186 original checks; no checked hypothesis remains in the public result.

This construction is an actual Lean proof candidate. The Python ordinal map
is only a static consistency check and does not establish theorem validity.
Closed-index definitional equality, elaboration, strict lint, resource use and
full kernel/object acceptance remain untested by this worker.

## Dependencies and the old receipt

Every check leaf imports AssemblyCore, which imports the actual
`PairedV2FullCertificateData`. Preserving the original statement bytes therefore
requires all twelve data leaves in the shared object closure. Check leaves are
independent of one another and of NaturalSums; this is not a one-data-leaf
optimization. The source-only graph in `strip-split-dependencies.json` records
all project source hashes, direct imports, pinned external frontier and each
leaf's full project source closure. Exact transitive object binding is unpaid.

The old strip-module receipt records -t0 compilation in2762.087 seconds with
`warnings_as_errors=false`, no full replay or complete audit. Its source hash
matches the frozen original; its recorded object depended on the old monolithic
FullData object. The historical record is preserved, not promoted to current
acceptance or a reusable new-object claim.

## Joint protection and deterministic reproduction

```text
python3 verification/parts/p2/split_paired_v2_strip_certificates.py --check
python3 verification/parts/p2/split_paired_v2_certificate_data.py --check
```

Without `--check`, the first producer emits exactly14 authorized Lean files and
two strip reports. The existing data/sum producer still emits the same43 Lean
files unchanged. Its original StripCertificates protection is migrated, not
removed: it calls the new producer's read-only joint verifier with the exact
original Git bytes. That verifier independently compares all186 current leaf
declarations, reconstructs the entire original source including the historical
aggregate, and demands byte equality of every generated core/leaf/entry source.
The old report's `unchanged_files` now truthfully lists the other8 protected
inputs; `strip_certificate_joint_protection` records the stronger split-specific
check and every exact generated source hash.

The producer obtains the frozen43 source hashes from the input commit's
manifest and compares both hash and original Git bytes. A modified declaration,
statement, composition, frozen source, pin or data input is rejected. This
explicit check has no dependency on a possibly edited current generated report.

The legacy `verification/parts/takeover-p2/generate_strip_proofs.py` is outside
this ownership and remains unchanged as historical provenance. It regenerates
the original monolithic layout and must not be run over this split candidate.
Do not use the historical natural-sum producer for the split layout either.

## P0 execution order and complete gates

After independent source review and P0 selection: first AssemblyCore, then
Block00 (129 rows and the complete moved-proof/local-embedding shape), then
Block11 (includes the longest191-row strip) and Block10 (largest2,757-row group).
Only after those actual diagnostics are resolved, run the remaining Block01–09
in small separate requests and finally the entry. Do not pack all twelve check
leaves into a single 65-minute CI batch. Each leaf needs its own complete strict
compile/replay/audit evidence; the old monolithic timing is not a new estimate.
No accepted natural-sum/data leaves are repeated as targets;
exact prerequisite reuse is exclusively governed by P0's object-binding rules.

Maintain one heavy process, -t0/-j2/-M4096, warnings-as-errors, ordinary kernel
proof checking, same-object replay, complete defining-module type/inventory,
private/generated declaration coverage, transitive axiom/import-object binding
and audit replay. Source declaration counts are not compiler inventories.
Stop at the first real failure; do not raise limits, bypass trust, change pins,
change data or restart the unchanged old monolithic checker in parallel.

Even success here would establish only actual adopted-row checks. It would not
prove a new full-integral theorem, full budgets, common policy, hLower/hUpper or
the unconditional main theorem. Those obligations remain separate.

Fixed API sources:
- [Fin.addCases](https://github.com/leanprover/lean4/blob/v4.33.0-rc1/src/Init/Data/Fin/Lemmas.lean#L1055-L1079)
- [FinCases implementation](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Tactic/FinCases.lean#L54-L76)
