# P2.1 five-root verification plan

**Status: pending.** This plan concerns the five roots and 26 named public theorems in [TARGETS.json](TARGETS.json), frozen against the commit named in `source_snapshot_commit`. Its 140 project modules include the roots. The plan grants no compile, replay, declaration or node acceptance.

## Select the two batches

Run the commands in Bash in the private P2 checkout **after** the normal compilation of the five roots is complete. For a published source repair, first refresh the batch manifest against the repaired commit and preserve the original manifest in Git history or its reconstructible digest and delta. An older manifest cannot validate new bytes. Keep the published source bytes, qualified native snapshots, original toolchain, Mathlib package paths and actual project `.olean` files available through export. Use the same inherited environment as the successful compile. A newer checkout can be used if every listed source still matches its manifest digest. Synchronize the published target manifest to the checkout before running these commands.

```bash
set -euo pipefail
cd /workspace/p2-1-20261125
plan_dir=docs/verification/20261125-p2-1
targets="$plan_dir/TARGETS.json"
registry=.lake/p2-private/records.json
mapfile -t roots < <(jq -r '.roots[].module' "$targets")
mapfile -t base_roots < <(jq -r '.roots[3].module as $b | .roots[] | select(.module != $b) | .module' "$targets")
mapfile -t first < <(jq -r '.roots[3].module as $b | .modules[] |
  select((.used_by_roots | index($b)) == null) | .module' "$targets")
mapfile -t buchstab < <(jq -r '.roots[3].module as $b | .modules[] |
  select((.used_by_roots | index($b)) != null) | .module' "$targets")
test "${#roots[@]}" -eq 5
test "${#base_roots[@]}" -eq 4
test "${#first[@]}" -eq 132
test "${#buchstab[@]}" -eq 8
jq -e '.roots[3].module as $b | all(.modules[]; (.used_by_roots | index($b)) == null
  or .used_by_roots == [$b])' "$targets" >/dev/null
jq -r '.modules[] | "\(.source_sha256)  \(.source)"' "$targets" | sha256sum --check --quiet
```

The four base-snapshot roots share 132 modules. Of these, 71 have native ancestry and 61 are project/standard-library modules without native ancestry. The eight project modules of the fourth root all depend on the Buchstab native extension and are disjoint from the base 132. Get the physical snapshot paths from the successful, source-bound compile records. The extension's final qualification must bind the SHA-256 of the 515-module parent.

```bash
base_snapshot=$(jq -er --arg n "${roots[0]}" '.[$n] | select(.exit_code == 0)
  | .external_snapshot | select((.native_modules | length) == 515) | .snapshot' "$registry")
extended_snapshot=$(jq -er --arg n "${roots[3]}" '.[$n] | select(.exit_code == 0)
  | .external_snapshot | select((.native_modules | length) == 518) | .snapshot' "$registry")
base_sha=$(sha256sum "$base_snapshot" | cut -d' ' -f1)
ext_sha=$(sha256sum "$extended_snapshot" | cut -d' ' -f1)
jq -e --arg parent "$base_sha" --arg combined "$ext_sha" --arg path "$extended_snapshot" '
  .status == "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED" and .parent_sha256 == $parent
  and .snapshot_sha256 == $combined and .verified_snapshot == $path' \
  "$(dirname "$extended_snapshot")/QUALIFICATION.json" >/dev/null
```

For a failed or incomplete normal compilation, use the already-qualified snapshot paths from the preceding compile setup. The four-root base producer command is `python verification/part2/run_winner9_private_checks.py --workers 1 --threads 1 --memory-mb 11264 --external-snapshot "$base_snapshot" "${base_roots[@]}"`. The Buchstab command uses the same options with `"$extended_snapshot" "${roots[3]}"`. The compiler traverses project imports and validates per-module source/object hashes, dependency signatures and the native snapshot before and after the batch. It can reuse valid prior records. Native qualification by itself supplies no project proof receipt.

## Replay and audit the defining modules

The audit driver replays **each positional module** with stock `leanchecker --verbose MODULE`, then audits that module's owned declarations. Giving it just the five root names would check the imported compilation closures but only enumerate five owners. Invoke it on both explicit module lists, serially in the same working tree. Smaller sequential batches with distinct summary basenames can be used when the remote job time limit requires checkpointing.

```bash
python verification/part2/run_winner9_private_audit.py --memory-mb 11264 \
  --summary-name p21-audit-515.json --external-snapshot "$base_snapshot" "${first[@]}"
python verification/part2/run_winner9_private_audit.py --memory-mb 11264 \
  --summary-name p21-audit-518.json --external-snapshot "$extended_snapshot" "${buchstab[@]}"
```

Require a current accepted receipt for each module. The driver checks the exact project modules actually loaded and equality of three inventories: the serialized `.olean` names, the Lean environment's module-owned names, and the complete declaration records. That includes private and generated declarations. Each record must have a complete type, safe, total, non-axiom status and transitive axioms contained in `propext`, `Classical.choice`, `Quot.sound`. Both replay and audit must exit zero with the input bindings unchanged. The 11,264 MiB option applies to the audit's Lean subprocess. The independent replay command has its own recorded invocation.

The [historical index](REUSED_EVIDENCE.json) supplies 27 matching source hashes. Of those, 23 historical inventories cover all owned declarations for their recorded scope. Four inventory only public declarations: `P2BuchstabRationalSemantics`, `P2HistoricLogPointInterpreter`, `P2HistoricLogRangeReduction` and `P2ContinuousSieveRational`. Source identity identifies a proof candidate; it cannot establish the identity of a newly produced object or its imported environment.

For full audit reuse, the current driver requires an earlier accepted receipt with the same input snapshot and intact hashed artifacts. This binds project sources and objects throughout the closure, toolchain, Lean and checker binaries, audit template/driver and, for native-dependent modules, the exact external snapshot. An earlier replay alone can be reused when its source/object/toolchain/checker/native context equals the current replay binding, the command matches, it exited zero with inputs unchanged and its actual log still has the recorded hash. The current owned audit must then succeed. The compiler separately validates the dependency object hashes and recursive closure signatures. Preserve the historical receipts as evidence for the scopes they actually covered. Never insert them as current registry records based on matching source bytes alone.

## Export and check the public claims

Run the existing exporter with all 140 modules in one call. It revalidates each selected receipt against its own external snapshot, so both snapshot files and their physical inputs must remain available. Include the declared batch scope and earlier evidence as supplemental records. The export command can exit zero after selecting a subset. Apply the following coverage checks to its actual on-disk manifest.

```bash
export_parent=$(mktemp -d)
export_dir="$export_parent/p21"
python verification/part2/export_winner9_private_evidence.py \
  --split group --output-dir "$export_dir" --extra-evidence "$targets" \
  --extra-evidence "$plan_dir/REUSED_EVIDENCE.json" \
  "${first[@]}" "${buchstab[@]}"
manifest="$export_dir/manifest.json"
jq -e --slurpfile t "$targets" '
  (.accepted_modules | keys) == ([$t[0].modules[].module] | sort) and
  (.object_manifest | keys) == (.accepted_modules | keys) and
  .accepted_module_count == 140 and (.unselected_modules | length) == 0 and
  (.duplicate_owned_declarations | length) == 0 and
  .owned_declaration_count == .unique_owned_declaration_count and
  ([.external_snapshots[].binding.native_modules | length] | sort) == [515,518] and
  (. as $m | all($t[0].modules[]; . as $row |
    $m.accepted_modules[$row.module].source_sha256 == $row.source_sha256))
' "$manifest" >/dev/null
```

Inspect the 26 named public theorems in the exported, selected declaration records. Match each full name exactly once **in its declared owner's inventory** and review its actual printed type against the root domain in the manifest. In this batch both `Block31FullCheck` and the other 39 `BlockNNFullCheck` owners must count, independently of their shared imports. For the named theorems, the following check reads only the selected export package and writes each audited type for that review.

```bash
python - "$targets" "$manifest" <<'PY'
import hashlib, json, sys, tarfile
from pathlib import Path
targets, manifest = (json.loads(Path(path).read_text()) for path in sys.argv[1:])
requested = {r["module"]: r["public_theorem_targets"] for r in targets["roots"]}
assert sum(map(len, requested.values())) == 26
for package in manifest["packages"]:
    archive = Path(package["path"])
    digest = hashlib.sha256()
    with archive.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    assert digest.hexdigest() == package["sha256"]
    relevant = set(package["modules"]) & set(requested)
    if relevant:
        with tarfile.open(archive, "r:gz") as tar:
            for owner in sorted(relevant):
                paths = manifest["accepted_modules"][owner]["artifact_paths"]
                (member,) = (p for p in paths if p.endswith("/declarations.json"))
                raw = tar.extractfile(member).read()
                assert hashlib.sha256(raw).hexdigest() == manifest["files"][member]["sha256"]
                rows = json.loads(raw)["declarations"]
                for name in requested.pop(owner):
                    (row,) = (r for r in rows if r["module"] == owner and r["name"] == name)
                    print(name, row["type"], sep="\n")
assert not requested
PY
```

Review exporter warnings, especially missing normal-compile logs, and distinguish reused baseline objects from fresh strict compilations in the final count. Rejected older candidate receipts remain diagnostics; a verified selected receipt is required for each module. Keep the export manifest, checksum-addressed packages and both qualified snapshot bindings. To transfer a slim archive, use `repack_winner9_private_evidence.py catalog --repo "$PWD" --output "$export_parent/catalog.json"`, then `repack "$export_dir" --manifest-sha256 "$(sha256sum "$manifest" | cut -d' ' -f1)" --catalog "$export_parent/catalog.json" --output "$export_parent/p21.tar.xz"` and `verify "$export_parent/p21.tar.xz" --repo "$PWD" --git-tree PUBLICATION_COMMIT --output "$export_parent/verification.json"` with the same Python script. Use the actual published Git revision for the last command. Slim archive verification checks byte preservation and availability of omitted identical sources in that Git tree.

## Import the accepted roots together

After the complete export above, run `python verification/part2/check_p21_joint_imports.py --export-manifest "$manifest" --memory-mb 11264`. It revalidates the 140 selected receipts under their original contexts, requires the extended snapshot to preserve the base entries, and imports the five roots together under the extended physical environment. The exact 26 public declarations and the loaded module/path union must match. Every resolved input's loadable facets must already be registered in its snapshot; all selected project bytes, receipts, records, runtime and search paths remain frozen before and after the probe. It writes an independent compatibility receipt and does not alter old ledgers or grant additional compilation, kernel or audit credit. Static review and four synthetic regression results are recorded in `JOINT_IMPORT_REVIEW.json`; the actual joint import remains pending until its remote receipt exists.

The fifth root, `ImbalancedChen.P2OriginalCompactQ80Table`, supplies the original compact Q80 `sf 16384 12` point-query enclosure. Its existing P2.4 source was adopted byte-for-byte. The named targets cover nodes, numerator interpolation, integer point queries and all rational inputs. The paired Q80 `maximum=8` and P112/P160 All40 results retain their separate scopes. An independent source intake also replaces the directed-log traversal used by the current closure. The historical gate failure concerns its earlier source digest. Both newly adopted sources require normal compilation, independent kernel replay and an audit of all owned declarations on their current input bindings. The provider supplies no acceptance for historical serialized arrays, cache realization, adaptive subdivision, leaf ordering, charges or totals. [Shared repair provenance](SHARED_REPAIR_REUSE.json) · [Compact provider provenance](COMPACT_PROVIDER_REUSE.json) · [Manuscript scope](MANUSCRIPT_SCOPE.md)

The current owned-audit template and joint-import probe explicitly import `Lean.Elab.Command` as well as `Lean.Util.CollectAxioms`, so their meta-programming API does not depend on a target importing Mathlib. The unchanged strict replay cache can reuse a completed stock replay across this audit-only template repair; the owned audit must match the new template digest. The old template and observations remain recoverable from the Git revision in [AUDIT_SUPPORT_REPAIR.json](AUDIT_SUPPORT_REPAIR.json).
