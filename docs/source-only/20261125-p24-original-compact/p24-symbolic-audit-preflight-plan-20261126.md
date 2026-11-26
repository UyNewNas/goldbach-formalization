# P2.4 symbolic audit preflight while finite A remains open

This changes execution order only. The original 321 symbolic modules have passed at source pin `909214bbfb5ca9caa74fcc1b6f95b469bf43e125`; A, B and W remain unaccepted. The full scope stays at 324 with ordered fingerprint `c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.

The unchanged exporter selects valid historical receipts independently for each requested module. A target with no valid receipt is listed in `unselected_modules`; it does not prevent a partial manifest. The unchanged audit runner freezes and checks the source/object/dependency/native closure of its target, rather than requiring the whole project HEAD or the finite endpoints to be accepted. Therefore symbolic audit receipts can remain valid after later changes confined to A/B/W, provided each audited closure and all toolchain/template/native bindings remain unchanged.

## Execution

1. Under the existing P2 lock, require the exact source pin and clean tracked state; verify the original checker, audit driver, exporter and audit-template hashes.
2. Generate the full ordered 324-module list through the original `project_nodes` function and verify its fingerprint. Independently regenerate the accepted 321-symbolic set from the five original roots and assert that the set difference consists exactly of A, B and W.
3. Invoke the unchanged exporter with all 324 explicit modules, `--split all`, and a fresh `.lake/p24-audit-export/symbolic-preflight-001` directory. Do not add unsupported arguments or change historical driver selection.
4. Preserve the actual manifest and selected receipt set. Assert no duplicate owned declarations and that every reported module belongs to the requested full scope. An exit-zero partial export does not mean P2.4 is complete.
5. Form the next audit list as `unselected_modules` intersected with the 321 accepted symbolic modules, in original dependency order. Do not audit already selected valid historical receipts again.
6. Run only missing symbolic targets with the unchanged audit runner and existing qualified external snapshot. Save each actual receipt. Keep all proof, native, safety, axiom, complete-inventory and full-type requirements unchanged.
7. After A/B/W pass their original gates, select and audit the remaining finite/whole modules and perform the final full 324-module export. Require complete accepted coverage, no unselected entries and no duplicate owned declarations. Preserve the exporter's separate `full_p2_complete: false` boundary.

No template change is authorized by this ordering adjustment. Any actual audit failure must be diagnosed before changing implementation. The preflight only writes its new evidence directory and must preserve the compile registry and tracked sources.

## Actual preflight outcome

Task `31d2dbedc14d4731a3213ed93041ad09` completed successfully: 0 selected, 324 unselected, 321 eligible missing symbolic modules, no duplicate owned declarations, and unchanged compile registry. Manifest SHA256 `43b5f8366283883a81766b6ccb16f9f2c12dc70d59f54bc5f26b9a18e42428c1`. The next batch uses the original runner for the first ten eligible modules. See [actual checkpoint](p24-memory-and-audit-checkpoint-20261126.md).
