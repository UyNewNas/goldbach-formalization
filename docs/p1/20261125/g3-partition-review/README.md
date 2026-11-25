# G3 Data source partition candidate

**Source-only candidates: 24 flat data units and the existing Data facade.** Root authorized this mechanical partition after the actual normal timeout and missing completion evidence. The 24 new providers and one changed facade are materialized locally. No compiler driver, Reader, Archive, BoxIntegral, fixture or output was changed. No new source has been compiled or audited.

[PARTITION_PLAN.json](PARTITION_PLAN.json) records the exact construction and grouping. [SOURCE_PARTITION.json](SOURCE_PARTITION.json) binds all 25 candidate sources, their pre/post hashes, ownership of 109 original source declarations and the 188 exact fixture paths, sizes, hashes and original archive locators. [MONOLITH_FAILURE.json](MONOLITH_FAILURE.json) binds the observed timeout, preserved normal log and exact snapshot. These are source and observation records, not compiled objects or acceptance receipts.

## Actual reason for partitioning

Task job_9a4760aaa4e9410b9faf39d9fcf1efdf timed_out, exit -9, runtime 3600.075420618 seconds, with reported task peak 8,367,046,656 bytes. The preserved [monolith-normal.log](monolith-normal.log) is 153,991 bytes, 1999 lines, SHA256 64c2affbdbac7c6a6fddc1e89462b543dbb715ac7757b3bc07872d2b4a5736d7. It contains old dependency warnings and no Data target error or Built line. Reader's direct no-build check exited 0; Data's no-build check exited 3. The normal command started but left no normal-command completion, NORMAL_PASS or fixture-bound companion.

This establishes the one-hour task limit. It does not establish a Lean proof error, OOM or defective tree shape. The task peak is not a measurement of the guard or individual Lean process.

Exact metadata task job_c0ad57efd255463bb52196f661c9570f used the frozen snapshot definition: source plus .olean, .ilean, IR/.c, IR/.setup.json and .trace. The cloud source remained the original 5fc51f... hash. The .olean, .ilean, .c and .trace files were absent. Only .setup.json remained: **6,334,162 bytes**, SHA256 **02b7248c74edcbf9a293e9ebc65b9a7f16a90b3ebf8bc0e25a6213d81a7c2d83**. Preserve that existing file; its presence is not a normal success. The exact record is ../batch13-accepted-evidence/G3_EXACT_FACETS.json, SHA256 d6063b581259ce08e394493e44e52ed821239b4cd5f3efaf331638f62dc319a9.

An earlier probe checked two auxiliary .olean names instead of the two IR paths, so it did not establish that all five required artifacts were absent. The exact metadata supersedes that incomplete inventory. No large setup payload is copied here.

## Existing sources and path semantics

The four input-source snapshots were checked against the original pilot's exact source commit 220c14630ffd266f824bdbf0977147ecb740c0dd before materialization. Reader, Archive and BoxIntegral still match it byte-for-byte. Reader SHA256 is 59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6; Data is 5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4; Archive is 886986042a8cf148355d109420f8d844328f477c3c5a3898178707da2d1213cb. All full pins, including BoxIntegral, are in the plan. The changed Data facade is now SHA256 5337ba076aa55ad3661f73c430cc6fc22ebc6d79f427fa98e3893a94dd63ce24.

The existing g3-reuse/G3_REUSE_INVENTORY.json remains authoritative for the 188 file sizes and hashes (inventory SHA256 c89fd6388cfb269ebe74bad97e62454a8ad36fc317d7e5685253f4c13785047e). This review reuses its metadata; no fixture was downloaded, extracted, read or rehashed. Counts match the original count arrays and registered pair sizes: 43,236 C rows plus 1,720,184 F rows, 423,244,864 raw bytes.

The elaborator resolves each include path using the current source filename's parent and FilePath.withFileName, then reads the pair with IO.FS.readBinFile. Every new unit stays directly under ImbalancedChen/. The original literal g3-fixtures/Cxxxx-cells.npy and floors.npy strings therefore continue to resolve to exactly the existing ImbalancedChen/g3-fixtures/ files. Moving a unit into a nested Data/ directory would change that relationship and is excluded.

Reader is already balanced: it creates one Words.leaf per row, repeatedly pairs adjacent entries into Words.branch, and carries an odd final entry. The total is 1,763,420 leaves, 1,763,347 branches and 21 empty-block nodes. F0020's 133,348 leaves have maximum branch depth18. No Reader implementation change is proposed. Its source, five accepted artifacts and67-module dependency closure must be revalidated, without repeating accepted Reader proof work.

## Deterministic groups

Walk the original C and F orders separately. Add whole original blocks while an ordinary group's row total remains at most65,536. An original block above that value becomes a singleton. No block is subdivided and no row is reindexed. The cap is a static work-unit heuristic, not a measured time or memory guarantee.

| Unit | Original block range | Blocks | Raw rows | Single block above cap |
| --- | --- | ---: | ---: | --- |
| 1 | C0000ToC0046 | 47 | 43,236 | no |
| 2 | F0000ToF0007 | 8 | 58,403 | no |
| 3 | F0008 | 1 | 63,426 | no |
| 4 | F0009ToF0010 | 2 | 56,860 | no |
| 5 | F0011 | 1 | 70,141 | yes |
| 6 | F0012 | 1 | 29,559 | no |
| 7 | F0013 | 1 | 102,264 | yes |
| 8 | F0014 | 1 | 29,877 | no |
| 9 | F0015 | 1 | 84,084 | yes |
| 10 | F0016 | 1 | 79,098 | yes |
| 11 | F0017 | 1 | 79,849 | yes |
| 12 | F0018 | 1 | 123,876 | yes |
| 13 | F0019 | 1 | 57,974 | no |
| 14 | F0020 | 1 | 133,348 | yes |
| 15 | F0021 | 1 | 63,069 | no |
| 16 | F0022 | 1 | 130,287 | yes |
| 17 | F0023 | 1 | 100,454 | yes |
| 18 | F0024 | 1 | 89,594 | yes |
| 19 | F0025 | 1 | 93,107 | yes |
| 20 | F0026 | 1 | 31,277 | no |
| 21 | F0027 | 1 | 76,784 | yes |
| 22 | F0028ToF0029 | 2 | 58,733 | no |
| 23 | F0030ToF0031 | 2 | 62,659 | no |
| 24 | F0032ToF0046 | 15 | 45,461 | no |

For a range XToY, the module is ImbalancedChen.P4AOriginalNewFifthArchiveDataXToY; a singleton uses its one block identifier. All 24 exact module/path names and actual candidate source hashes appear in the manifest.

Each unit imports only the unchanged Reader, opens the same Reader namespace, and declares its exact original lines in namespace ImbalancedChen.P4AOriginalNewFifthArchiveData. In particular C0000 through C0046 and F0000 through F0046 keep their fully qualified declaration names and original macro arguments. These 24 units are the only new canonical Lean files.

## Existing Data facade and API

The facade remains ImbalancedChen/P4AOriginalNewFifthArchiveData.lean. The recipe removes exactly the94 original include-definition lines, inserts24 imports after its existing Reader import, and preserves every other original byte. No aliases or new arrays are introduced. The bankC/countC/floorC and bankF/countF/floorF expressions retain their original47 entries and order. BlockIndex, block, count, floorSum, grid, Position, packed, rawRow and floorNumerator retain the exact original expressions.

Position remains the dependent type over the original block's Words.list length. Coarse/fine grids remain400/800. The floor total remains1648717268323516459667 with denominator2^80. The BoxIntegral fractionBound keeps four lower and five upper odd logarithm terms; the independent six/seven-term replay cannot replace the original saved-floor contract.

There are109 original source declarations:94 block definitions move to the new owners and15 facade definitions/abbreviations stay. This source count is not an owned-declaration audit count: Lean-generated declarations must be enumerated from actual compiled environments.

## Archive and aggregate contract

The current Archive is one file containing94 Checked theorem declarations, not94 existing modules. Its Geometry, CheckRow, Checked definitions and instances, all bodyC/bodyF proofs, and all aggregate proofs remain byte-identical in this first plan. Its public API includes all_blocks, position_checks, geometry, facts, row_grid, block_floor_sum, exact_counts, original_block_totals, original_sum_Q80, literalIntegral and original_floor_le_full_sum.

The aggregate conclusion still compares the exact original Q80 floor total with the sum of physical-coordinate literalIntegral over every Position. Nothing in successful Data elaboration alone proves the row geometry, saved-floor arithmetic,94 Checked statements or that integral conclusion. Archive may later reveal its own runtime limit; it has not been run successfully or failed on this partition. No Archive split or proof rewrite is proposed now.

## Gates before publication and execution

1. Root reviews the materialized sources and publishes the manifest at a new source commit. Preserve the monolith's failed logs and existing setup file. Keep the historical 220-bound pilot and receipts unchanged.
2. Before any cloud source write, preflight the entire batch: the facade must match its old preimage or exact new postimage; all 24 new paths must be absent or exact postimages. Reject symlinks, nonregular files and unknown bytes. Verify all 188 fixtures and accepted Reader bindings, back up the old facade and preserve dirty Git state.
3. Use the existing serializer and unchanged lane-0 guard. First pilot C0000ToC0046, then F0020 in its own task. These are independent Reader-only units. After actual measurements, process the remaining units individually in original order. Build the facade only when all direct units are ready. Never launch a cold fan-out through the facade.
4. Save each normal success before moving on. Bind the new source commit, source and exact five outputs, dependency objects/traces/configuration/runtime, complete command log and actual Built set. Bind each unit's immutable fixture subset before and after its command. Reuse fully validated successes; hold ready outputs with missing provenance or partial audits for inspection.
5. Use unchanged e9 kernel/full-owned acceptance for populated selected owners. The complete Data union is 24 providers plus the facade: **25 owners**. Validate all 24 fixture companions and the complete 188-file inventory for the facade. Auditing the facade alone cannot accept constants owned by the providers. The already accepted Reader is revalidated, not re-audited.

The source-parameterized context/normal/audit utilities in batch13-repairs/run_repairs.py and the fixture-companion design in g3-data-pilot/run_pilot.py are existing components for a later bounded caller. Their fixed CLIs do not accept this partition. Do not alter historical source commits or target sets; bind a new published manifest and explicit source commit. This change creates no compiler caller and changes no guard, e9 template, heartbeat, memory or thread option.

## Resource and proof boundary

Each unit requires fresh literal elaboration only for its assigned original blocks and permits a durable checkpoint after completion. F0020 remains a large original block and may still exceed the task limit. The facade imports all 24 artifacts; import/deserialization, Archive proofs, kernel replay and owned-declaration auditing may still require all data resident. No peak-memory or total-runtime improvement is guaranteed.

The Reader already constructs a balanced tree. This change partitions compilation units; it does not fix a linear-tree implementation. Existing normal success, independent kernel replay and full-owned acceptance remain separate gates. Even the complete 25-owner Data union does not finish the 94 Checked proofs, G3's integral conclusion or P1.

## Local verification

Before changing canonical files, the read-only checks produced three expected failures: providers absent, monolithic definitions still in the facade, and source manifest absent. The unchanged-source check passed. After materialization all **4 checks pass**. They compare every original include line and namespace, restore the entire original nonliteral byte stream after removing new imports, bind all 25 actual source hashes and 188 fixture records, and compare Reader/Archive/BoxIntegral byte-for-byte with the original commit.

    python3 -B docs/p1/20261125/g3-partition-review/test_partition.py

LOCAL_VERIFICATION.json preserves the RED/GREEN output and candidate pins. These are static byte/provenance checks, not Lean proof evidence. The project Lean build and acceptance suite were not run because root owns compiler execution. No Lean, Lake, kernel, audit, cloud job or fixture I/O was executed by this implementation.
