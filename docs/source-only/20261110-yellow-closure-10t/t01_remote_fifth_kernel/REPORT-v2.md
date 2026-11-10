# T01 v2: one pinned Mathlib import-path repair

Status: concrete repair candidate for T10 independent review and root retry. No new target compilation, kernel result or green claim. The published v1 packet remains byte-identical.

The first actual remote run42738653705, job129574001335, at published commit`f4b63655412159566c6a3e9088cf390bf8eebedc` ended in FAILURE. Original-binary materialization, toolchain installation and the unchanged12GiB guard succeeded. The dependency cache downloaded and decompressed all8679 requested Mathlib files. `record_dependencies.py` then failed because `Mathlib.Data.Matrix.Notation` had zero source matches in the pinned packages. Target build, theorem-type exports and kernel replay were SKIPPED. This was a source-inventory failure, not a timeout or proof result. The exact failed-log hash and outcomes are recorded in `repairs/FAILED_RUN_42738653705.json`.

Root cause: the one selected caller `ImbalancedChen.P2OriginalThirdMinorantLogDictionary`, original public path`ImbalancedChen/P2OriginalThirdMinorantLogDictionary.lean`, uses the absent import at line3. The pinned Mathlib revision`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` instead has the canonical module `Mathlib.LinearAlgebra.Matrix.Notation`. Its Git blob is`0508d8071067df2d1a5c168f9a4a09e7c0e23e3e`, raw SHA256`0a5b11bff151565fa33a4b7faf0e20d4bf2d27075f98f88a0a9e9e25b40e2940`. It publicly imports `Mathlib.Data.Fin.VecNotation`, which supplies the caller's vector notation and `Matrix.cons_val_zero`/`Matrix.cons_val_succ`. The actual pinned source was read; no shim, extra theorem or new dependency version is needed.

The repair changes exactly one line:

```diff
-import Mathlib.Data.Matrix.Notation
+import Mathlib.LinearAlgebra.Matrix.Notation
```

The repaired copy is `repairs/P2OriginalThirdMinorantLogDictionary.lean`, SHA256`9ed28a91a6578b2db6f752764487c79c4b305805c6de1ae691fe66bedf6f3af8`, Git blob`7c84653732c217b6b455a49f1fb10cfc2e95a0dc`. All bytes after the initial four import lines are identical to the original source; every definition, theorem, hypothesis, proof body and constant is unchanged. The other728 selected project source hashes are unchanged. Every one of the15 frozen S25-reviewed primary proof sources keeps its original published124d09f SHA256 and original source path. Thus this repair does not supersede or alter their mathematical review.

The full direct-import inventory was checked before preparing the retry. Nontruncated pinned Git trees contain8839 Mathlib Lean files,7390 native Goldbach Lean files and6905 Lean-toolchain Lean files. Across all144 v1 proof external imports plus the separate audit import, the stale Matrix path is the only missing source and there are no ambiguous matches. Replacing it by the canonical current path leaves144 distinct proof external imports; every resulting145 proof/audit source module resolves uniquely. `repairs/EXTERNAL_IMPORT_CENSUS-v2.json` records both the original and repaired complete145-module inventories, including source paths and Git blobs. T10 independently reached the same path/API diagnosis and exact repaired-source SHA.

`EXACT_INSTALL_MANIFEST-v2.json` selects the repaired inherited caller while reusing the existing172 bundled source files and every unchanged public source. It retains729 project modules, the original raw binary/path/pins, the15 primary proof hashes, the eight S25 declarations and the same toolchain/Mathlib/native revisions. The new source-identity hash is`f8c2b8a82adc7f4b2a5dbd23df56824cb9a9838cd557a38f7d9495aedf348f21`. It no longer makes the v1 claim that every source hash is unchanged.

`stage_project_v2.py` is the v1 materializer with only its manifest filename changed to the v2 manifest. The dependency-source gate is retained unchanged; absent or ambiguous imports still fail. `t01-fifth-kernel-v2.yml` keeps every mathematical acceptance gate: full selected build, separate raw eight-declaration pp.all/readable type export, allowed-transitive-axiom checks, explicit730-module replay, same-source/object hashes before and after replay, runtime audit and evidence retention. Its changes are the v2 name, manifest filename/hash and materializer filename. No gate was skipped or weakened.

Root should add the exact new files listed in `REGISTRY-v2.json` on the existing publication branch and replace only `.github/workflows/t01-fifth-kernel.yml` with the bytes of `t01-fifth-kernel-v2.yml`. The existing v1 packet and its172 payload files remain installed and frozen. The large local `repairs/PINNED_EXTERNAL_TREES.json` and pinned reference text are read-only investigation evidence and are not required for this minimal publication; the complete relevant145-entry census is included. Root alone publishes or triggers the retry, after T10 review of the exact candidate pins.

Manifest-v2 SHA256:`ab3a852493e4f49ed056a9d815f245bafbf58800234bc96bffb83f2472d25a75`.

Workflow-v2 SHA256:`cd12d74ee323f79a9a7ac233facf43aef99e66fceb140005b576e8a500a2db65`.

Local checks were source/byte/Git-tree/AST/YAML inspection only. No Lean, Lake, LSP, guard, finite body, numerical producer/replay, version probe, test harness, Git mutation, remote mutation or quota call was performed locally. The actual failed remote run supplies the failing observation; the repaired candidate remains UNCOMPILED. A successful root retry and independent acceptance of its exact expanded terminal types are still required for this assigned fifth-integral scope. Broader P1.4 authenticity/full87/history obligations remain open.
