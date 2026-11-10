# T01 v2 import repair review

**PASS for the exact v2 publication and fresh remote run.** Remote run 42738653705 on f4b6365 failed during direct dependency-source identification, after successful materialization and toolchain setup. It supplied no fifth proof build, eight-type receipt or kernel replay.

| v2 input | SHA256 |
| --- | --- |
| EXACT_INSTALL_MANIFEST-v2.json | `ab3a852493e4f49ed056a9d815f245bafbf58800234bc96bffb83f2472d25a75` |
| t01-fifth-kernel-v2.yml, published at the same single CI workflow path | `cd12d74ee323f79a9a7ac233facf43aef99e66fceb140005b576e8a500a2db65` |
| stage_project_v2.py | `95f7d6f027bb90cb08aaab4804d75275cf4cb805e041ad600e15c508335d344a` |
| repaired P2OriginalThirdMinorantLogDictionary.lean | `9ed28a91a6578b2db6f752764487c79c4b305805c6de1ae691fe66bedf6f3af8` |
| v2 target source identity | `f8c2b8a82adc7f4b2a5dbd23df56824cb9a9838cd557a38f7d9495aedf348f21` |

I compared the bytes against the public f4b6365 Git object. Only line 3 of the one selected inherited source changes, replacing `import Mathlib.Data.Matrix.Notation` with `import Mathlib.LinearAlgebra.Matrix.Notation`. Original SHA256 `6bcaeb8d4f3e24f3422ba52cec424d0cbae84a6801e5b5cb37992652dcf38230`, repaired Git blob `7c84653732c217b6b455a49f1fb10cfc2e95a0dc`, 14,897 bytes. All declarations, hypotheses and proof bodies in the file are byte-identical. The other 728 module records are identical. The repaired file is outside the 15 S25 primaries.

I independently queried the complete pinned Git trees of Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native goldbach `09b97db5764ade1246bfb77206baa1b124760958` and Lean v4.33.0-rc1 (`62eed1db4d67327ec8120be05f1a1b0847d74561`). Among the 145 distinct v1 selected-plus-audit names, these trees resolve 116 to Mathlib, 24 to native and four to Lean. Exactly the obsolete Matrix.Notation name was absent. The replacement is the genuine Mathlib module, blob `0508d8071067df2d1a5c168f9a4a09e7c0e23e3e`, SHA256 `0a5b11bff151565fa33a4b7faf0e20d4bf2d27075f98f88a0a9e9e25b40e2940`. It publicly imports Mathlib.Data.Fin.VecNotation, SHA256 `17b85a7ee9c4478995b91d56eda4115ac0b399ea676e1d29ba50485803d4b34e`, which supplies all the caller's uses: vector notation at line 70 and Matrix.cons_val_zero / cons_val_succ at lines 126 / 133. The v2 replacement makes all 145 direct names resolvable among those source trees. The remote provenance stage must still verify the actual checked-out packages and runtime.

The 729 project names, binary, 15 reviewed primaries, eight allowed target signatures, axiom gate, 730 project-plus-audit kernel replays, runtime guard and dependency revisions are unchanged. The v2 manifest switches one selected external module path and binds a new source identity. The materializer changes only its manifest filename. The workflow changes its version label and matching manifest/script references. No library shim, theorem, excluded dependency, source-gate downgrade or new mathematical premise is introduced. The v1 source and first review remain frozen. The green gate still requires all nine execution outcomes on one v2 commit and independent inspection of the eight actual expanded types and axiom lists. Source-only review, uncompiled locally.
