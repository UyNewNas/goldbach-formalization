# Spectral continuation acceptance at 80d7eeb

The two spectral continuation modules passed strict compilation, kernel
replay, and the complete serialized declaration/transitive-axiom audit.
This receipt verifies these two conditional transport modules, not the
actual full-range Pascadi J input or P3 as a whole.

- Commit: `80d7eeb46250bea9fee3a42fc499929f080e9ab1`.
- [GitHub run](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45343356986).
- Job: `138272108983`; artifact: `14897342383`.
- Compiler: Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- Allowed transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.

| Module | Complete serialized declarations | Source SHA-256 |
| --- | ---: | --- |
| `Part3ExceptionalWeightExtension` | 43 | `ab3c1305215ea2251ba32dba5916ae6a05d006dc5fc021492730c8603fa92719` |
| `Part3ExceptionalWeightGeometry` | 45 | `250a3da7c65ca7483432e68ddaf7494213d00701ca9179255f9afde6153d9a84` |

[report.json](report.json) contains the exact source/object hashes,
commands, actual package revisions and stage-log hashes.
[declarations.json](declarations.json) retains all 88 declaration types
and their transitive axioms.
[verification.zip](verification.zip) is the unmodified GitHub artifact,
including every stage log, the generated Lean audit, and the full
compiler theorem types. ZIP SHA-256:
`02b1f2f9dd1afb828166ae4ee619481c0e71d706e8aba678a90144ac1ededb1e`.

After download, the artifact digest, every recorded stage-log digest,
both literal module replay messages, the 88 declaration records, and the
two current source hashes were independently matched. The baseline's
80 proof source files remain unchanged.
