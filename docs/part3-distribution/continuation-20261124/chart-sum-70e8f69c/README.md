# Complete original chart-bank acceptance at 70e8f69c

The current public-helper LogSaving and complete ChartSum modules passed
strict compilation, kernel replay and the complete serialized inventory /
transitive-axiom audit in **Workspace Compile 27f68009**.

- Commit: `70e8f69cbbacb2b851147a5fa51948a106beeca7`.
- Workspace: `/workspace/goldbach-p3`.
- Task: `e59ba7fbaf2c4d1fb38d51af2c0b6580`, succeeded with exit code 0.
- Compiler: Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- Allowed transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Complete serialized declaration count: **20**.

| Module | Complete serialized declarations | Source SHA-256 |
| --- | ---: | --- |
| `Part3ProperPowerLogSaving` | 9 | `136815a60067b4e7eded3df5f9782b2d0cb3632d3e5da510019a04b6c86b5954` |
| `Part3ProperPowerChartSum` | 11 | `6033d5b3e829400a2b91bd8c55f7a61b4adcc72b853c1d6beff412aab0fac9c1` |

[report.json](report.json) records exact source/object hashes, commands,
all actual package revisions and stage-log hashes.
[declarations.json](declarations.json) preserves all 20 declaration types
and transitive axiom sets. [verification.zip](verification.zip) contains
every stage log, generated audit and compiler type output. ZIP SHA-256:
`f99f8e72deedc8a7b0b6468da82c230a9ca3db9dfa9db0fff9f387ba46def6a2`.

The full chart bank reconstructs the actual proper-power residual and
its original signed error, including the precise coprime mean and
full-product diagonal. It uses the accepted per-chart estimate at A+k
to pay the bank's logarithmic cardinality. It applies on effective VM
integer support, not merely on prime tuples.

The first attempt at a875610a passed normal compilation and LogSaving
strict compilation, then strict lint rejected a redundant `ring` after
`field_simp` had already closed the goal. Removing that tactic, without
changing statements or disabling lint, produced this accepted version.
The old LogSaving nine-declaration inventory is superseded, not added
again. The latest eight-module aggregate is 68 + 88 + 20 = 176.

This receipt does not supply the actual full-range Pascadi J/KS inputs,
the final medium estimate or the full P3 prime-product conclusion.
