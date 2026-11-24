# Proper-power continuation acceptance at 60cf3d49

The five proper-power continuation modules passed strict compilation,
kernel replay, and the complete serialized declaration/transitive-axiom
audit in the user-selected **Workspace Compile 27f68009** environment.
This receipt covers the actual per-chart residual estimate. It does not
claim acceptance of the later ChartSum source or completion of P3.

- Commit: `60cf3d49f8aefc687a6ce3dd7008ae5804cc61d3`.
- Workspace: `/workspace/goldbach-p3`.
- Task: `01939e7a38db48588e48759820e6a787`, succeeded with exit code 0.
- Compiler: Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- Allowed transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Complete serialized declaration count: **77**.

| Module | Complete serialized declarations | Source SHA-256 |
| --- | ---: | --- |
| `Part3SignedModulusPayment` | 21 | `57dbb0b13e356c86df1e2acb6289a07eed1acf4f9c91e00577bcc57095d7c0a9` |
| `Part3ProperPowerResidualPayment` | 23 | `f6227547d4df25745c53f2eca74c58e8f8d44a6d691ea0ac36969b7ae6ac7395` |
| `Part3ProperPowerDyadicBudget` | 7 | `d10e5809e4604ca7f34d302f0adad846b15de76a5c16a2ab749d325059d263fc` |
| `Part3ProperPowerOriginalChart` | 17 | `50a372771ebfa4cee6554402e938e5b7d334bd3cc1c0440a57df39c86fed26ca` |
| `Part3ProperPowerLogSaving` | 9 | `289913d4c27daee7b556f7d4a1bd5d68c38b44f375cde28baa16905665c672fc` |

[report.json](report.json) records exact source/object hashes, commands,
actual dependency revisions and stage-log hashes.
[declarations.json](declarations.json) preserves all 77 declaration types
and their transitive axioms. [verification.zip](verification.zip) retains
every stage log, the generated audit, full compiler type output and report.
ZIP SHA-256:
`0f6b483e36815cd341896b8e84027a7a4c7540fa49c9317b29567a054cc15fee`.

After export, the ZIP digest, every recorded stage-log digest, all five
literal replay messages, the original full inventory validation, and
all source hashes at this exact commit were matched. The baseline's 80
proof files are unchanged. The original baseline report was also located
in this workspace and copied byte-for-byte to
[baseline-c509267-report.json](../baseline-c509267-report.json), SHA-256
`c9367eb0ad5f2a35ec46e004ca9a6172d7a8113f8293862c38fffb94e9d90b34`.

The later public-helper revision of LogSaving must use its own new
receipt. Aggregate reports should select one verified version per module
and must not double-count these nine LogSaving declarations.
