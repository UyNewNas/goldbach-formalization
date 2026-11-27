# Review of the two-owner evidence export

This source review covers the two original U5 rounded correction and count owners. The original audit job is `job_5f9c0d1eb4cc49348095b29f16fcd481` on P1.

| Reviewed helper | SHA-256 |
| --- | --- |
| `export_owned.py` | `1c92eabac8ee9e250341d2c2382228ba37445886bbcd9f0f753f3b67c4665286` |
| `verify_export_locally.py` | `a05b39ff122479444d8df499c5f495b2aa94defb1e08320ab8f3c428d4ddc2fc` |

The exporter maps the two module names to their exact source and object paths and checks their digests. It includes the driver, generated audit, validation report, inventory, command logs and pins. Each archived payload has a length and SHA-256 entry. The exporter re-reads the inputs to check for changes and emits the compressed size and SHA-256 alongside the Base64 bytes. Checking the decoded archive against this original export record binds the transport.

The local checker reads regular files directly from the archive, rejects duplicate or escaping member names, and verifies the complete manifest. It compares the owner sources with the worktree, the owner objects with their pins, and the 286 project sources with the accepted source list. Compiler, checker and reused object identities are compared with their recorded pins. Runtime byte checks of these binaries and reused objects come from the original driver. The local checker also re-renders the exact inventory input, verifies the expected replay names, and runs the original inventory validator on the archived audit log. That validator checks full declarations, types, defining modules, counts and permitted transitive axioms.

**One terminal-to-report check remains outside the reviewed local helper.** It checks the original successful task ID, exit code, time window and untruncated status, but does not compare the archived verification report with the final report printed by that task. The driver prints the complete report in its final output. Before attributing the recovered archive to this specific audit, compare that original stdout JSON with `acceptance/report.json`. Equality binds the verification ID, ordered command and log hashes, counts and reported axioms. The downstream checks already bind the payloads to those values.

This review inspected source and paths. It ran no remote command, compiler, replay or archive verification. The actual terminal, archive-digest comparison and local verification output supply execution evidence.

## Disposition after the transport fix

**Addressed.** I reviewed `verify_export_locally.py` at SHA-256 `ef711c377e50aec979514098911d5e9d88601a1f1249ba1c153e2521ba892261`. The exporter SHA-256 remains `1c92eabac8ee9e250341d2c2382228ba37445886bbcd9f0f753f3b67c4665286`.

The revised checker requires the named original audit to have succeeded with exit 0 and untruncated stdout of the recorded byte length. It recovers the unique complete verification report from that stdout and compares the full JSON object with the archived report. Its verification ID must also match the export frame. The exporter’s task ID, truncation flag and complete stdout length are checked. Its unique frame must reproduce the recovered xz file byte for byte using strict Base64 decoding, and must agree on length and SHA-256. The checker records both original stdout digests. These checks close the original terminal-to-report and transport mappings. The exporter’s separate task exit status, if reported, should be read from its terminal. Exact transported bytes are established by the complete frame.

This disposition covers the revised source. The parent reports that the original audit succeeded with exit 0 in 687.85 seconds. The local verification receipt records the outcome on the retrieved evidence.
