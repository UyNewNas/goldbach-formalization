# Compiler-owner intake snapshot

Captured: 2026-10-28T13:26:53.225101+00:00

266 regular candidate sources across A-E, plus 1 separately listed frozen extra (267 total intake sources). No compilation, kernel verification, installation or numerical checker was run; new formal credit is zero. Every proposed installation remains ready_to_install=false.

| Batch | Candidate files | Metadata/map state |
| --- | ---: | --- |
| 20261028-resume-30 | 32 | Frozen exact batch map; 0 candidate mappings pending |
| 20261028-resume-30b | 34 | Frozen exact batch map; 0 candidate mappings pending |
| 20261028-resume-30c | 44 | Frozen exact batch map; 0 candidate mappings pending |
| 20261028-resume-30d | 68 | Frozen exact batch map; 0 candidate mappings pending |
| 20261028-resume-30e | 88 | Frozen exact batch map; 0 candidate mappings pending |

Read INTAKE_MANIFEST.json candidates for module_name -> exact source_path/SHA -> intended_install_relative_path. Each source also lists actual direct imports and destination state. Direct_dependencies is the exact pinned local frontier, with absent external package bytes separate. Frozen dependency copies are excluded from candidate counts.

Direct frontier: 439 distinct modules, 671 import occurrences. Status counts: {"MISSING_EXTERNAL_PACKAGE_BYTES": 32, "RESOLVED_EXACT_BYTES": 404, "SAME_BYTES_MULTIPLE_PATHS_IMPORTER_PIN_REQUIRED": 3}.
Global conflicting module/target bytes: 0. Explicit local pin mismatches at this snapshot: 0.

Candidate-only topological layers are included for intake planning. They are not a recursive build order for held source dependencies and do not certify import/axiom closure. The compiler owner still needs the pinned external package checkout, held prerequisites, source installation and API/type/kernel checks.

A-E are frozen at the recorded maps and raw hashes; no mapping exactness is a compilation or proof acceptance claim. No module or installation target is guessed from a filename. Extra adopted-plan candidates are listed separately only after complete author metadata, never counted among the regular thirty tasks. Pending records remain pending until exact metadata is supplied.

E frozen IMPORT_MAP reports one same-byte two-path alias. The merged A-E registry frontier records 3 same-byte path-alias modules (including two cross-registry production/held mirrors); importer pin failures: 0. No global alias path is selected. Every affected actual import edge retains its own explicit source pin.
E external bytes missing: {"goldbach": 2, "mathlib": 9}. Supplier hashes and package revisions are declarations only while their local bytes remain absent.

Confirmed extra candidate (outside the regular thirty-task batches):
- adopted_plan: 1 Lean file, 607 raw lines; Concrete tent-only bank and causal CapPlan; positive-width ordinary-root to third-cap accepted geometry. Full adopted policy remains OPEN. Module/source/target and exact pins are in extra_candidates/extra_summaries.

Extra delivery status:
- adopted_plan: ROOT_ACCEPTED_FROZEN_EXTRA_SOURCE_ONLY

Regular A-E counts remain 266 candidates and 668 import occurrences (437 distinct modules). The confirmed extra contributes one separately listed candidate and three import occurrences; the combined direct frontier has 439 distinct modules.
