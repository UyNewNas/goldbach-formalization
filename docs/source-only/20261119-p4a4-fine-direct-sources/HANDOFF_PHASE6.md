# P4A.4 later-sixth original fixtures and Q96 numerical subcheck

SOURCE_ONLY / COMPILED: NO / KERNEL_REPLAYED: NO / TRANSITIVE_AXIOMS: NOT CHECKED / INDEPENDENT_REVIEW_THIS_RUN: NO / LEAN FINITE CERTIFICATES: UNEVALUATED. The explicit numerical subcheck below succeeded; it is not a Lean kernel result and introduces no Lean theorem or assumption.

Baseline 8d2f9e81605318d870121f7bb269f0d684cbad59. Four unchanged archived source modules are bound with exact hashes in SOURCE_SELECTION_PHASE6.json: P2OriginalLaterSixthArchive, P2OriginalLaterSixthKernel, P2OriginalLaterSixthStageMass and the selected stage-repaired P2OriginalLaterSixthSourceIntegral. The former archive's originalLaterSixthText% elaborator calls IO.FS.readFile for all 15 names in its array, using the path ../tmp/publication-20261010/verification-renewal-v2/_runs/full-final relative to the process working directory. For a chosen project working directory, these are therefore actual elaboration inputs, not merely historical citations. This readback does not establish that the complete source/import graph is ready.

## Frozen input bytes

The later-stage and later-payment registries agree on all 15 named source files, lengths and SHA-256 values. The original GitHub release asset ID 626620833 has a recorded total SHA-256 8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1; this run did NOT download or recompute the complete 323,605,374-byte asset hash.

HTTP byte-range reads retrieved its ZIP central directory and then exactly the selected members, avoiding a whole-archive download. Each of the 10 witness JSON and 5 navigation JSON members was independently decompressed and checked against the two original registries' individual length and SHA-256, as well as the ZIP CRC-32. All 15 matched. The local stage places them at the elaborator's relative path alongside an isolated project working directory. Raw fixture files are not added to this repository; FIXTURE_RECEIPTS_PHASE6.json records the exact member names, byte offsets, compressed lengths, individual hashes and CRCs. recover_fixture_members.py can reconstruct them at a chosen existing project directory, rejects a mismatched existing file and verifies each extracted member. One fresh member was retrieved with the portable script successfully, and all 15 existing staged members were rechecked with it.

## Numerical comparison

check_later_q96.py checks the two selected Lean-source SHA-256 values and that the filenames, piece-to-file, offsets, navigation, patterns, piece counts and slot mapping match their literal source arrays. It reads the 15 individually verified documents. For all 21 pieces / 4,789 simplex records it checks simplex IDs and seven vertex indices, independently floors the rational bound recorded in each witness at Q=2^96, and compares that integer with the stored Q96 value. It also checks 3,414 stored auxiliary max-bound Q96 roundings. It then sums those stored values using the Lean slot map, including correction pieces 19 and 20 once in slot 5, and compares all seven sums to the literals of original_slot_totals. All these checks passed.

The seven Q96 numerators for G8–G14 are:
148834609033428677786865;
306737545112876482463163;
187277743940187526723019;
670429887277013841791829;
396820238432553171345546;
40185480009056702336216;
9304344466825907643536.

The last numerator equals 16*581521529176619227721, the original G14 rational 581521529176619227721/2^92. Its four source pieces 15–18 contain 60, 153, 322 and 1 simplices respectively. Their Q96 sums 1319589304650262861168, 1427773180538785395031, 6556943206335577926031 and 38775301281461306 match the four fixture gain_lower values individually and sum once to the G14 numerator.

These checks do NOT independently derive each recorded rational from vertices, determinant/volume, Q80 factor bounds, Jensen inequality, source gate, occurrence, signed payment or its real integral. They do NOT evaluate Lean's original_primitive, original_ordinary_Jensen, original_slot_totals, source_check, original_separators or any other finite proof body. The calculation does not certify All22, original hUpper, full distribution PP or the complete same-policy proof. It does not authorize reusing a CI object built from a different R17, K-ledger or radial selection.

## Recorded commands and remaining work

- curl byte-range reads of the fixed release returned HTTP 206; 15 members, 2,117,129 compressed member bytes and 14,257,735 uncompressed bytes. The whole ZIP hash was not evaluated.
- `python /tmp/p4a4_recover_members.py --project-dir p4a4-recovery-test/project --receipts /tmp/p4a4_fixture_receipts.json --only sixth-lower-mask33-upgrade-20261009-navigation.json`: exit 0, fresh recovery and exact hash verification.
- `python /tmp/p4a4_recover_members.py --project-dir p4a4-realize/project --receipts /tmp/p4a4_fixture_receipts.json`: exit 0, all 15 staged files rehashed.
- `python /tmp/p4a4_check_later_q96.py --project-dir p4a4-realize/project --receipts /tmp/p4a4_fixture_receipts.json --output /tmp/p4a4_later_q96_results.json`: exit 0, 4,789 recorded and 3,414 auxiliary rational floors plus seven slot sums matched. SHA-256 of the four delivered utilities/data records is recorded in SOURCE_SELECTION_PHASE6.json.
- Lean, Lake and elan were not available. No Lean typecheck, kernel replay, axiom check, numerical certificate proof evaluation, CI, independent review or user-machine access was performed.

Next: use the original data and exact selected source/overlays to check or compile the genuine finite guard and same-strategy arithmetic chain, and prove any actual failure found; continue the four-positive and remaining saving provenance against the same F/Q/rho. The selected original K ledger and radial dependencies must remain byte-consistent throughout the actual build.
