# Checked original Cell06 input prefix

This milestone accepts exactly the two restored original packed-data modules and `P2OriginalSaving19Geometry06ScalableInput`. The source copied into the repository is byte-identical to its successfully compiled source.

- Data06: official trust-zero replay checked both packed declarations; embedded bytes matched the entire original geometry (335,849 bytes) and moment (58,376 bytes). Full environment/serialized auditing checked both declarations with no axioms, unsafe or partial declarations and no new external imports. The old data normal builds were reused exactly.
- Input interface: strict normal compilation, official `leanchecker --verbose` and complete full-owned auditing passed. All nine canonical declarations and zero shared occurrences were inventoried. The normal object is 22,064 bytes, SHA256 `5bbf6326f14f962665dca69f2ab3aefea8ecc5503131331b827b1b860fb737ed`.
- The interface establishes the actual packed input, length 335,849 and exact remaining-list/drop equalities. It does not establish JSON parser/decoder, row arithmetic or an integral bound.

The accepted project union has 1,502 modules. Parent Cell01 milestone is `c985c5965c3ca64a30570829713b25d5ebdcc243`. Current source candidates and controller delivery are separately preserved at artifact commit `9779a018863ddfc674f34228beffbf7c34f4867c`.

`CAPSULE.json` records all five successful mode receipts and the exact STAGE contract. `CURRENT_ACCEPTED_CONTEXT.json` is the byte-identical selected catalog; its SHA256 is `d528a2f388f10c22b89c218e675b534a76de129de50054fd1dc4a68e66398ad1`. The archive includes the 24.15 MB shared input baseline, 32.60 MB environment lock, source/object pairs, permanent normal output, all actual commands/results/logs/seals, raw input copies and verification programs. Existing parent objects are referenced by exact pins and supplied by the parent evidence.

Archive `evidence.tar.xz`: 9,471,824 bytes, SHA256 `13a74b907d99206ed87c9651009c3df8915362b061ff7661184971fd0f5133a9`; all 59 members including MANIFEST were read back. No successful proof command was repeated during packaging.

Observed execution: Data2 took 129.113s (processes 15.194s replay plus 13.986s audit), sampled task peak 7,602,868,224 bytes. The input owner took 151.363s (normal 2.242s, stock checker 3.317s, audit 11.457s), sampled task peak 7,379,066,880 bytes. Remaining time includes input verification and other controller overhead; it has not all been isolated as hash cost. Broader batch performance remains unverified.

`Cell06_integral_complete:false`, `P2_6_complete:false` and `original_full_snapshot_verified:false` remain explicit. All 113 rows, 33 vertices, 97 gates, degree6/expdegree3, Q80/Q96 and saved max(old,new) remain required by the later Cell06 candidates. The new batch-boundary implementation is outside this checked milestone.
