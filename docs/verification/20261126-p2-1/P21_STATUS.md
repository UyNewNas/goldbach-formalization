# P2.1 five-root query verification — 2026-11-26

**The frozen P2.1 query closure has cloud acceptance, its complete evidence payload is published, and full local archive verification has passed.** Payload commit `947a5dd8fb3c32c8a2688b767f559d7ab31d46d1` was pushed and independently read back with the expected tree and parent. All 409 archive parts and seven auxiliary originals were retrieved, and the unchanged local verifier accepted the reconstructed archive against the original source commit. The results and raw execution records are recorded in this evidence-record commit; no self-commit hash or future remote readback is asserted. Independent completion review: 57 checks passed, with no Critical or Important findings. Paths below are repository-relative.

The scope is the five roots in `docs/verification/20261125-p2-1/TARGETS.json`: **140 distinct project modules and 26 named public targets**, against the 20261106 English manuscript at `chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. The project partition is 132 base modules plus eight disjoint Buchstab modules. All 40 `BlockNNFullCheck` owners are included.

## Acceptance record

| Item | Evidence-bound result |
|---|---|
| Mathematical source snapshot | `00af18335dcebcc5e24571e33be7791ff718fbff` |
| Verification implementation / source-availability commit | `1de0453bee55bf1128be422787216937b8fda9c9` |
| Source tree | `af74f02d263c72b0bb8e003ce49d1134ac04c5d5` |
| Published payload / evidence records | Payload `947a5dd8fb3c32c8a2688b767f559d7ab31d46d1`; tree `14b67d3e5a4435fb02046d7d541e0d5531aff719`; parent `48b343279639cb3a289628d35cc23b2710eedd05`. The subsequent execution and review records are in this evidence-record commit. |
| Finalizer job / terminal status / exit code | `048eb7ed9b5141e692483cef94c6cd9d` / `succeeded` / `0` |
| Selected export | `140` / 140; unselected `0` |
| Owned / unique owned / duplicate declarations | `18,581` / `18,581` / `0` |
| Named types / five-root compatibility | `26` / 26; original joint probe passed; the complete original receipt has been recovered and its byte hash verified. Independent auxiliary semantic review passed with the recorded scope limits. |
| Archive bytes / SHA-256 | `490,564,596` / `066a46e41e34578a2adbf2a1120e8aba0470dfde44d6052bc8576d8fcb9aa212` |
| Byte-preservation and published-source verification | Original cloud and retained-copy verifiers passed. Fresh local reconstruction verified all 409 parts; the unchanged local verifier exited `0`, verifying 28,167 logical original members and all 140 source references against accepted commit `1de0453b`. |
| Execution, reuse and failure statistics | `Attempt 037: 35-module affected closure, 33 reused and two rebuilt; those two passed stock replay and full audits. Attempt 038: original finalizer succeeded in 2764.985397560995 seconds, peak RSS 10323308544 bytes. The 140-module union reuses source/context-bound historical evidence.` |

Completion requires the full 140-module selection, no unselected modules or duplicate owned declarations, all 26 complete types in their proper owners, and the original five-root compatibility receipt. A successful exporter process alone does not establish those conditions.

## Public API scope

Root names below omit `ImbalancedChen.`; full target names remain in `TARGETS.json` and the exported declarations.

| Root; named targets | Actual interface and domain |
|---|---|
| `Certificates.OriginalNodeArraysV1.All40PublicQueryAllBranches`; 5 | Concrete 40-block P112 reader, scaled exactly to P160, grid 16384 and endpoint 12. `query_encloses_all`, `query_eq_original_all` and `public_query_encloses_all` cover every rational query; integer queries require a positive denominator. `query_range_encloses_all` covers every real point between arbitrary rational endpoints. |
| `P0RationalQueryPublicAPI`; 6 | `pointQuery_sound`, literal/rational endpoint adapters, and `rangeQuery_sound`/`rangeQuery_rational_bounds` on the closed domain `[2,12]`. Integer representation transport additionally requires a nonnegative numerator and positive denominator. |
| `P2HistoricBackendTypeAdapters`; 9 | `sourceSf_*` binds exact Q80 `sf 16384 8` delegation and actual normalized lower-factor enclosure for every rational query. `sourceLogI_contains` retains positivity of the initially rounded lower endpoint; the `of_one_le` and `ratio_contains` variants discharge that guard for `q >= 1` and ordered positive ratios. |
| `P5ZU1011AutomaticBuchstabIntervals`; 2 | `actual_interval_bounds` gives deterministic rational bounds on actual `buchstab s` for a natural number `m > 0` and `1 <= l <= s <= u <= 8`, including singleton queries and closed-cell knots. `actual_interval_width` requires a natural number `m > 0` and `2 <= l <= u <= 8`, and gives width at most `(u-l)/2 + 3000/m`. |
| `P2OriginalCompactQ80Table`; 4 | `table12_encloses_actual`: nodes 16384–196608. `numerator12_contains_actual_L`: `b > 0`, `2*b < a <= 12*b`. `point12_contains_actual`: every signed numerator and positive denominator. `sf12_contains_actual`: every rational `q`. All use original Q80 `sf 16384 12`. |

These concrete roots discharge their node/checker or backend-soundness premises. They retain their stated geometric and rounding guards. See `MANUSCRIPT_SCOPE.md` and `PRODUCER_BINDINGS.md` in the preceding evidence directory, especially numerical-appendix sections 94–175 and 425–445.

## Repair and verification provenance

The sole latest Lean repair changes the `contains_iff` proof site to definitional `change x.enclosure.Contains v`, then retains the existing simplification without `I80.Contains`. It preserves all theorem types, assumptions, imports and algorithms, avoiding duplicate lazy generation of `I80.Contains.eq_1`. The Sieve owner remains. Attempt 037 compiled only LogPoint and BackendTypeAdapters within the 35-module closure, reusing 33 records; independent replay and complete audits accepted those two owners, with 125 and 30 declarations. These counts are not additional declarations to add to the final union.

Normal compilation, stock `leanchecker` replay and complete owned-declaration audit are distinct gates. Reused receipts must bind the same source/object closure, runtime and native context. Owned inventories include private and generated declarations and must agree with serialized and environment inventories. Every declaration must be safe, total and non-axiomatic; transitive axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

Eight historical normal-compile logs remain unavailable: `VariableEnvelope`, `VariableEnvelopeConsequences`, `VariableEnvelopeRegularity`, `VariableEnvelopeBoxes`, `VariableEnvelopeScaled`, `VariableEnvelopeCertificates`, `BufferedFirstCubeGeometry`, and `VariableEnvelopeTailFloor`. The export retains these warnings and the available registry/source/object provenance; no replacement logs are fabricated. The fresh-compilation and reuse counts are reported separately in the acceptance record above.

The qualified native contexts contain 515 and 518 modules. The extension preserves the parent bindings and adds the three existing Buchstab providers. Qualification, fixture tests, transport and packaging confer no new mathematical proof credit.

## Publication and local verification results

The user explicitly answered **“同意”** to public release of the complete fixed P2.1 payload, including original compiler/audit logs, raw receipts and internal-path metadata, followed by full local retrieval, verification and publication of those records. [USER_PUBLICATION_AUTHORIZATION.json](USER_PUBLICATION_AUTHORIZATION.json) records this scope. The destination is the public repository `UyNewNas/goldbach-formalization`, branch `evidence/p2-1-20261126-6c7864ad`.

Prepare task `5bb55459f0854475b46dd18a78c0aa7c` succeeded with exit `0` in 81.891978 seconds. Its unchanged `PREPARED_ONLY` report binds all 409 archive parts, seven auxiliary originals and 140 sources. Its 2,877 original bytes have SHA256 `aaf23fc49c3e287b95ee8db08529fa4fbb83a31010fd32506985b9811b106efd`. The false push and local-verification flags in that report describe the prepare stage and remain unchanged.

The resumed push task `0e8e08b3c3254066a8cadd51cf95071e` succeeded with exit `0` in 37.71464767099678 seconds, peak memory 31,985,664 bytes and complete 10,286-byte stdout with no discarded bytes or truncation. All five stages—guard, original-report emission, initial ref check, push and ref readback—ran and exited `0`. The empty-ref lease created the intended branch at payload commit `947a5dd8fb3c32c8a2688b767f559d7ab31d46d1`. A separate GitHub readback verified that commit, tree `14b67d3e5a4435fb02046d7d541e0d5531aff719` and parent `48b343279639cb3a289628d35cc23b2710eedd05`.

[PUSH_RESULT.json](PUSH_RESULT.json) is the separate actual push report: 6,967 bytes, SHA256 `3243c46b98113424b51148ac2e76e36d8d8ecfb5a53e256e909a213802991ff8`. [PUSH_READBACK_VERIFICATION.json](PUSH_READBACK_VERIFICATION.json) binds the unchanged prepared report, actual terminal/stdout and independent GitHub responses. [AUTHORIZATION_AND_PUSH.tar.xz](AUTHORIZATION_AND_PUSH.tar.xz) retains this continuation's authorization record and raw submission, terminal and readback envelopes. The restored push command is 11,263 bytes, SHA256 `aafa92d03968c99ea23502858095b4586cc7090decc4b5c98a2eed0386c54380`; it is not byte-identical to the lost 11,269-byte command described by the historical block. The fixed payload was not regenerated.

Fresh Git retrieval then completed successfully. It checked the exact four pinned transport manifests, all 409 archive Git blobs, all seven losslessly recovered auxiliary originals and all 39 of their original PLAN parts. All 29 actual Git commands exited `0`. The reconstructed archive has exactly 490,564,596 bytes and SHA256 `066a46e41e34578a2adbf2a1120e8aba0470dfde44d6052bc8576d8fcb9aa212`. [GIT_RETRIEVAL_RESULT.json](GIT_RETRIEVAL_RESULT.json) records those checks: 282,278 bytes, SHA256 `2613854c2a1246f38eb7fa8720957e1e821b59c41361a37d802710803a1a57fa`. Its `archive_verifier_executed=false` and `local_archive_verified=false` fields accurately describe the retrieval stage; the later verifier has its own record.

The unchanged `repack_winner9_private_evidence.py verify` subsequently ran against the reconstructed archive and accepted source commit `1de0453bee55bf1128be422787216937b8fda9c9`. It exited `0` in 35.89830784399237 seconds, with 586-byte stdout and empty stderr. Its source SHA256 remained `bf20e2992d7f798b3bf5b00d054b56503796ff29822e1bb8ae03bff4b166cb5b`. [LOCAL_ARCHIVE_EXECUTION.json](LOCAL_ARCHIVE_EXECUTION.json) binds the actual command, exit, elapsed time, output and unchanged verifier. [LOCAL_ARCHIVE_VERIFICATION.json](LOCAL_ARCHIVE_VERIFICATION.json) contains 39,974 bytes with SHA256 `684b9b57b9698a34475f7e1e5ffdbd0b68bd94ef6af93be5afc6a6ac8b30262e`.

That local run verified **28,167 logical original archive members and 140 exact Git source references**, accepted source tree `af74f02d263c72b0bb8e003ce49d1134ac04c5d5`, and the original archive's declared 140 accepted modules and 18,581 owned declarations. Its scope is byte preservation and source availability. It did not invoke Lean, stock kernel replay or a new owned audit. The original cloud verifier remains unchanged as `ORIGINAL_ARCHIVE_VERIFICATION.json`.

### Independent review and preserved history

The earlier auxiliary semantic review recorded 74 consistency checks, zero Critical findings and zero Important findings in `FULL_AUXILIARY_EVIDENCE_REVIEW.json`. It matched all 140 modules and source hashes, independently summed per-owner counts to 18,581, checked all 26 public interfaces and the 6,724-module joint import, and retained the eight missing-normal-log warnings. The 339 native-overlay log paths were reconciled with the original checker's canonical-path semantics, without claiming a fresh resolution of private cloud symlinks. That review did not re-enumerate complete owner inventories, per-declaration safety rows or raw replay/audit logs inside the archive.

The current independent completion review passed **all 57 checks**, with no Critical or Important findings. [LOCAL_COMPLETION_REVIEW.json](LOCAL_COMPLETION_REVIEW.json) contains 25,016 bytes with SHA256 `924808305b516b40db0a346a6ffa82b9d3c514445d3e4b2a12307cf8564186d3`.

It independently checked the actual push/ref/tree/parent records, all 29 Git-command receipts and 4,488,200 bytes of their small I/O, the four pinned manifests, and every one of the 409 archive-part receipts against the original PLAN and Git tree. It independently rehashed all seven recovered auxiliary originals, totaling 40,769,869 bytes, and all 39 original auxiliary PLAN parts. It checked the unchanged verifier's actual command, source hash, exit `0`, stdout/stderr and complete report, and compared all 140 canonical source-reference rows with the frozen source bindings and prior original verification.

The source-reference map retains one historical same-byte source-only alias: 141 matching repository paths represent **140 canonical selected sources**, not an additional module. This alias is unchanged from the original cloud report. The review did not reread the 490,564,596-byte archive or its large binary batch capture, rerun the already successful verifier, rerun the earlier 74 checks, or invoke Lean. It confirmed that the recovered auxiliaries exactly match the bytes reviewed earlier.

The 18,581 owned/unique declaration counts and empty duplicate map remain original source-bound finalizer acceptance. This completion review did not freshly enumerate owned names, execute per-declaration audits or repeat kernel replay. Its publication check covers immutable payload commit `947a5dd8`; it makes no claim about remote publication or readback of the subsequent evidence-record or code-document commits.

The earlier automatic rejection happened before a push job was created. [PUBLICATION_BLOCK.json](PUBLICATION_BLOCK.json) retains its original text, circumstances and old command/capture hashes. The user's later explicit authorization resolved that condition; the block is retained as history. The old complete rejection capture is no longer available after temporary-storage loss. The old internal four-chunk/raw-page captures and temporary recovered files were also lost; saved verification and review records survived. Fresh readback in this continuation is new evidence, and is not the missing original capture. [RECOVERY_BOUNDARIES.json](RECOVERY_BOUNDARIES.json) records the remaining provenance limits.

The previous internal readback first exceeded P2's actual 2 MiB stdout-retention cap, then completed using four verified cached-bundle chunks. Its surviving reports retain that distinction. The current fresh retrieval independently re-established all seven auxiliary originals and their 39 PLAN parts from the published payload. Historical preparation-terminal hashes in the original push report remain historical bindings; they do not reconstruct the lost original tool envelope.

## Reconstructing the fixed published payload

Use a checkout of immutable payload commit `947a5dd8fb3c32c8a2688b767f559d7ab31d46d1` with all 409 `archive-parts` files present. The manifests credit 29 archive parts to existing MCP transfer captures and 380 parts to direct Git transport. No MCP capture is claimed for a part delivered solely through Git. Every part and the reassembled archive must match the recorded bytes and SHA256.

The original `FINALIZATION.json` (`9446bdef4c23ba799006bd96e236e0a3ddce82d9afcbd68dcafa4b5d3162c868`), export manifest (`6e9da9d095b500c85c85d70a358db135e1b19b6eea4d80f5a2de40974e85ed0f`), all three joint artifacts, original archive verification and `PERSISTENT_COPY.json` (`90c6ad3fa52488f3e626026db8b047668f23c9d0eba676535dffbb938f1b04c4`) are preserved as original bytes. The retention mapping binds copied bytes without rewriting their original descriptors. The current execution reports are separate records in this evidence-record commit.

From that fixed checkout's repository root, using the existing `parts`/`full_archive` manifest convention:

```bash
p21_out=$(mktemp -d)
python3 - "$p21_out/p21.tar.xz" <<'PY'
import hashlib, json, sys
from pathlib import Path
m = json.loads(Path('docs/verification/20261126-p2-1/ARCHIVE_PARTS.json').read_bytes())
h, size = hashlib.sha256(), 0
with Path(sys.argv[1]).open('xb') as output:
    for i, part in enumerate(sorted(m['parts'], key=lambda p: p['index'])):
        assert part['index'] == i
        data = Path(part['path']).read_bytes()
        assert len(data) == part['bytes']
        assert hashlib.sha256(data).hexdigest() == part['sha256']
        output.write(data); h.update(data); size += len(data)
assert size == m['full_archive']['bytes']
assert h.hexdigest() == m['full_archive']['sha256']
PY
python3 verification/part2/repack_winner9_private_evidence.py verify \
  "$p21_out/p21.tar.xz" --repo . \
  --git-tree 1de0453bee55bf1128be422787216937b8fda9c9 \
  --output "$p21_out/verification.json"
```

**Full P2 remains incomplete (`full_p2_complete=false`).** Query correctness does not establish historical serialized-array identity, equality with author Q80/4096 or N48/8192 Buchstab integers, adaptive trees, downstream saved floors/charges, all integral totals, final density constants or the manuscript's main theorem.
