# U02 P2 exporter delta — independent source applicability review

Disposition: **PASS_EXACT_SOURCE_DELTA_APPLICABILITY_ONLY**. This is a static review of the isolated exporter delta and its connection to the original P2 component. It approves no compilation, current checked environment, native kernel result, stdout parser, runtime/final/retention protocol, physical input, object reuse, dispatch, Ready status, or whole-P2 result. There is no unresolved finding within this assigned source-delta scope. Every unperformed gate below remains HOLD.

The reviewed U02 freeze is `97f39b56dc5018c8c6fea980f2ed2853afaf9e7411f9a7c5752dd3b0854de2ac` (3,738 bytes). Its only Lean candidate, `output/resume-20261115/u02-p2-exporter-only/CandidateAudit.lean`, is 26,345 bytes, SHA-256 `80f718e9820ac03dc572da2ad910e03dde5318022c5647d168a92301b9cbc956`, computed Git blob `92cfbcc5c54d6e92b212c802a5844fd0a738c53a`. No original R22 or inverse-R2 source/freeze is changed by this review.

## Evidence and unchanged P2 scope

`FROZEN_BYTES_AND_SCOPE.json` independently recomputes 19 length/SHA/Git-blob bindings, with zero mismatches: all seven U02 artifacts, original auditor, upstream algorithm, mathematical manifest, seven provenance bindings, upstream template and the U02 freeze. The 102 mathematical import lines and their order, the full original ordered 102-module array, and all printer-option lines are identical. `STATIC_DIFF_CHECK.json` independently applies the six patch hunks as text to the original auditor: every preimage matches and the result is exactly the frozen candidate. This is text processing, not evaluation of Lean or candidate Python.

Original R22 identity remains run `43635271771`, attempt 1, head `3d4dce4431e036fc7035429f136332e81e82871f`, mathematical source `d9002cf6fe0c162060db9760b587dc5fe7c549bb`, manifest SHA `909cc1172c77320ad905bcb63bd752ed31b21331c083c1fc7a1bf1d63e4c8938`. The prior 102-module successful compilation/kernel logs do not certify this new exporter.

The original endpoint is retained literally:

```lean
ImbalancedChen.Certificates.P2HistoricalThirdIntegerMass.checked_ordinary_integral_upper
(table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
(hg : P2OrdinaryIntegerGuard.check lo hi = true) :
  (∫ t in P2OrdinaryIntegerGuard.leaf lo hi, compactKernel t) ≤
    value (ordinaryUpper table lo hi)
```

This readable signature is a scope description; the existing `t07/p2-exporter-only-next-contract/REQUIRED_ENDPOINT_FULL_TYPES.json` preserves the original full compiler types. The new source requires this exact constant to be inventoried and to be a safe theorem (lines 228–231, 334–335). It does not compare its full type against that external original record. That comparison remains a mandatory future authenticated-parser/source-and-object binding gate.

The statement still assumes a `CheckedBlockTable` and the actual integer guard. It is the ordinary-leaf actual-integer-mass-to-integral component corresponding to main.md line 157 / P2.4, not the whole P2 claim at line 143. The whole checked table, successful actual guards and leaf coverage, original global partition/order/charge summation, required numerical dictionary or a valid complete alternative, and the whole manuscript numerical conclusion remain unpaid as specified in the contract. No easier terminal, weakened premise, inverse-542 scope, eight-facade exception, or new mathematical source is substituted.

## Transplant and added observations

The reused source is the already independently signed inverse-R2 `inverse_validation.py`, SHA `1f3445628be8da5e2779ff6db00f9bce8121b8e37e683afe25cab686569f6a53`; S03's exact source review is SHA `5bba825c159918c926b25a4059e550610b68e71df7734590c78474eb09e3e29c`. Only its actual-flag classification and fresh checked type/body worklist are reused. Its other scope counts and approvals are not transferred.

The independent text comparison finds the upstream fresh-worklist literal and obtains the identical core after removing only the added constructor/body/owner completeness checks, dependency-kind check, dependency-output list and graph-output deduplication. Those additions were inspected in their actual new position; they do not replace the approved traversal or add an accepting escape.

| Candidate lines | Independently inspected behavior and limit |
| --- | --- |
| 118–226 | Original const2ModIdx/serialized defining-owner multiset equality, multiplicities, nonempty modules, complete legacy/importAll/hasData requirements and canonical ownership are retained. The new exact totals are 102 modules, 3,628 ConstantInfos and a separate 3,787 extra-codegen names. All actual extra-codegen names are emitted; they are not kernel declarations or proof credit. |
| 143–153 | Actual loaded-module mode/importAll/hasData records are emitted for the complete loaded header. This observes the data needed by the later physical gate; it does not itself prove complete modern private loading or impose the full F7 acceptance contract on every dependency module. |
| 239–257 | Every inventoried root is read from `env.checked.get`. Actual `isUnsafe || isPartial` chooses the implementation class. Only actual defnInfo/opaqueInfo can enter that class on an accepting path; unexpected kinds and owned axioms cause failure. Every root creates new pending, seen, axiom and unsafe-dependency collections. |
| 258–303 | Every reached constant is read afresh from current checked data. Missing constants fail. All eight current ConstantInfo constructors are explicitly matched. Theorem/definition/opaque bodies are required via `value? (allowOpaque := true)`; missing bodies fail. Missing or out-of-bounds canonical owners fail. Every reachable unsafe/partial dependency rejects a safe root. |
| 298–317 | The same approved `getUsedConstantsAsSet` primitive supplies edges from current type and value, including opaque bodies and inductive/constructor/recursor metadata. The added body flag is not treated as a substitute for that traversal. The fixed-source semantics are also recorded in T02's read-only `FIXED_LEAN_SOURCE_REFERENCES.json` for Lean commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, FoldConsts lines 59–68. Actual body/facet availability still requires the new run's complete environment and physical bindings. |
| 300–317 | Dependencies are both recorded and queued before the global graph-emission test. `graphEmitted` only suppresses duplicate stdout node records; it never skips a checked lookup, safety check, AX check or dependency enqueue. Each root's fresh visited count remains independent. |
| 296–320 | All roots, including executable implementations, receive the same transitive AX walk. The only allowed axioms remain exactly propext, Classical.choice and Quot.sound. There is no suffix exception, imported `collectAxioms` shortcut or implementation AX bypass. |
| 325–384 | Both original full type printers remain. Actual constructor/owner/flags, per-root closure identity/count, AX and unsafe dependencies are added. Implementations explicitly receive zero proof and termination credit. Truncation, safety, kind and AX failures cannot yield a successful exporter; missing structural data already fails immediately. Diagnostic records are not acceptance. |

The exhaustive current ConstantInfo matches provide no wildcard accepting an unknown future constructor. Unsupported kinds are therefore a source compatibility/acceptance HOLD rather than a generic whitelist. Inductive and recursor records do not have a theorem-style `value?` body; their dependencies remain supplied by the unchanged approved primitive. No new incomplete manual type-only graph is introduced.

The original `firstMax._unsafe_rec` failure can be classified by this approved actual-flag/kind rule only when the future checked environment reports its real constructor and flags. Its name is never the acceptance criterion. This source review does not claim that its complete future safe-root reference graph has already been observed or accepted.

## Remaining mandatory gates

The candidate's `ROOT_PROTOCOL_BINDING_FIELDS.json` correctly leaves the runtime/parser/final/retention implementation pending. Its checklist is not implementation or protocol approval. T02's new R3 protocol is not imported as an approved result.

1. Compile only the exact independently approved exporter after authorization and complete input qualification. Mathematical source compiler events must be zero; no mathematical/C/native/link fallback may silently pay for missing cache objects. Lean parsing, API compatibility, resource sufficiency and execution have not been checked here.
2. Bind stage, qualification, preexec, proof, final and retention to these exact independently approved exporter bytes. A self-hash is not an external source approval.
3. Authenticate the actual kernel/exporter process argv, cwd, exits, stdout/stderr and runtime identity. Independently reparse complete 102/3,628 inventories, multiplicities, both full types, original terminal type, 3,787 separate codegen names, all dependency nodes/edges/owners/flags, and every per-root recomputed closure/AX count. Graph records alone or double type printing are not fresh audit evidence.
4. Fresh native kernel replay is required for the full safe logical scope of all 102 modules, with the implementation category retaining zero proof/termination credit. Preserve the original all-102 proof gates and fail on unknown kinds or any safe closure reaching unsafe/partial data.
5. Apply all original P2 F1–F7 gates to current full source, private/serialized/artifact/IR, stock, ABI, loader, setup/search/runtime, actual original stdout, collector/provenance and retention bindings. The P2 profile is b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254 / ALL407; no inverse or Weil scope exception is transferred.
6. Keep the original 19 compiled-candidate and 83 quarantined classifications unchanged. The existing index receipt authenticates producer metadata, not physical outputs. Current T09 acquisition is exactly 11 of 45 requested originals: five retention JSONs plus six stdout; 33 stdout and the collector log are still missing. The partial input receipt is SHA `f70a45ca5623df466dd1cc206915bc0e1ab8a00f69d86a3d646c05d52febc032`. The retained-object listing has only 612 of the 918 module-local references; 306 setup/C/C-hash references are absent from that listing. Neither this source AL nor the old tar metadata supplies those missing bytes or a loadable closure.

No candidate/helper/proof/setup/guard/fixture, Lean/Lake/LSP, kernel, runtime or collector was executed in this review. No artifact was downloaded, Git/GitHub mutated, quota inspected, CI prepared or dispatched, or subagent spawned. The source-only AL is useful for a later exact-byte protocol implementation; all execution, physical qualification and formal result fields remain false/HOLD.
