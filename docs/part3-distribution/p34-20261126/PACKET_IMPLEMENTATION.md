# Task 1 implementation and local verification

Initial source commit `40a5b28303c652450da65e740fd5a4e70c902391` extends `f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e`. The root agent owns the independent cloud check and publication.

## Source and mathematical review

- The five donor files supplied 15 public declarations. Each original signature, original file SHA-256, exact line interval and original declaration block SHA-256 is in `docs/part3-distribution/p34-20261126/DECLARATION_MOVES.json`. I recorded the intervals, hashes and signatures from the base before editing. I later re-read each interval from `git show <base>:<path>`, checked both hashes and all signatures, and compared each destination. Fourteen complete blocks are byte-identical, including the entire ten-declaration coefficients block. I compared each complete donor remainder after deleting only the expected block and accounting for the new import. All five comparisons passed.
- The packet retains the residue, level, positive-level proof, multiplier, residue-level coprimality proof and original beta. The indicator tests `Nat.Coprime n d.residue` before producing the coefficient. The modulated beta uses `k 2 / 64` times the physical first variable divided by U and `k 3 / 64` times the level variable divided by Z. The mode update changes only beta. The existing finite sums use the original carrier on both sides. At this initial commit, both original pairing bodies and statements were byte-identical. The first body was later adjusted in the audit repair below.
- The new scalar product theorem follows from the moved real equality and `e_add`. The Boolean specialization uses eta = -1 for a negative frequency and eta = +1 otherwise. The new pairing combines the specialization with the prior signed section theorem at the same positive level and height, actual Gamma0-invariant function and signed integer frequency. The coefficient is the fixed-height Haar coefficient. A Maass/Eisenstein supplier, the original Oldform spectral coefficient relation and the original staged `OriginalData` row consumers remain open.
- Prior archived sources and the seven-module acceptance directory have no source diff against the baseline. The optional seven-module verifier defaults still name the same old scope, audit, baseline and output directory. The new script invokes the shared verifier with its own 13-module catalogue. Its source manifest also binds the new Python entry point and declaration move ledger. The Lean auditor uses the original serialized vs. defining-module equality, private/generated declaration traversal and transitive allowlist, changing only the import and module lists.
- Only the Task 1 changes and the root-authored plan and incremental source search were staged. No remote operations or cloud compiler requests were made by this worker.

## Focused checks and repairs

All commands below used the repository working directory with `source /workspace/library-files/p34-runtime/env.sh`.

1. Strictly elaborated the changed modules by setting `m=ImbalancedChen/Part3<short>` and running `lake env lean -t0 -j1 -M6000 -DwarningAsError=true -o .lake/build/lib/lean/$m.olean $m.lean`. The seven short names were FourierModeIndex, CoprimePacketCore, CuspPhaseCore, CoprimePacketCoefficients, ActualCuspScalingSourceOnly, ActualCuspPacketPairing and OldformCuspPhase. All passed after the following changes.
2. The extracted `norm_e` previously referred to the large donor's `e_eq_fourier`. Computing the real part of the purely imaginary exponent with `Complex.norm_exp` removes that dependency. This is the only changed body among the 15 moved declarations.
3. In the staged scaling theorem `cuspPhase_true_mul_false`, the original simplifier left a sum of opposite divisions and flagged three unused simp arguments under warnings-as-errors. The repair exposes both sign choices, proves the sum is zero by `ring`, then uses reverse `e_add` and evaluates `e 0`. The proof works for every natural z and n in the original statement.
4. The original pairing file did not enable the scopes for `SL(2, ℤ)` and `ℍ`. Compilation first reported unexpected opening parentheses at both theorem arguments. Opening `MatrixGroups` and `UpperHalfPlane` resolved both declarations with unchanged bodies. The two staged-module banners now identify their date of origin and current verifier.
5. Ran `python verification/verify_p34_cusp_packet.py --source-only --expected-head <base>` and `python verification/verify_p34_cusp_normalization.py --source-only --output-dir .lake/p34-default-regression --expected-head <base>`. Both reported SOURCE_ONLY_NOT_COMPILED. Inspected the original verifier's seven-module catalogue and report metadata. `lake env python verification/test_p34_import_scope.py` passed all three regressions. `git diff --cached --check` passed. The source-only runs are separate from the compiled evidence.
6. Launched the full verifier on the clean source commit with `python verification/verify_p34_cusp_packet.py --expected-head 40a5b28303c652450da65e740fd5a4e70c902391`. Local detailed logs and source/tool/object manifests are in `.lake/p34-packet-acceptance/`. Root manages a distinct formal cloud acceptance run.

## Initial full run failure and independent inventory review

The first full local run at `40a5b28303c652450da65e740fd5a4e70c902391` completed strict elaboration and the bundled kernel replay for all 13 modules, the parsed-import guard and its three regressions. It failed before the declaration/axiom inventory. Lean exited 1 at `verification/P34CuspPacketAudit.lean:35:0`:

```text
Serialized and defining-module inventories differ for ImbalancedChen.Part3CoprimePacketCoefficients
```

The audit compares the complete serialized constant set of each module to the environment's owner map. Independent consumers of the same definition can generate a congruence or unfolding lemma with identical declaration names. Each serialized copy is real, and the environment maps the name to a single owning module. A diagnostic with the exact official auditor's 13 imports compared both sets for every module and read each discrepant declaration from both `ModuleData.constants` arrays. The two complete types and two proof values matched textually for each duplicated name. All six printed `ConstantInfo` types/values had no elision marker. The receipt records all 13 pairs of complete inventories, every owner index and name, and both serialization locations for all three duplicated constants. It embeds the diagnostic Lean source and the 13 original olean hashes. Read it with `gzip -dc docs/part3-distribution/p34-20261126/failed-40a5b283-inventory.json.gz`. The initial full verifier's unmodified logs remain at `.lake/p34-packet-acceptance/`.

| Generated declaration | Official environment owner | Other serialization |
| --- | --- | --- |
| `P3ActualLiteralPacketIntegralSourceOnly.cuspPhase.eq_1` | `Part3CuspTranslationFourierPhase` | `Part3CoprimePacketCoefficients` |
| `ImbalancedChen.Part3.ActualCuspFourierSectionSourceOnly.oldFourierCoeff.congr_simp` | `Part3SignedCuspFourierSection` | `Part3ActualCuspPacketPairing` |
| `ImbalancedChen.Part3.ActualCuspFourierSectionSourceOnly.newFourierCoeff.congr_simp` | `Part3SignedCuspFourierSection` | `Part3ActualCuspPacketPairing` |

Round 1 keeps the serialized/defining inventory equality, all declaration traversal and all other auditor conditions unchanged. A local simp attribute now materializes the unfolding equation in the common defining module before the independent consumers import it. The attribute goes out of scope there. Three simplifier calls in the first existing pairing proof use explicit rewrites instead; this avoids regenerating two congruence lemmas owned by the signed section module. No active declaration was renamed or deleted. The source header cites both provenance ledgers.

An isolated check with `Lean.readModuleData` on the two changed modules' newly compiled objects showed `Part3CuspPhaseCore` serialized `cuspPhase.eq_1` and `Part3ActualCuspPacketPairing` serialized exactly the two public pairing theorems. The scalar and finite-sum statements remain unchanged.

## Round 1 clean source validation

Local repair commit `7d9d146c100a64dc4c7ce0abec014314e5be37e4`, tree `9effc51d3ce49d4aa29c9b2aa811d1f18373ee03`. Root published the same tree as GitHub commit `145be87ff0a88914b607baa2a330bc88105a08d6` and manages its separate cloud receipt.

Recompiled the eight affected modules in dependency order with the strict command from step 1 and ran `lake env lean -t0 -j1 -M6000 -DwarningAsError=true verification/P34CuspPacketAudit.lean`. The auditor emitted `PART3_AUDIT_COUNT 167`. The focused diagnostic also printed `13 of 13 exact serialized/defining inventories agree`. The complete original verifier entry point then ran on the exact clean repair source:

```sh
source /workspace/library-files/p34-runtime/env.sh
python verification/verify_p34_cusp_packet.py --expected-head 7d9d146c100a64dc4c7ce0abec014314e5be37e4 --output-dir .lake/p34-packet-acceptance-r1
```

The verifier exited 0 and recorded **PASSED**. All 70 subprocess stages exited 0, including 13 strict compilations, 13 bundled kernel replays, 14 parsed import inventories covering the modules and auditor, the import-scope regressions and final working-tree cleanliness. The complete inventory contains **167 declarations**, including **124 theorem constants**. The union of transitive axioms is exactly `Classical.choice`, `Quot.sound` and `propext`. The archived failed-run directory was preserved in place. Counts in dependency order were `1, 23, 7, 11, 15, 20, 10, 38, 13, 16, 7, 2, 4`. No separate rerun of the old seven-module acceptance was made.

The local success is attached to its exact local commit. The separate cloud check is owned by root. The checked scope does not extend to all external mathlib objects or the original four staged consumers.
