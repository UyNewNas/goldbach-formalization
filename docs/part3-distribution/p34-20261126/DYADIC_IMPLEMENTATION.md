# Task 3 implementation and local verification

Assigned source checkout and review base `0c5917f49a3bfe30c4619b606cb2b77d4cc11239`; verifier ancestry and donor source `2b284342fce23962a1b431d8003cb5cdffac8128`. The donor git blobs and file SHA-256 values match the source-only records in the approved plan. Both exact parent remainders were compared after excising the selected contiguous source range and adding one import. All five short-parent consumers and three assembly-parent consumers retain their complete source blocks. The heavy parents are outside this verification unit.

The 20 short and 28 assembly declarations use their old namespaces, public signatures, and finite definitions. The single private helper `finite_singleton` is now public under the old short namespace; its proof is unchanged. Every donor signature, block, range, hash, final target-block hash, elaborated-type digest, and necessary proof repair is recorded in `docs/part3-distribution/p34-20261126/DYADIC_DECLARATION_MOVES.json`. The two cores use exactly the planned imports and reuse the finite source, signed output, coprime packet, mode coefficient and primary gate.

The scale is strictly open below and closed above, with the `j=0` scale equal to one half. The computed key remembers the sign and depends only on the joint output, so each output's finite beta belongs to a unique key. The energy identity sums those same squared norms without a cardinality multiplier. The nonzero-beta premise gives a source witness, and the actual signed quotient gives the coprimality and singleton endpoints. The code's output scale `U` is the manuscript's `Y` at lines 676–687. The coefficient gate matches line 722 and the one-half lower bound matches the length premise in line 999. No new assumption or supplier for the Maass/Eisenstein coefficient, oldform relation, original row or common interval is introduced.

The initial migration check failed at the absent new core before any tracked edit. The donor hash and block checks then passed on the exact move. First focused short elaboration reported a change to positive-factor multiplication cancellation and an equal-branch conditional left by the old split tactic. The first repair uses the pinned positive-factor theorem with the donor's original multiplier positivity; the second simplifies the identical zero branches. Both are Lean elaboration repairs and preserve the complete statement.

The first focused assembly check exposed four pinned elaboration issues. The sign split left the immediate integer consequence `y ≤ 0` of `hn : y < 0`. The equality between the two filtered fibres required explicit `Finset.ext` and membership projection/construction. A final `simpa` with no `using` triggered the strict unnecessary-simpa linter. The occupied energy branch required the norm and square to be distributed explicitly over the same output-key conditional before simplification of its unique summand. A first repair of the sign branch using a chained tactic generated a strict unnecessary-sequence-focus warning; the final proof closes its single remaining goal directly by `hn.le`. The unchanged energy proof structure still exchanges the finite sums and then splits on the actual beta.

## Exact source and focused inventory

Commit `ca06f1264eb7e098f9c1f21e3174ea059b2d61e9` has tree `b44520eee77b18d80a38d95e937ab812581f98ac` and parent `0c5917f49a3bfe30c4619b606cb2b77d4cc11239`. Seven owned paths changed. Clean git status was checked after commit. Across both moved cores, 42 bodies match their donor bytes after visibility normalization, and six are the proof repairs described above.

The focused strict builds used the pinned executable and the original resolved local dependency path (obtained from the Task 2 bundled-tools receipt). Both new files passed with `-t0 -j1 -M6000 -DwarningAsError=true`, emitting their project olean files. The focused nine-module audit then passed with 168 serialized/actual-owned declarations, of which 26 belong to the short core and 38 to the assembly core. Its output supplied the 48 type digests prior to the clean source commit. The exact command for fresh full verification follows.

```bash
cd /workspace/library-files/p34-proof-work
set -eo pipefail
source /workspace/library-files/p34-runtime/env.sh
python verification/verify_p34_primary_dyadic.py --expected-head ca06f1264eb7e098f9c1f21e3174ea059b2d61e9 --output-dir .lake/p34-primary-dyadic-acceptance | tee .lake/p34-primary-dyadic-local.log
python .lake/p34-dyadic-final-check.py .lake/p34-primary-dyadic-acceptance | tee .lake/p34-dyadic-final-check.log
```

## Independent reviewer finding on the shared verifier

Root's independent whole-branch review identified a clean-checkout reproducibility issue in the shared pre-existing import-scope regression test: its positive control uses the phase and Gamma objects of an earlier scope. The local checkout has the old Gamma object. This report distinguishes successful execution of that control in this checkout from reproduction of that control on a checkout with only the nine fresh project objects. Each of the actual nine project modules and the auditor still had their Lean-resolved imports checked against the appropriate fresh objects and pinned external roots. The reviewer finding concerns the regression-test fixture. Root assigned the shared-harness fix to a separate worker and explicitly requested that this exact source and receipt be retained.

## Final local result

The exact-SHA full local gate returned exit code 0. All 58 stages passed. It checked actual resolved imports for nine fresh modules and the auditor, strictly rebuilt nine objects with warnings as errors, replayed all nine with the bundled leanchecker, and checked serialized inventory, actual declaration owner, explicit compiler type and transitive axioms for all 168 declarations. The complete union is propext, Classical.choice and Quot.sound. Both the verifier’s final clean-tree check and a separate migration-ledger check passed. The latter matched all 48 compiler-type digests and owners, as well as all eight retained consumer blocks and both complete parent remainders.

| Module | Owned declarations |
|---|---:|
| ImbalancedChen.Part3FourierModeIndex | 1 |
| ImbalancedChen.Part3CoprimePacketCore | 23 |
| ImbalancedChen.Part3CuspPhaseCore | 7 |
| ImbalancedChen.Part3CoprimePacketCoefficients | 16 |
| ImbalancedChen.Part3PrimaryPrimeSupport | 11 |
| ImbalancedChen.Part3LiteralReciprocalSource | 24 |
| ImbalancedChen.Part3FixedRhoPrimaryFiniteCore | 22 |
| ImbalancedChen.Part3PrimaryDyadicShortEndpoint | 26 |
| ImbalancedChen.Part3PrimaryDyadicAssembly | 38 |

### Local receipts

The complete local evidence is under `/workspace/library-files/p34-proof-work/.lake/p34-primary-dyadic-acceptance/`. The report includes exact commands, per-stage return codes and elapsed times, source and object hashes, pin and executable checks, and resolved dependencies. Each named stage has a complete raw log in the same directory.

- `.lake/p34-primary-dyadic-acceptance/report.json` — SHA-256 `366e18673c585c0af62417a448babf2616b1866c9419693a0891d8dc374ee1aa`
- `.lake/p34-primary-dyadic-acceptance/declarations.json` — SHA-256 `f0309250495247a01ace2554fc3ba2db7825f1c0d741914d4ae7dfb3e7152dbb`
- `.lake/p34-primary-dyadic-acceptance/axioms.log` — SHA-256 `f6431acd13d6a8c6c1d5f9b42a8c5c67a40cb73db430aa67a3307c92f833396a`
- `.lake/p34-primary-dyadic-local.log` — SHA-256 `b2fb23b409a3315ffa5203e52e58a1644df490db6481e35c056c3c7f7fc3d911`
- `.lake/p34-dyadic-final-check.log` — SHA-256 `6840b00031772129d674911102991068e18aa7b43ea767740d30b44738f1675f`

The scoped result is the finite dyadic decomposition and short endpoint. The retained heavy parents and manuscript spectral and original-row identifications are outside this gate. Independent review, external publication and replacement clean-checkout acceptance are controlled by root.
