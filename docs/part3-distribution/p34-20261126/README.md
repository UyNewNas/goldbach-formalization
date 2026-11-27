# P3.4: literal packets, primary arithmetic and exact dyadic assembly

Three manuscript-facing sub-scopes are implemented, independently reviewed and verified. The code is submitted through [draft PR #8](https://github.com/UyNewNas/goldbach-formalization/pull/8), branch `codex/p34-kernel-20261125`. **P3.4 as a whole remains incomplete.** The genuine original-data closure and spectral coefficient connection are still required.

The manuscript is the [1106 analytic appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703/paper/release-20261106/en/analytic-appendix.tex), frozen at `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`. This delivery reuses existing proof bodies and original finite objects. It introduces no substitute `OriginalData` or external spectral foundation.

## Accepted scopes

| Scope | Exact accepted GitHub source | Modules | Successful stages | Audited declarations |
|---|---|---:|---:|---:|
| Literal coprime packet, actual fixed-height cusp pairing and scalar phase product | `145be87ff0a88914b607baa2a330bc88105a08d6` | 13 | 70 | 167 |
| Actual finite primary arithmetic and ABL arithmetic licences | `e84c5a1c2f70f983de7bafc80472fa2d2eb947d0` | 4 | 43 | 63 |
| Exact dyadic source/beta/energy assembly and short endpoint | `e84c5a1c2f70f983de7bafc80472fa2d2eb947d0` | 9 | 58 | 168 |

The scopes overlap. [The checked union](ACCEPTED_SCOPE_UNION.json) contains **19 distinct modules and 294 distinct declarations**. All 104 repeated records agree in every recorded field. The declaration count includes definitions, private helpers and generated constants; it is not a count of new mathematical theorems. No single new nineteen-module kernel run is claimed. The earlier seven-module cusp receipt is historical evidence within this development, not another disjoint set to add to these totals.

Every accepted scope has strict warning-as-error compilation, Lean-parsed import provenance, bundled `leanchecker` replay for each listed project module, complete serialized/defining-module inventory agreement and transitive-axiom checking. The only allowed transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. Lean is frozen at `4.33.0-rc1`, compiler commit `62eed1db4d67327ec8120be05f1a1b0847d74561`; Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, with the original complete manifest unchanged. External dependency objects are pinned cached inputs, not a newly rebuilt external kernel closure.

## Mathematical progress

**Original packet and actual cusp sections.** The existing `CoprimePacket` keeps its beta, multiplier, positive level, residue coprimality and zero branch. Its signed coefficient and original two mode phases are preserved. The scalar phase identity leaves exactly the remaining cusp phase, and the pairing theorem applies it to the actual Fourier integral at positive height. See [packet acceptance](PACKET_ACCEPTANCE.md) and [the phase source](../../../ImbalancedChen/Part3OldformCuspPhase.lean).

**Arithmetic from a genuine source witness.** The new membership endpoint obtains the signed quotient, positive natural index, `(n, |a|*nu)=1`, `(|a|*nu,z)=1`, and supported cofactor one from the existing carrier and its computed primary fibre. The beta endpoint uses nonzero beta to obtain an actual witness first. It does not put the desired arithmetic conclusions into new hypotheses. Its cofactor labels are natural numbers. See [primary acceptance](PRIMARY_ACCEPTANCE.md) and [the two endpoint proofs](../../../ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean).

**Exact dyadic decomposition and the short endpoint.** The existing primary/sign/dyadic key partitions the original finite source and beta. The squared-norm decomposition is exact and incurs no block-count loss. With the original positivity and nonzero-coefficient conditions, the output length `L=Y/nu` is at least `1/2`; when `L<1`, the nonzero natural frequency is `1`. The code uses `U` for this output scale `Y`. See [dyadic acceptance](DYADIC_ACCEPTANCE.md), [assembly source](../../../ImbalancedChen/Part3PrimaryDyadicAssembly.lean) and [short-endpoint source](../../../ImbalancedChen/Part3PrimaryDyadicShortEndpoint.lean).

The source-move ledgers preserve 15 packet, 57 primary and 48 dyadic declarations and their original provenance. The primary proof bodies are retained. The dyadic unit preserves 42 bodies and records six pinned Lean API or simplification repairs. Existing public statements remain unchanged; the two promoted private helpers are explicitly documented. The retained heavy parent consumers are not covered by these lightweight compilation scopes.

## Clean-checkout verification and final review

The final repair source is `e84c5a1c2f70f983de7bafc80472fa2d2eb947d0`, tree `fca71215e562bfe8ee5a48c0de3d59589a94b2e2`. [Publication mapping](PUBLICATION_MAPPING.json) verifies full tree equality with the independently reviewed local commits.

P3 task `5e2f28aa60a64f3dbd7b5ea1db7a0e06` succeeded with exit 0 in 283.236 seconds. It ran the primary and dyadic gates in **two separate clean worktrees, each starting with zero project `.olean` files**. They ended with exactly four and nine project objects respectively. Only the pinned external dependency cache was shared. The [task record](fresh-cloud-task.json), object inventories and raw archives preserve these facts.

The review found that the previous parser-regression positive control needed an old cusp object outside these two scopes. The repair builds two temporary Init-only fixtures and uses the actual Lean parser with a fixture-only search path. Actual theorem-import validation remains unchanged. The final repair also makes both verifier modes enforce the expected HEAD and baseline ancestry, while explicitly recording any dirty source-only preview. Five focused regression cases passed. The historical README digest is handled by a separate [revision-labelled presentation mapping](README_PRESENTATION_SUPERSESSION.json); old evidence is not rewritten.

[Whole-branch review](WHOLE_BRANCH_REVIEW.md) records the original findings. [The final scoped re-review](FINAL_HARNESS_REVIEW.md) closes all four findings and independently confirms both fresh P3 receipts. No further repair or rerun is pending within these accepted sub-scopes. [Source reuse at the fixed revision](SOURCE_REUSE_AT_FIXED_SOURCE.json) distinguishes the two changed harness files from unchanged Lean, audit and configuration bytes. The thirteen-module packet receipt is reused at its exact original source rather than relabelled as a new run.

## Evidence and reproduction

| Evidence | Contents |
|---|---|
| [Packet report](packet-cloud-report.json) / [archive](packet-cloud-verification.zip) | 70-stage accepted packet run; 73 original files |
| [Primary fresh report](primary-clean-cloud-report.json) / [archive](primary-clean-cloud-verification.zip) | 43-stage run from an empty project-object directory; 47 files |
| [Dyadic fresh report](dyadic-clean-cloud-report.json) / [archive](dyadic-clean-cloud-verification.zip) | 58-stage run from an empty project-object directory; 62 files |
| [Evidence manifest](EVIDENCE_MANIFEST.json) | File sizes and SHA-256 hashes for this delivery |
| [Harness repair](FINAL_HARNESS_FIX.md) / [regression archive](final-harness-regressions.zip) | Preserved red/green parser and provenance evidence |

Each verification ZIP has a separately named archive manifest binding every member. The original primary cloud receipt and original dyadic local receipt remain available under their original names. The failed first packet inventory and cancelled earlier dyadic task are retained and receive no acceptance credit.

At a clean checkout of the accepted repaired source, with the frozen toolchain and pinned dependency cache available:

```sh
python3 verification/verify_p34_primary_arithmetic.py \
  --expected-head e84c5a1c2f70f983de7bafc80472fa2d2eb947d0 \
  --output-dir .lake/p34-primary-clean-acceptance

python3 verification/verify_p34_primary_dyadic.py \
  --expected-head e84c5a1c2f70f983de7bafc80472fa2d2eb947d0 \
  --output-dir .lake/p34-dyadic-clean-acceptance
```

The independent clean-cache evidence used different worktrees for the two commands. `fresh-cloud-task.json` preserves the exact setup checks and executed command. The packet's exact-source reproduction command is in `PACKET_ACCEPTANCE.md`.

## Remaining work

[The remaining integration boundary](REMAINING_BOUNDARY.md) names the genuine `FixedBlock`/`OriginalData` closure, actual Fricke and completed-Eisenstein suppliers, the identification with normalized spectral `R(n)`, and the oldform/regular-trace assembly. The fixed-height integral and scalar phase cancellation do not establish the oldform spectral relation. Existing accepted P3.1 and P3.5 interfaces remain available for reuse when their actual hypotheses are supplied.

The restored-P3 source search and incremental audit are preserved; no repeated broad search or new external theorem formalization was used to fill an unavailable source attachment. These results warrant acceptance of the listed sub-scopes only. The P3.4 parent and its unresolved source-only board leaves are not promoted to green.
