# P5 literalScale public API independent source review

Verdict: `PASS_EXACT_MINIMAL_SOURCE_VISIBILITY_POSTIMAGE`. Reviewer `n20_acceptance_review` is independent of author `n20_p5_literal_public_api`.

The author freeze `d971d83e4cd8d30f8cdd97632f69bf7cd5e430ec34aeb12cd5759b56c3f6b337` and every listed artifact were independently hashed and matched. I compared the complete 20,929-byte preimage with the complete 20,921-byte postimage. The sole change is deletion of ASCII `private ` at zero-based byte 7409, line 158. All remaining bytes are identical. The postimage SHA256 is `b0580c827fa840432f04c617c1ea7db13fbbfeddecf38f3d945047d2646a08c6`; the preimage remains `cc3ef5f1c7d692d1b062ffb0c2738bf9f43edd87ce98918900367ecec39e6833`.

This exposes `ImbalancedChen.Part5OriginalH430RootIntervalTheta.literalScale_limit` with the existing type `Tendsto literalScale atTop (nhds 1)`. There are no added parameters or hypotheses. All seven imports, all 31 original definitions/theorems, every proof-expression byte, the literalScale definition, and the existing internal caller are preserved. No proof was copied, no generated private name was invoked, and no PNT supplier was added.

The original scalar is `logarithmicIntegral N * Real.log N / N` on Nat physical N. The original proof subtracts the exact `(2/log 2)*(log N/N)` correction from the public true-li leading-one limit. The current edit neither changes literal li nor identifies it exactly with N/log N. The existing scoped mathematical proof review is reused and is not re-signed as new mathematics.

The original manuscript density and marked-normalization requirements were independently checked earlier in `../ACCEPTANCE_CRITERIA.md`: same rho at each precision, physical N, same Q and actual alpha. This source change only makes the already proved scalar limit callable. Same-rho density/distribution, signed Delta, PP, relative own-Theta, aggregation, h34, 430/441, hLower and P5.6 remain unpaid.

The exact allowlist authorizes only this source postimage for publication/use. It does not assert successful elaboration, compilation, recursive closure, kernel replay, transitive axioms, runtime readiness or objects. The declaration's public Lean name differs from its old generated private name, so old private objects or receipts cannot certify the new source automatically. No local Lean/Lake/LSP/nativekernel, project helper, fixture, setup, stage or guard was run. Formal/green credit remains zero.
