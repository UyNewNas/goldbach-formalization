# FormalAlgebra — independent pinned-API source review

Verdict: `PASS_EXACT_PINNED_API_SOURCE_REPAIR`, for the single 8,804-byte postimage SHA256 `202b5832455324f3dd9c060c7ef9e29563e540bb042b095859cd7f25524df528`, Git blob `7727bfdccb9d76b7dc3789e188426ee11cc8a772`. Reviewer `n20_acceptance_review` is independent of author `n20_weil_failure_review`. Author freeze: `61f5de19bd6d7fd4e8ca9310cd610b0d9cd84e4e7d8869235bf899f21ae0ce73`.

This source review is separate from the already frozen R4 runtime review. It uses that review's exact actual failure and does not repeat its acceptance. The 8,645-byte preimage SHA256 `68e2f08d38b65dd7bec6ba58998849059ffd479fff9e51d39ad3948e7b687915` matches the actual `WEIL_STAGE` row, including its Git blob. FormalAlgebra was invoked once and failed with seven derivative-application errors plus two dependent rewrite errors. Those facts justify investigation of the source API; the generic outer no-build error is not the mathematical diagnosis.

## Exact source changes and declaration correspondence

All 17 author-frozen files independently match their lengths and SHA256. I read the complete preimage, postimage and diff, and independently reversed the exact transformation back to the complete original bytes. The change consists only of adding explicit `ℂ` to the 13 existing `d⁄dX` applications and replacing the unavailable named lemma with one local `hlog_base` proof. No new global declaration, notation, definitional wrapper, hypothesis or import is introduced.

At pinned mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, `PowerSeries.derivative` takes its coefficient ring explicitly, and `d⁄dX` is exactly that notation. Every affected expression differentiates a formal series in `ℂ⟦X⟧`. The explicit ring therefore restores the intended formal derivative, rather than introducing a new operation or a stronger premise.

Two declaration conclusions necessarily change their surface syntax:

| Declaration | Preserved full mathematical statement | Necessary head change |
|---|---|---|
| `derivative_logOf_mul_self` | For the same implicit `f : ℂ⟦X⟧` and sole hypothesis `constantCoeff f = 1`, the conclusion is `D(logOf f) * f = D(f)`. | Two derivative applications explicitly instantiate ℂ. |
| `coeff_derivative_KSeries` | For every same `K : ℕ → ℂ` and `n : ℕ`, `coeff n (D(KSeries K)) = K(n+1)`; no hypotheses. | One derivative application explicitly instantiates ℂ. |

All other 13 complete declaration headers are literal matches. All three public imports, 15 global names, original KSeries/quadraticL definitions, module/public exposure, namespace, license, generating-identity hypothesis, index ranges and recurrence/spectral-root conclusions remain unchanged. Full exact before/after headers are in `IDENTITY_AND_DECLARATIONS.json`. Because the old source does not elaborate at the fixed pin, this is intended mathematical/source correspondence, not a kernel-equivalence assertion between two successfully elaborated declarations. It would be false to describe the entire patch as preserving all header bytes or as changing proof expressions only.

## Local logarithm identity

The fixed-pin Log source defines the same formal logarithm and provides `deriv_log`, but not the later `derivative_log_mul_one_add_X`. The later upstream snapshot is comparison evidence only and is not imported or treated as an upgraded dependency. All five supplied official-source snapshots were independently hashed; their computed Git blobs match the recorded fetch identities. I made no duplicate remote fetch.

The new local goal is exactly `D(log ℂ) * (1+X) = 1`. After pinned `deriv_log`, the series has coefficient `algebraMap ℚ ℂ ((-1)^n)`. At degree zero the product coefficient is 1. At degree n+1, `mul_add`, the pinned `[simp] coeff_succ_mul_X`, `[simp] coeff_mk`, ring-hom simplification and `pow_succ` reduce the coefficient to the image of `(-1)^(n+1)+(-1)^n = 0`. The same `ext (_ | n)` syntax is used in the pinned Basic source itself. Thus the finite coefficient argument preserves the same algebraic identity and introduces no number-theoretic assertion.

The existing proof then substitutes f−1 using the existing `HasSubst` proof from constantCoeff(f−1)=0. The pinned `substAlgHom_X`, ring-hom multiplication/addition and `coe_substAlgHom` give `(D(log ℂ)).subst(f−1) * f = 1`. The unchanged chain rule and derivation subtraction reduce D(f−1) to D(f); associativity/commutativity yields `D(logOf f)*f = D(f)`. The later recurrence coefficient rewrites remain the original ones. This is a static proof/API review; only a real compiler can establish that the tactics elaborate and that no further errors remain.

The local hlog_base is a repair of an omitted old-pin API derivation for an existing identity, not a new assumption, changed mathematical scope, or identified manuscript gap. The review approves no changes to the other 33 Weil sources or any cache/guard/producer/qualification protocol.

## Acceptance boundary

This exact source may be published/used as the scoped repair candidate. It has not been compiled, kernel-replayed or axioms-audited. No object/reuse AL, Stage A, full34, native6/J or new green follows. The existing five successful preceding modules retain only their previously reviewed compile observations; their physical/current-input object qualification is a separate task. No automatic recompile of those five or of all original19 is authorized here.

No local Lean/Lake/LSP/nativekernel, project helper, fixture, guard, stage, setup, artifact execution, download, Git/GH write or CI dispatch was performed. Source AL is independent from runtime evidence and old source ALs. Formal/green credit is zero.
