**saving19_moments — SOURCE_REVIEW_HOLD for the pinned import chain.** The new local physical mass, weighted means, max-top range and first-moment arguments pass mathematical source review on their stated inputs. One concrete inherited proof-script blocker prevents acceptance of the complete source chain. The original P2.6.simplices28918 task remains OPEN. Compiled=false; kernel_verified=false; formal_credit=0.

Reviewer: `/root/k_review_moments`. This review is independent of the author and applies only to the frozen delivery below.

| File | SHA256 |
|---|---|
| P2OriginalSaving19SimplexMoments.lean | `b6013daa273742797688325fbda8f7f20d305e7a52ba1cb8d78e310bb7d8488a` |
| P2OriginalSaving19MomentFloorConsumer.lean | `71cb35db43b7ccfe0340a60223e080407607869c11bf75b06542bf4c5c0a1d2d` |
| REGISTRY.json | `04758b92a4fc0fb71e5bbe6182d4da59a2aea3421cfd03d64340e172728073be` |
| REPORT.md | `79e9470d838fd582f3ba5b27a1e94e435048195b09877248673605690ce8bbf8` |

The inherited blocker is at line 124 of `P2Winner9ActualEightSimplexMoment.lean`, SHA256 `2a511a7246bf9dd54d79649c171c34cf741ca4a0fbd10b2701ba42e6e615239e`, in `actualMomentN_eq_nested`. After `simp_rw [monomial_cons]`, the left side is the integral of `t^(ms 0) * monomial ...`, and the next `change` requires `t^(ms 0) * actualMomentN ...`. The intervening `rw [← integral_const_mul]` has the wrong direction. The inspected Mathlib API at `MeasureTheory/Integral/Bochner/Basic.lean:288-290` states `integral(r*f)=r*integral(f)`; the forward rewrite is needed. This is a static source/API finding, not a compiler result. The held predecessor was not changed. The issue does not contradict the canonical monomial formula, but the pinned source chain requires repair/refreeze and later elaboration.

The local mathematical check uses the actual saving19 source: `R=A(t1+t4)`, `M=A(t2+t4+t8)-10^-6`, `g=M-R`, and factors `(R-S8,M-S8,t1,...,t8)`. The A23/s23_low history minorant is not substituted for either cap. The factor 4, cutoff 53/13824, mask 138, c=49044063/25000000 and K=8452171/1250000 remain unchanged. The manuscript at lines435-449 has no Chen quarter or ordering factorial. The `Winner9` import supplies a generic canonical eight-simplex theorem; its inspected analytic chain imports no unequal-seed 11026 row data, `SimplexData`, or floor family.

The core normalization is substantive. The proof derives barycentric first moments `1/9!` and second moments `(1+diagonal)/10!`. With `J=abs(det L)` and `G=sum(g_i)`, affine transport gives

`integral_T(g)=J*G/9!=physicalVolume*G/9`,

`integral_T(g*l_j)=J*(G*sum(l_j,i)+sum(g_i*l_j,i))/10!`.

The invertible map supplies J>0, and the stated G>0 permits cancellation. The normalized mean is therefore `(sum(l_j,i)+sum(g_i*l_j,i)/G)/10`, with diagonal multiplicity two retained. The source comparison and new-cap interpolation preserve the constant negative buffer because the same nine weights sum to one. The physical support is the actual affine image of the canonical simplex. The witness's ambient `physical_jacobian=1` is not mistaken for a unit simplex determinant.

`MomentRow.massEncoding` and `meansEncoding` are finite equalities with determinant/vertex expressions. They do not assume integral semantics. `row_mass_semantics` and `row_means_semantics` derive the checker inputs hMass and hMeans from the new integral identities. The archived encodings themselves are still unproved, and no actual `MomentRow` family is constructed. `higherPowerMoments` explicitly retains the internal integral equalities for degrees 2-6; this review gives no moment-certificate credit for those fields.

`vertexTop` is the maximum over the same nine physical vertices. Vertex PhysicalRows and affine interpolation give positive factors, nonnegative gap and the exact top bound throughout the support. Compactness gives the needed logarithm, reciprocal and power integrability. Positive gap mass normalizes the genuine weighted probability. The cutoff supplies the strict range margin `q=1-cutoff/top<1` without changing the producer's top. The first moment `E_g(1-factor/top)=1-mean/top` follows from the proved weighted factor mean; its finite rational encoding is the remaining field.

The Q80/Q96 consumer matches the original adapters and engines: degree-six log gaps, downward Q80 factor floors, their sum, the degree-three exponential polynomial, then downward Q96 rounding for the complete row. The author's `max(old,new)` is retained, and nonnegative Jensen gaps establish oldFloor<=newFloor. The consumer remains conditional on degrees 2-6. Its aggregate fixes only the thirteen count slots `[56,144,2938,427,2864,56,113,2799,2842,3693,2017,4369,6600]` and proves a sum of row floors is below a sum of true simplex integrals. It does not prove that an arbitrary supplied family is the archived one or that its integral sum is bounded by J.selectedSaving.

I read K README/TASKS, both complete new modules, current J floor/geometry reports and relevant source, the held analytic APIs, original geometry and moment adapters/engines, and the original thirteen geometry and moment witness schemas. All 309 registry-listed source/dependency/reference/API/witness pin occurrences match the current raw bytes. This checks identity, not the witness mathematics. Original witness bytes are present. No producer, determinant, recurrence, stored-floor test, count lemma, numerical sum or finite decision was executed.

The exact remaining obligations are:

- Construct and authenticate the original 28,918 typed rows, their ordered vertices, invertible edge maps, PhysicalRows and positive gap sums; bind saved mass, means, maxima and first moment to the vertex formulas.
- Prove the actual duplicated-node degree 2-6 moment evaluator, including common-denominator scaling and `binomial(9+k,k)`.
- Bind all archived Q80/Q96 integers and the same-family endpoint `283388722705335806564439/2^96`. The previous full bound `69876938299079768108917/2^94` is replaced; only the increment `3880969509016734128771/2^96` is additional. The two full bounds cannot be added.
- Prove correct-cell inclusion, proper-wall nullity and within-cell almost-disjoint ownership, then bridge to J.selectedSaving. A sound disjoint inner union suffices for the lower-bound direction, but is not supplied here.
- Preserve the common policy, old gains and both reserves, then attach the density/compiler and all22 ledger.
- Repair/refreeze the inherited source blocker, install the held dependencies, and obtain elaboration/kernel validation.

No new K mathematical defect, circular mass/mean assumption, new axiom, manuscript contradiction or 11,026 substitution was found. Only this review pair was written. No compiler/build/CI, numerical replay, Git operation, subagent or quota call ran.
