# 30d medium 独立源码验收

结果：5 项窄 SOURCE_REVIEW_PASS；已读 16 份最终 Lean、3736 行与五组最终 REGISTRY/REPORT。93 个登记本地路径/哈希对全部匹配。原始完整 task_complete=false，local_step_complete=true，batch_target_source_complete=false；compiled=false，kernel_verified=false，formal_credit=0。

此前 30c 的 medium.json、medium.md、IMPORT_MAP 已按下列最终 raw SHA 锁定；本轮未改前批。

- `goldbach-proof-continuation/docs/source-only/20261028-resume-30c/reviews/medium.json` — `4889cc7db0fcde1a0ddbe04dcbda6c8f463ae7f3cc5551f76a5f6b187ce5df32`
- `goldbach-proof-continuation/docs/source-only/20261028-resume-30c/reviews/medium.md` — `b10a4c5962ce142c92ae34be0062fd61a8255d8c82825b0f8552f9b8a99f4095`
- `goldbach-proof-continuation/docs/source-only/20261028-resume-30c/IMPORT_MAP.json` — `a28313bfc288dfda72169b41348046d613c963cba0c1093cb5c266cc3ee1f2e5`

只按实际源码和原稿核查数学逻辑、条件、循环假设、范围及原始哈希；未编译、未跑 checker、未安装导入、未查额度、未派子代理。没有作完整依赖闭包或外部 API/内核验收。

## medium_s1 — SOURCE_REVIEW_PASS

Actual lambdaTrim owned three-q-piece FixedBlock atlas, original Y=Q1*D, polynomial caps and entire-d same-paperPsi S1 remainder with fixed logarithmic power 38.

已核查：

- OwnedAtlas:44-134 uses actual physical ownedSlice equality, choices-to-divisors injection, prime-support coprimality and primitive gamma zero terms. Repeated prime powers are retained. Rough upper endpoints added by a closed FixedBlock have zero actual lambdaTrim.
- OwnedAtlas:136-224 partitions the complete natural paperPsi q carrier into three disjoint integer pieces at Q1 and 2Q1; unique ownership and arbitrary complex finite-sum equality preserve both boundary points in their lower piece.
- OwnedAtlas:226-291 constructs actual blocks using original atom, lambdaTrim, alpha and paperPsi/Fourier profile. Inert singleton frequency fields are unused by S1 and are not claimed as E3 frequencies.
- PolynomialCaps:17-167 derives occupied D,R<=physicalCap<=4*x^2, block physicalCap<=192*x^5, qCap<=3*x, roughCap<=8*x^2 from MediumAdmissible geometry; fixed-cap logarithms become one sourceLog.
- BlockBudget:35-157 pays all active d at once using the original ordinary divisor mean, yielding kernel<=96*U^2*sourceLog^38/(Q1*D). Lines188-223 select one common-m constant before all atoms/keys/pieces/d, then sum actual remainders. Lines179-184 give exact atlasPureS1=atlasMainS1+atlasRemainder.
- BlockBudget:225-242 exposes the original numeric z via the shared exact half-integer receiver. It changes the discrete receiver only; analytic z stays original.

仍保留条件：

- MediumAdmissible and sigma>=0; occupied original keyBank; actual primitive gamma support; original positive U,V,Q1.
- The receiver-parametric atlas is connected to original prime cutoffs via strictReceiverCutoff(z); the exact predicate bridge requires original z>=0.

实际缺项：

- Complete one overall carrier/Fubini theorem from medium_s3 samePsiS1_cast_eq_literal to atlasPureS1, including the common-m sum, all q pieces, inactive-d zero terms and rough endpoint extension.
- Full original S1 principal cancellation, S2/S3 assembly and final medium/spectral return remain OPEN.

最终快照：

- REGISTRY `fcf558d8d09c6eac6aa8d0afc94e2cb770ee3d2ed52b44a6d4942bf51b07220e`
- REPORT `dddb98f565494a3e2db156b097052342ec2cd1179603793e57b0f6974da50d19`
- `Part3OriginalOwnedS1BlockBudget.lean` (258 行) `eb8bacaef3aeee85b558cdee0eabb1ab443f1e2b5a6433899c336ce420ce7132`
- `Part3OriginalOwnedS1PolynomialCaps.lean` (170 行) `3ec25f19e61bb13a455c82e7b01acf7f34e13d4750d4a8ab19a3fbbd7970d72b`
- `Part3OriginalSamePsiS1OwnedAtlas.lean` (294 行) `8fc590e94e81d973528ad9cfd27fd7d5946d64d901de1b674dcf43c200d6748a`

## medium_s2 — SOURCE_REVIEW_PASS

Actual same-profile collapsed smooth-modulus deletion packet, including the complete fixed-D mixed family with genuine Shiu calls and the original 1/D saving, plus exact kept-Lambda/key-fiber dictionary.

已核查：

- MixedFamilyGeometry proves subset H by actual q*d*r=l representation multiplicity<=tau(l)^2, independent second rough harmonic mean, free n2<=2N and modulus level Y; no H or progression-output budget is assumed.
- FullMixedCollapsedTail retains all mixed independent r,s bins. Actual nonzero three-tail terms force a nonzero literal Lambda tail, so the pinned valuation lemma places a physical modulus in the original collapsed filter under the explicit physical cap gate.
- FullMixedTailPayment invokes the actual held half-Rankin/divisor/Mertens collapsed-tail proof, whose A-before-x0 order was inspected. Its whole-family V0=M*N^2/Q1 result is separate and is not used to absorb D.
- FixedDMixedTail:34-115 uses one family containing D<=small<2D and ALL mixed r/s, proves actual s2Carrier full=kept+tail and derives q*small>=Q1*D before summation. Lines138-282 return the genuine Shiu subset packet and final arbitrary-log tail at M*N^2/(Q1*D), with C,X preceding every positive D.
- FixedDMixedTail:286-321 states direct full-minus-kept actual coefficient deletion and exact mixed-owner image partition of that same fixed-D family.
- ReceiverLambdaBinding uses the shared exact original cutoff bridge, then identifies original kept Lambda with a SUM of actual lambdaTrim fibers over all matching keys. It does not collapse two independent key sums to a single common key.

仍保留条件：

- Original PrimitiveShiuTauBoundary 1 (1/10) (1/10), with its native natural X,H,q,reduced-class gates; foundational existence remains deferred.
- MediumAdmissible; x above the chosen uniform threshold; D>0; physicalCap<=floor(x^(4/5)). The latter must still be derived by the actual original range(7) caller.
- The lambda/key-fiber dictionary requires original z>=0 and positive original support; no no-boundary-prime premise is introduced.

实际缺项：

- Instantiate the physical cap/smooth-level gates from the original actual atom range(7).
- Bind the exact same-key literal quadratic S2 of medium_s3 to these fixed-D kept/full coefficient carriers, preserving independent key cross terms, all q/m windows, mean restoration and deletion identities.
- Complete the original principal/Poisson S2 and subsequent medium return; current packet is not full task completion.

最终快照：

- REGISTRY `b942b0ffd25e7f30624945b4ac63d85ffb3833188ab4d198ec1b9f48b7b39249`
- REPORT `c03a4bd32d8ef645f06e35f79755461cb05b62b6d5cd32948269a06542f05330`
- `Part3OriginalS2FixedDMixedTail.lean` (324 行) `cffe489bceaf3af7a7599544aaf30f2d0656f7b681c690954cb04801e191cea5`
- `Part3OriginalS2FullMixedCollapsedTail.lean` (260 行) `13675965040a2cf961a2b41657f555d8b78ef74c736815208286fc215e7aeb25`
- `Part3OriginalS2FullMixedTailPayment.lean` (173 行) `d2cc2b3e9474a48185f73ea81033135329e0a7d740d635717cfcba1a205ccfc0`
- `Part3OriginalS2MixedFamilyGeometry.lean` (241 行) `31ae99e2f40197e3a599d42307c326570828ce62572aeff3ed6c1abc686f5a56`
- `Part3OriginalS2ReceiverLambdaBinding.lean` (140 行) `03b7e690dae05f06ac97efe9922208e664a90c94f14108a3d226a4c258c8b31e`

## medium_s3 — SOURCE_REVIEW_PASS

Exact original-cutoff receiver, insertion of the same positive paperPsi on q and m before Cauchy, literal shared-q/d/m S1/S2/S3 expansion and actual divisor-bounded beta L2 payment.

已核查：

- ReceiverCutoffArithmetic:23-47 proves p<=z iff p<floor(z)+1/2 and z<p iff floor(z)+1/2<=p for every natural p and z>=0. Lines102-158 preserve prime-power factors and prove original labelDW=(actualD,actualW) at this exact receiver, including zero separately.
- ActualPsiPreliminaryDispersion proves paperPsi=1 on original q1/m supports, inserts both weights in the actual LINEAR source, and enlarges only its nonnegative quadratic carrier. This preserves original Cauchy order rather than deleting independent q/d cross terms from an already squared W.
- The literal paired sums use actual lambdaTrim and alpha with shared q,d,m but independent (r,n1)/(s,n2). Exact complex/real-part identities give quadratic=S3-2*S2+S1, using the same paperPsi throughout.
- The original common-m unit condition factors into actual alphaCoprime mass and the m unit gate. General beta remains its actual L2 factor; only a finite betaDivisorL2=sum tau(m)^(2B) payment is proved, with gamma1L2 explicit.
- Lines323-355 define original inclusive-z retained source and prove its equality to the actual same-profile blocks at the translated receiver. No exceptional boundary-prime condition or change of numeric z is used.

仍保留条件：

- General exact identities/Cauchy use actual L2 and do not require beta one-boundedness. The finite divisor-payment corollary assumes the original explicit norm(beta(m))<=tau(m)^B.
- Original retained source receiver equivalence assumes z>=0; fixed original trim and dyadic key ownership remain explicit.

实际缺项：

- Connect literal S1 to the complete S1 atlas via one full Fubini/endpoint theorem.
- Connect literal S2/S3 to deleted/restored and clean/nonclean Poisson carriers with the complete q/m windows and all correction terms.
- Derive actual asymptotic betaDivisorL2 and gamma1 moments, pay trim/exact-product corrections and final arbitrary-log errors.

最终快照：

- REGISTRY `111f8ce63aac5dd9846852ad1fc4475f3f883fb5db37874c5c5174223fbc7cd4`
- REPORT `b8c575d6b01a37c6e08fddddef9260ecc8461443c656b11c9f29821cc7bb3b05`
- `Part3MediumActualPsiPreliminaryDispersion.lean` (357 行) `954936990cb8dd0f3029289697dcf43bd38a41bdd02ccf5325da271a1810f131`
- `Part3MediumReceiverCutoffArithmetic.lean` (161 行) `5575c681f5a7d5cf7530d6082a6fe56f8a52f14cb38ef0bf543b313f400e233d`

## medium_variance — SOURCE_REVIEW_PASS

Actual r-filtered crude variance, fixed-log low/high-conductor recombination and weighted (14) under explicit numerical support gates; finite original principal Gram diagonal insertion.

已核查：

- CrudeWeightedVariance removes the actual nonnegative principal mass, bounds same-residue compatible pairs using progression occupancy and original bounded alphaCarrier, and obtains actual Var<=2*N^2/ell for ell<=N=floor(2U), without a tau loss.
- The native fixed-order harmonic divisor mean pays the second weighted-Cauchy factor. HighConductorLogMargin constructs R=ceil(log(x)^b), controls its integer windows and uses strict Q<=N*x^(-delta) to absorb all fixed logarithms; no x^epsilon energy premise is used.
- LowConductorLogChoice chooses b and the fixed divisor-moment order before the SW exponent. WeightedFilteredBDH then directly recombines original UniformAuxiliarySW and the 30c actual native primitive large-sieve high return, with C,x0 preceding varying atom,Q,r.
- The final weighted theorem is for the ACTUAL filteredVariance/weightedVariance, not an abstract BDH placeholder. Original hSW and named native primitive large-sieve are the inputs; no desired variance conclusion is assumed.
- PrincipalGramVarianceBound identifies the original centeredPaperRow with actual filteredError on reduced residues. Exact finite Gram normalization and Cauchy give card(R)*sum |eta_r|^2*Var/(phi(ell*r))^2 for arbitrary signed eta; common period ell*product(R) is actually constructed and never treated as an analytic error scale.

仍保留条件：

- Weighted (14): fixed w natural and A,delta>0; original MediumAdmissible family and UniformAuxiliarySW; Q,r>=1; Q<=N, Q<=x, Q<=N*x^(-delta).
- The physical caller still must set its actual Q (for example floor(8Y)) and derive all numerical gates; these are not assumed outputs of the desired variance theorem.
- Gram bound keeps actual finite rough R of positive integers, actual centered row, arbitrary eta and original totient denominators.

实际缺项：

- Prove the physical medium Q/support strict-margin caller from original geometry.
- Insert actual lambdaTrim at strictReceiverCutoff(z), rough support/cardinality, reciprocal-totient levels, q,d repetition and ordinary r-divisor means to close full (15).
- Complete actual S1/S2/S3/principal cancellation and four-chart/spectral return.

最终快照：

- REGISTRY `1b83cd7828a0712f3cb60ed6e5d3a2f0ed5bb4a0503be12f90456b4b451d0b51`
- REPORT `1fc85dd77dd621dee00c29673d8ff9132f35c967ccfd7c60e4c9ccda1c50779b`
- `Part3ActualCrudeWeightedVariance.lean` (260 行) `688df86d2d23f2c13906b24ae31f06af8a57cba41574929d91228be3a61c5378`
- `Part3ActualHighConductorLogMargin.lean` (162 行) `61a2dab17b43d770c52b35b0accedd7232356b86980485876a5c343825a3f3f4`
- `Part3ActualLowConductorLogChoice.lean` (98 行) `cf51b0e0ed88738ef4df2065ca6c44e4b931f4bc549c7570a18f271edc29e249`
- `Part3ActualPrincipalGramVarianceBound.lean` (165 行) `853343c2b6ed6b00ca9d800aa217afef6c7219e6d0cda1a3eb99f54b7585d0ef`
- `Part3ActualWeightedFilteredBDH.lean` (172 行) `f61767cc5f3120a04e909f33414f083700828a80632bd690e85bf8b3529a654c`

## medium_poisson — SOURCE_REVIEW_PASS

Actual original-Lambda raw-box clean/nonclean E2 partition, explicit fixed-d family constraints and licensed clean CRT phase/normalization dictionary; no full preliminary-W to E3 identification.

已核查：

- Actual inclusive prime-power Lambda has d/w coprimality on nonzero support. actualBlock assigns original Lambda and the constructed paperPsi/Fourier profile, retaining arbitrary supplied physical geometry rather than claiming an actual geometry constructor.
- RawBox is partitioned exactly into clean and nonclean complements. The full term retains physical lcm, actual CRT residue, signed h and both coefficient pairs. Only the actual clean subcarrier uses rough cross-coprimality to deduce gcd(d*w1,d*w2)=d and lcm=q*d*w1*w2.
- PreliminaryBlockFamily enforces atom equality and block.d=the summation small for every indexed d. Global clean/nonclean partition and normalization V/L=(V/d)/(q*w1*w2) are proved without forgetting the outer 1/d.
- Clean CRT compatibility and inverse licenses are derived from original carrier gates. Exact modular divisibility yields equation (21), preserving the reciprocal slow phase; the final typed phase bridge reuses production canonical_inverse_modEq rather than assuming equal inverse representatives.
- Original inclusive Lambda equals the translated strict receiver UNTRIMMED d/w fiber under z>=0. This is explicitly distinguished from a single lambdaTrim/windowed key, and from the full preliminary source.
- Explicit actual q weight and same-profile Fourier factor are exposed. Clean coefficient/phase dictionaries are proved, but the whole clean summand/sum has not yet been assembled as (V/d)*typed E3.

仍保留条件：

- Clean equation (21) requires the actual clean carrier and all original CRT/inverse conditions, now derived on that branch. It is not generalized to the entire nonclean raw box.
- An actual full geometry/atlas constructor, h-window and separation/trimming identification are not supplied by PreliminaryBlockFamily alone.
- The original cutoff bridge requires z>=0; no no-boundary-prime exception is added.

实际缺项：

- Bind actual preliminary Cauchy lambdaTrim/common-d source and all windows, key sums, separation and frequency trims to rawBox/globalPreliminaryE2.
- Assemble the full clean raw summand and sum with the complete typed E3 array and original E2 outer weights.
- Retain/classify/control all nonclean general-D/root branches; finish enlarged q support, coefficient l1, Abel/window and final analytic return budgets.

最终快照：

- REGISTRY `91ad55072ef86ef2d4b1fbc9e84fbb9795828aa07857357fdc468666704dac6f`
- REPORT `0377d20524a0b7beb52f8fdc90346da0a0508c8189ef184e57c58bab9f6a57ee`
- `Part3OriginalGevreyPreliminaryE2Partition.lean` (501 行) `6434249e9d4c2c8a7a8f6069fb2021b9ddde94250f2c8a87ae05a41f78561513`

## 跨模块边界

- Original inclusive p<=z/>z and strict receiver p<c/>=c agree at c=floor(z)+1/2 for z>=0. Numeric analytic z is retained.
- Exact original untrimmed Lambda fiber, kept-Lambda sum over key fibers, single-key lambdaTrim and complete common-key quadratic carrier are distinct interfaces. Only proved equalities are credited.
- S2 fixed-D family preserves its original 1/D uniformly; the separate V0 whole-family estimate does not pay a variable D.
- Full actual samePsi S1-to-atlas Fubini, S2/S3 windows/mean restoration, physical variance caller/full (15), preliminary-W-to-E2/E3 and all nonclean branches remain OPEN.

仍未证明完整 medium 或最终主定理。未发现可据此宣称的原稿反例；当前缺项是上述实际源码连接、数值门和后续解析预算。SOURCE_REVIEW_PASS 不产生内核信用。
