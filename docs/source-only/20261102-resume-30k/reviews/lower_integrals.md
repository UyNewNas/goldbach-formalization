# Independent K U8/U9 integral source review

Reviewer: /root/j_review_p5_errors. Retained assignment: gpt-6-astra / xhigh; runtime model identity was not separately queried. Only the two lower_integrals review files are written. J and all author sources remain unchanged.

Both frozen packets receive a narrow **SOURCE_REVIEW_PASS**. This is an independent mathematical and static source assessment, with compiled=false, kernel_verified=false and formal_credit=0. Neither complete h8/h9 nor the saved endpoint certificates receive acceptance. No compiler, build, CI, finite mathematical execution, numerical certificate replay, Git, quota query or subagent was used.

## Exact frozen packets

The companion JSON records exact source, registry, report and registered dependency/reference pins, modules, imports and declaration inventories. All 33 registered U8 records and all 39 U9 records match their raw SHA-256 and byte counts. This metadata audit does not confer independent review of every transitive dependency.

| Packet/file | Raw SHA-256 |
| --- | --- |
| u8_upper/P5OriginalU8ScalarProducer.lean | a06becfdeaeff531d363efeaa77dc45d9d91fc0deac4def5e0fa1a50be1e9e1d |
| u8_upper/P5OriginalU8MidpointEnclosure.lean | b5c6c4a9f0b86e1aad5d9a617643922ff010bcb3126a2b1450e0866dd3367a83 |
| u8_upper/P5OriginalU8MidpointEndpointPort.lean | c25f22c8d69eac2dff88a998b6d472200099a603bc4b73e64f103ed66685a417 |
| u8_upper/REGISTRY.json | 642066e7344f74dbcf95e303da6173549a851e606a3bf0ad6dc9afe64d644e0d |
| u8_upper/REPORT.md | e9fe6d7a7a5bf9914407874dc381c37418a29432be8c410478fef5cfaef56b32 |
| u9_integral/P5OriginalU9MidpointCurvature.lean | 2d6eb1cc7360c1e95255b4651e92ecd78a8f5be7f53005a8baede37313608d22 |
| u9_integral/P5OriginalU9MidpointIntegral.lean | 032959d52a21113c5291510a352fd692ded896b21b21db3ff55307e946c0cf65 |
| u9_integral/P5OriginalU9UpperOnlyStrictSlot.lean | 3b8aa1e665a263acd71b9f0cfb0efca77df6f8333c742b0ab00ca4717da175f0 |
| u9_integral/REGISTRY.json | 2a004a225755b49dac6a4280d5d6b2f7849d63e6b29b53a904cbc750893835d6 |
| u9_integral/REPORT.md | f3bee14b3125a96bfa2c16192413ecd686fe6ce464d2b38375fa0f9c68f03eab |
| u7_sharp/P5OriginalSignedMidpoint.lean | 507dee4fe27c1fb4b6bdc4ba095a1fde3651a4ca215fa4381fbc4bafe89b0e69 |

All paths in that table are relative to docs/source-only/20261102-resume-30k. The six new modules and shared midpoint module are not installed at their declared ImbalancedChen targets. No inherited verification is claimed.

## Shared signed midpoint application

I directly read the shared source and each application's premises. Both anchored primitives have derivative f minus a nonnegative quadratic kernel times f''. Applying FTC on the left and right halves cancels the midpoint f' terms. The total kernel mass is (r-l)^3/24, including the degenerate l=r case. Thus lower and upper bounds for the signed second derivative give the corresponding signed integral remainder bounds. The argument does not replace f'' by an absolute value.

Each U8/U9 application supplies the actual first and second derivatives, continuity, and a bound holding at every point of the closed cell. The resulting cell bound is width times the midpoint-value bound plus width^3/24 times the corresponding curvature bound. Reviewer /root/j_review_h7 separately reports a narrow pass for the same frozen shared source in reviews/u7.json and reviews/u7.md. Neither that review nor this one accepts numerical curvature ranges or saved outputs.

## u8_upper — SOURCE_REVIEW_PASS

The scalar source's original_integral_eq_logIntegral (line 31) uses the existing U8 Fubini identity and the general inner primitive to obtain

    f(t) = log(2-3t)/(t(1-t)),  417/5000 <= t <= 1/3.

This is the original U8 domain. For L=log(2-3t), R=1/t+1/(1-t), the source proves f=LR and the genuine derivatives

    L'=-3/(2-3t),       L''=-9/(2-3t)^2,
    R'=-1/t^2+1/(1-t)^2,
    R''=2/t^3+2/(1-t)^3,
    f''=L''R+2L'R'+LR''.

The endpoint guards establish positivity of t and 1-t and 2-3t>=1 throughout the closed interval. The derivative and continuity arguments therefore apply at both cell endpoints. The mesh identity (line 165), exact cell sum (line 210), and 1024 partition (line 221) identify the complete original partition, with node 417/5000+k((1/3-417/5000)/m).

In the enclosure source, inverseBounds_contains (line 32) derives its guards from positive endpoints and cell membership. logarithmBounds_contains (line 45) uses q=3-3t>=2, with the lower log bound at the right endpoint and the upper bound at the left. secondBounds_contains (line 99) combines the inverse and log boxes using signed interval arithmetic to enclose this actual f'' over the whole cell. It assumes no finite sample, curvature estimate or computational certificate.

panel_enclosure (line 147) supplies the shared theorem with these actual scalar derivatives and interval bounds. original_integral_midpoint_enclosure (line 197) sums every cell; original_1024_midpoint_enclosure (line 210) explicitly specializes to 32 logarithm terms and 1024 panels. This is a symbolic rational enclosure of the real integral.

The endpoint port retains the exact saved rational U8/K0 upper value and exposes upperEndpointCheck as an unproved comparison premise. Its conditional endpoint and upper-only envelope theorems preserve the existing U8Envelope. The lower side of the stored two-sided interval is not assumed proved by this packet, and it is not needed by the retained upper-only adapter.

Remaining OPEN: the complete aggregate inequality proving upperEndpointCheck, authentication of the archived Q80 execution and selected endpoint, original common density and strict PP suppliers, and complete h8.

## u9_integral — SOURCE_REVIEW_PASS

The curvature source differentiates the original density

    f(x)=log((1-x-d)/d)/(x(1-x)),
    a=19/125, b=d=59/250.

The log slope is -1/(1-x-d), and its curvature is -1/(1-x-d)^2. source_positive (line 36) covers every denominator over the full closed interval. The reciprocal derivative formulas and product rule then yield the actual density curvature; this is not a certificate-named surrogate.

The reciprocal boxes at lines 129–131 use the correct monotone endpoints for 1/x, 1/(1-x), and 1/(1-x-d). logQuery is 1+(1-x-d)/d>=2, and the decreasing log uses the right endpoint for the lower bound and the left endpoint for the upper bound. curvatureBox_contains (line 201) derives its signed whole-cell bound from those boxes.

midpoint_cell_enclosure (line 34 of the integral source) applies the shared theorem with those actual derivatives and curvature bounds and the existing directed lower and upper midpoint value suppliers. The full summed enclosure (line 86) uses the exact original mesh and integral identity. The 1024 theorem (line 126) is universal in the number n of log terms, so includes n=32 without evaluating any sum.

The ordered-domain theorem (line 133) uses the original squared-terminal kernel 1/(t*u*w^2). Its reduction to the scalar integral does not silently substitute the unsquared kernel. The cost bound (line 143) scales by the positive original K0=67619/10000.

The upper-only strict-slot source retains the unchanged original envelope and fixed k=currentK+1/100000000 in [0,K0]. Its branch theorem passes the same nu, r, e, retain, cap and rho to the J strict-branch reduction and retains its repeated-coordinate C+1 error. The endpoint upper comparison, density, licence, scope and strict PP hypotheses are explicit. It proves a reduction, not those hypotheses.

Remaining OPEN: the complete aggregate comparison with the saved upper endpoint, the archived Q80 execution, original lower/upper endpoint authentication, common density and strict PP, and complete h9. This packet also does not prove the independent Simpson lower certificate.

## Final U9 Mathlib metadata correction

The accepted final REGISTRY and REPORT hashes are those above. The three sources below are present read-only snapshots under u9_integral/provenance/mathlib-e4c91783, referring to revision e4c91783ca8e6a7c693ae624ade32fd22d4e43c1. Their recorded .lake installation targets were checked and are absent. Static inverse, product, quotient and power derivative API shapes support the intended route. No installation or import-resolution success is claimed.

| Upstream file | Snapshot SHA-256 |
| --- | --- |
| Mathlib/Analysis/Calculus/Deriv/Inv.lean | 728a55b0c00e62076563a9018c801d6f61ff491ab040b923c7235879060f3477 |
| Mathlib/Analysis/Calculus/Deriv/Mul.lean | 9eaf8d222c347ea647939daa68fac11edeb7c2572719246ce03d43cb04c94b44 |
| Mathlib/Analysis/Calculus/Deriv/Pow.lean | e800a35ad837f14ee41c68f967af9e27222efa06288c6a6c08efc1af50a550c5 |

## Archived execution boundary

The original manuscript, producer, sharp-switch proof, fixed-point backend and saved data were read as sources. The mathematical real expressions and all 1024 cells are accounted for. The exact rational log enclosures have 32 terms and a proved tail; they are not an authenticated replay of the archived backend's intermediate Q80 rounding.

The saved U8 upper value is 4904703865205402441361491/1208925819614629174706176; the saved U9 upper value is 3937512077512215599969887/1208925819614629174706176. Their presence in JSON and endpoint definitions does not prove their relation to the new rational aggregate. No comparison was numerically evaluated.

The original factors, constants, retained affine envelope and -1/4 root weights are preserved by these conditional adapters. The two local passes therefore remove only the reviewed scalar, derivative, whole-cell curvature, complete partition and analytic signed-midpoint obligations. They do not close the original endpoint, common-density, strict-PP or full-supplier obligations.
