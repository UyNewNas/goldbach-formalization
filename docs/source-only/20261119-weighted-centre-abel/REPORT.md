# P1.4: exact cancellation of weighted upper centre-prime Abel correction

Baseline: `c544229a323c7c2d8eb09fb3633570e29bd271d4` on verified `chatgpt/p1-full87-centre-interval-bridge-20261119-2110`. Source commit: `294788bb9f3c0c514b405a9a374268501e0f9875`; source blob: `9b4970d4c026049911b77a9b0b90d9b2c65bb00f`. New branch: `chatgpt/p1-full87-weighted-centre-abel-20261119-2210`. Scope: this proof packet only, 268-line new candidate.

## Actual mathematics (candidate, not Lean-validated)

The previous finite identity separated the *unweighted* anchored reflected prime discrepancy into the primitive additive carrier and a literal centre divisor count. It is **false** that the latter count vanishes on each arbitrary interval (prior N=70,b=13,a=5 diagnostic). Here, unlike that unweighted interval, the ORIGINAL room weight `actualRoomBetaWeight` is zero unless `Nat.Coprime (a * (p :: pre).prod) N`. If the reflected integer `P = N-a*b` belongs to `chenPrimePrefix N` and divides N, its primality gives positivity and `a*b <= N`. From coprimality of `a*b` and N, self-subtraction gives `Nat.Coprime P N`, contradicting `P | N`. Hence **pointwise weighted** centre step is zero: `w_b(a)*centre_b(a)=0`.

Finite Abel summation and endpoint weight zero imply the FULL original weighted centre jump invoice (anchored at the strict original lower gate) is **exactly zero** after summing all real beta jumps, although individual unweighted centre intervals can be positive. This yields the finite candidate identity:

`originalRoomAbelCorrection = originalRoomCarrierJumpCorrection`.

Therefore an authenticated same-rho primitive-carrier interval estimate E at every true jump endpoint would give the original signed PLUS-beta prime discrepancy bound `E * originalRoomBetaVariation`, **without separately charging C * variation**. This replaces the previous E+C local bound, not an additional credit or a second payment.

Same full modulus `b=(p::pre).prod`, original `actualPrimitiveRosserRoom`, true `actualSmallRosserPlus` sign, strict lower/upper quotient gates and all actual jump endpoints. The original fifth/sixth ordered occurrence and frozen parent propagation is in upstream candidates and is not claimed newly closed here. No external estimate, source density, global H_N sum or final reserve proved.

## Performed checks / limitations

- GitHub source file readback: blob `9b4970d4c026049911b77a9b0b90d9b2c65bb00f` matched local Git blob.
- Static inspection: 4 public candidate theorems, no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` proof escape.
- Independent finite arithmetic model: 12,500 seeded cases, zero Abel/weighted-centre mismatches; 1,506 cases contained **nonzero unweighted centre intervals**. These do not kernel-validate the Lean text or certify the original producer.
- `lean --version`, `lake --version`, `elan --version`: not found (127). No matching toolchain locally. Container 4GiB memory cap. `git ls-remote` network/DNS failure (128). GitHub connector used for authorized source-only branch write.
- Verification: SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No kernel replay, transitive-axiom audit, independent review, CI launch, pin change, main/master update, or resource expansion.

## Remaining obligations

Elaborate and repair this exact candidate with frozen imports. Authenticate same-rho primitive AP jump-interval input and its exact full-b primitive normalization, uniformity and source. Prove E times actual beta variation summed with original fifth signed masses and sixth List occurrences is paid against H_N. This cancellation does **not** remove lower-half centre or modulus-prime errors. Complete ordinary integral, saved87 certification, RAW/BOTH/rank9 changed/tagged coverage and two independent compiler/density reserves. P1.4 stays YELLOW.
