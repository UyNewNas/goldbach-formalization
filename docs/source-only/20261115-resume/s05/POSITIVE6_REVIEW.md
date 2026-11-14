# S05 independent mathematical source review: actualpositive6

Decision: PASS_SCOPED_MATHEMATICAL_SOURCE for author freeze `ddee11b6a8f815518c5b1967f0e74a29be29e016f039df4c6620bd1fedf1a317`. All eight frozen file records and five external direct-source records were independently rehashed, including lengths; all match. The six Lean files are byte-identical to the earlier `native-fixed-mark-order` drafts. The selected paid-return dependency is R2 `d80da5e655ddf99f8ee15655048b1279ee7b519927717a29a797d9127d1980f3`, source `f8b012e5afc0e35422a4662d0152eaaff01fd99a40443573a09b66c91de95e81`, separately reviewed in this directory. The original paid-return missing import is not silently inherited.

The newly established scope is: the original positive infinity coefficients with τ>3/4 vanish; the complete positive common-interval initial mean holds for all Y>0; the actual T08 J has its stated initial range, also the full requested range when Q/M is bounded by a fixed constant; and the complete six-window prefix recurrence has only additive ordinary-spectrum prices. No unconditional full J at unbounded Q/M is proved.

## Original objects and primary comparison

I read medium §10(v)–(vii) at commit `9731290e8f53cffda44129906cde6a965eaa869b`, exact module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`. The required m row is the common positive interval and common phase at infinity; its full weight range is X≪max(M,Q²/M). The current source retains the actual native basis multiplicities, fixed infinity frame, τ=2√(1/4−λ), and ρᴷ=2R. Every squared native row therefore has the factor four already accounted in the paid trace extraction. A complete interval-energy sum is over the original slots, not over a new filtered spectral family.

Drappeau separates the initial bound (4.30), return bound (4.29), and square-root transport in Proof 4.8; the remark following that proof identifies the Selberg input for the latter step. Pascadi's Theorem J uses the identity infinity frames and the longer X range. The distinction between a complete recurrence and a completed critical induction therefore agrees with the original statements. [Drappeau §4.2](https://arxiv.org/html/1504.05549v4#S4.SS2), [Pascadi Theorem J](https://arxiv.org/html/2404.04239v3#S3.SS4)

## Fixed marking: arithmetic growth and spectral extraction

The fixed-mark arithmetic interface is the previously reviewed T25 majorant and Euler summability, independent allowlist `b945abb4b5616e063b5b885de8a5bcd9393ba09e0faf970798a8d023a0eb3a45`. I read its review and checked the actual imported `summable_majorant_price` and `physical_le_majorant` declarations. No new Weil estimate is assumed. For fixed m>0 and δ<1/4,

    S_m,δ = Σ_(k≥1) B_m(k)k^(−2+δ) < ∞,
    |S(m,m;k)| ≤ B_m(k).

`FixedMarkTraceGrowth.geometry`, lines 24–88, uses the actual scalar same-infinity trace with m=m and test Φ(Yx). A nonzero arithmetic term is q|k times S(m,m;k)Φ(4πYm/k)/k. The actual cutoff support lower endpoint 1/2 gives k≤8πmY, including the boundary. Put v=1−δ>0. Then

    |S(m,m;k)|/k ≤ B_m(k)k^(−2+δ)k^v
        ≤ (8πmY)^v B_m(k)k^(−2+δ).

This is a nonnegative termwise majorant, so dropping q|k is legitimate at this arithmetic step. The absolute trace identity and the summable majorant give |spectral_q,m,m|≤(8πm)^v S_m,δ Y^v for every q and Y>0. The q-level spectrum is not changed after this estimate. The constant depends on fixed m and δ, which is sufficient.

`PositiveMarkOrder.slot_floor`, lines 84–116, takes T_q=max({0}∪{τ_q,i:i exceptional}). The family is finite at fixed q and every strict exceptional order is below one, so T_q<1. Applying the prescribed native test floor to that entire band gives common c_q>0 and Y_q≥1 for all slots at this fixed quotient. At diagonal m,m, conjugate(R)R=|R|²; every exceptional summand has nonnegative real part for Y≥Y_q. A selected slot is consequently bounded below by c_qY^τ|R_q,i(m)|² inside the real part of the entire complementary sum. The proof does not apply positivity only to a selected slot while ignoring the rest.

`others`, lines 45–82, isolates q from the nonnegative dyadic norm bound on (q/2,q]. It chooses a dyadic frequency block containing m and the genuine singleton [m,m+1), at phase zero. The full principal and incoming norms are O_q,m(1+log²(2Y)); the full holomorphic norm is O_q,m(1). The complete trace split thus pays every unwanted sector before extracting the slot. The principal t=0 endpoint and the all-channel continuous integral are inherited from the already-reviewed complete regular price; no term is removed by a sign assumption. Those fullregular12/cubic6 proofs receive no repeated credit here.

For τ>3/4, `high_positive_zero`, lines 118–160, chooses v=(τ+3/4)/2 and δ=1−v, hence 3/4<v<τ and δ<1/4. Absorbing the logarithm into Y^v and taking the real part of the exact four-sector identity gives

    c_q|R_q,i(m)|²Y^(τ−v) ≤ A_m,δ+D_q,m,v

for all sufficiently large Y. If R≠0, the left side tends to infinity. Therefore R=0, and `FullPositiveLevelSwitch.rho_zero` converts this to the actual ρᴷ=0. All fixed-(q,m) constants disappear in this coefficient identity. One may then quantify over every q,m without needing a uniform-in-m Euler bound. This is the essential reason a fixed-level floor does not contaminate the later moving-level constants.

The temporary static concern about multiplication direction at PositiveMarkOrder:150 was resolved against pinned mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`: `mul_le_mul_iff_left₀` cancels a positive right factor. Its next `mul_assoc` rewrite has the required shape. This is an inspected API match, not a compiled theorem claim. [Pinned definition, lines 270–274](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Algebra/Order/GroupWithZero/Defs.lean)

## Actual high slots and all-positive-height initial estimate

`row_zero` annihilates the high row for every common phase and every real Mellin twist because all its marks satisfy m≥a>0. `zero_slot` is stronger than vanishing of a squared row: it permits an arbitrary two-mark multiplier W(m,n). The conjugated first native coefficient already vanishes at each positive mark. It therefore annihilates both actual physical input and reflected high slots, even though the reflected transform depends jointly on m,n. `outside_zero` and `high_zero` kill the genuine finite complex high sums before taking norms.

The identity `all_weights` restores the complete native interval energy from the retained τ≤3/4 sum: omitted slots have zero row, rather than being declared absent. Inserting these identities into the R2 paid initial and recurrence leaves the full exceptional parent and no high residual on either leg. The constants are now those of the one fixed cap T=3/4, chosen before all moving levels, marks and phases. No conclusion is drawn about negative coefficients, other frames, or absence of the corresponding eigenvalues. In particular `globalSelberg` is neither assumed nor proved.

For X,Y>0, transport is proved term by term using the support just obtained:

    E(L,Y,ω;a,b;t) ≤ max(1,Y/X)^(3/4) E(L,X,ω;a,b;t).

It is valid at every positive-start interval and arbitrary twist t. The quantitative initial theorem itself has t=0; this review does not enlarge its statement to a new arbitrary-twist initial estimate.

For any ε>0, the source applies the paid initial theorem at δ=ε/2. For Y≥Y₀, the geometric part and L(Y)(Q+M^(1+δ))M are bounded by a constant times [(1+M)(1+Y)]^ε(Q+M+Y)M. In the additive part, M^(1+δ)≤M(1+M)^δ and L(Y)≤P(1+Y)^δ; all small powers stay in this allowance. For 0<Y<Y₀, the proven X=1 short-interval bound is 32C_sieve(Q+M)M; the transport costs at most Y₀^(3/4). Thus the stated C=max(32C_sieveY₀^(3/4),K(1+2P)/c) works before j,a,b,Q,Y,ω. The common dyadic length is M=2^j−1/2≥1/2. Empty rows and j=0 are covered.

For fixed A≥0, the T08 initial-region theorem applies this result to the entire original dyadic row and then dominates any subset of levels by positivity. With X≤A(Q+M), ε/2 in the initial estimate and U=(1+Q)(1+M), the inequalities 1+M≤U, 1+X≤(1+A)U and Q+M+X≤(1+A)(Q+M) give exactly the displayed terminal constant. If Q≤BM for fixed B, max(M,Q²/M)≤max(1,B)(Q+M), so the bounded-ratio corollary follows. No parameter that must stay fixed is allowed to grow with Q.

## Six physical outputs, all additive costs, and four mothers

The full recurrence has B_l=2^(l−1)πMY/Q, l=0,…,5, and the four input shoulder endpoints A_v=2^(v−2)Q. Let P=Q+M+MY/Q, Z=2+16π, W=Z+1. Every B_l and A_v is at most ZP. With δ=ε/2 and U=(1+M)(1+Y), every one of the six lower-order costs Y^δ(B_l+M)M is at most U^ε WPM. Every one of the ten ordinary-plus-holomorphic prices (B+M^(1+δ))M is at most U^δ WPM. The logarithmic allowance is at most L_δU^δ, so their product costs U^ε, not an extra unbudgeted power.

After dividing by c, the exact choices in `six_window_mean` are

    A_ε=K/c,
    D_ε=(6K+40D L_δ)(3+16π)/c.

The 40 is the exterior factor four times the ten genuine dyadic charges. The six lower-order costs supply 6K. No logarithm or small-power factor multiplies the returned prefix maximum. The maximum is taken after the whole original level-and-slot sum, with one common endpoint; at a<b its index set contains every nonempty prefix, and the omitted empty prefix has energy zero. At a=b the only prefix is empty.

For the mother (Q,16Q], use Q_b=2^bQ separately, b=0,…,3. Then C_b=C/2^b and B_bl=2^(l−b−1)C, C=πMY/Q. The resulting 24 child endpoints lie between C/16 and 16C, with covering dyads inside (C/16,32C]. Each reflected test keeps dQ_b in its denominator. One may sum all four inequalities with the same constants; equal endpoint values from different mothers retain their multiplicity. The exact two-sided ordinary-plus-holomorphic bill and the damping endpoints were checked in `REGULAR_PAID_REVIEW.md`. This four-entry conclusion is an elementary deduction, not a claim of a newly formalized 24-window declaration.

## What remains unpaid

The coefficient identity above concerns τ>3/4. The separate critical induction explicitly requires, for every original level, exceptional slot and positive integral infinity mark, τ>1/2 ⇒ ρᴷ=0. This provider is absent. The prime term in the reviewed T25 series is 2p^(−5/4+δ); its present summability argument only permits δ<1/4. An epsilon renaming cannot improve its coefficient threshold to 1/2. Neither finite exceptional support at each fixed level, the initial estimate, nor the complete six-window recurrence proves that stronger statement.

I read the conditional critical terminal to check the boundary: its original-range theorem takes `coeff : positiveHalfSupport`. It may be discussed or separately reviewed as conditional, but receives no unconditional full-J credit from this allowlist. The critical files themselves are outside this positive6 selection. The manuscript's 7/32 requirement is also separate. Existing mathematical literature may furnish stronger spectral results; no realization of such a provider on these native coefficients is supplied by this frozen package.

Classification: the old paid import is a repaired formal-expression omission; the four-mother extension and explicit finite-family floor are accounted elementary deductions; the 1/2 coefficient provider is a substantive remaining gap. The selected six sources contain no new axiom, sorry/admit, hJ input, recurrence hypothesis, or global spectral-gap hypothesis. This is a mathematical and static source pass, with zero formal credit and zero leaf closure. It is not elaboration, compilation, kernel checking, or a transitive-axiom audit. No author source, repository, or external service was mutated; no Lean/Lake/LSP/helper/fixture or proof execution was run.
