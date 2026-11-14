# S05 independent full-body review: conditionalcritical5

Decision: PASS_SCOPED_CONDITIONAL_MATHEMATICAL_SOURCE, uncompiled. The author freeze is `0861c52b1d3ca2ac1b3b72d5922fb09df194391ec607b08dc8ebe08ab8b06348`. I read all five complete proof bodies and the directly used scalar scale-contraction, prefix-maximum and energy-identification interfaces. All six frozen file records and all five external direct-source records match their raw SHA-256 and byte length. Each of the five Lean files remains byte-identical to the earlier critical-induction draft. No author file was changed.

This is a proof of the actual native critical estimate and original T08 J range **conditional on `positiveHalfSupport`**. The additional premise is not proved. Neither an initial estimate, a recurrence nor a J bound is assumed by the new critical theorem: those first two inputs are the already-reviewed actualpositive6 results, freeze `ddee11b6a8f815518c5b1967f0e74a29be29e016f039df4c6620bd1fedf1a317`, independent allowlist `3b48cf00eb2b75cf3fadd20bef99333b3f14332c00497350600e217209a50edc`. The unconditional full-J status remains false.

## Original manuscript and precise scope

I reread §10(v)–(vii), lines 463–481, of the original medium module at commit `9731290e8f53cffda44129906cde6a965eaa869b`, blob `19f9672bc9b6d455045213c5e23e10433a9569d2`. It asks for the positive m interval and additive phase common to all levels, at infinity, up to X≪max(M,Q²/M). The code uses the existing native infinity coefficients, every exceptional basis multiplicity, M=2^j−1/2, and the actual T08 `pascadiJ`. No cusp-one average, level-dependent phase, or arbitrary-coefficient substitute is introduced.

In the primary proof, the improved interval initial estimate and return recurrence precede a separate square-root weight comparison. The latter is precisely the role of the explicit half-order hypothesis in this implementation. The target range agrees with Pascadi's Theorem J, while the numerical 7/32 input in the medium manuscript is a separate requirement. [Drappeau, Lemma 4.10 and Proof 4.8](https://arxiv.org/html/1504.05549v4#S4.SS2), [Pascadi, Theorem J](https://arxiv.org/html/2404.04239v3#S3.SS4)

The stronger critical theorem quantifies over every common subinterval 2^j≤a≤b≤2^(j+1), including empty intervals. Its final named J terminal specializes to the full original dyadic frequency row and allows any finite subset of the level dyad (Q,2Q]. All real Q>0 and X>0 are included. If the level dyad is nonempty, Q≥1/2; since M≥1/2, the displayed factor [(1+Q)(1+M)]^ε is at most 9^ε(QM)^ε. If Q<1/2 the actual level sum is zero. Thus the harmless 1+ normalization does not weaken the manuscript's intended small-power range.

## The condition and the two genuine weight transports

`CriticalTransport.positiveHalfSupport`, lines 21–22, is the proposition

    for every q,m>0 and every original exceptional slot i at q,
    τ_q,i>1/2 implies ρᴷ_q,i,infinity(m)=0.

It concerns positive coefficients at the original identity frame. It is not replaced by absence of eigenvalues or by a global Selberg assertion. In `transport`, lines 24–46, the premise is used exactly on the τ>1/2 branch to annihilate each positive-frequency row. On the other branch and for 0<Z≤X, (X/Z)^τ≤sqrt(X/Z). Summation preserves all actual levels and slots. The row starts at a>0, so every mark at which the condition is invoked is positive.

`prefix_child`, lines 48–73, assumes B≥H=max(1,M). Then B²/M≥H and the child benchmark is exactly B²/M. For every prefix endpoint u=min(b,n+1), the induction hypothesis bounds the complete level-and-slot energy at that benchmark; the same half-support transport moves it to Y≥B²/M. The source takes the finite supremum only after this whole energy. Its common phase and starting endpoint a are unchanged. The index range contains every nonempty prefix and the empty-row case, so no positive contribution is omitted.

The scalar `child` theorem does not mention the coefficient premise because it compares numerical prices only. The actual recurrence proof calls both `prefix_child coeff` and `transport coeff`. The final terminal first calls `critical coeff`. The premise is therefore present at each analytic use and at the final theorem boundary; it does not disappear through the scalar lemmas.

## Constants are selected before every moving scale

Fix ε>0 and δ=ε/2. Let A,E,X₀ be the actualpositive6 six-window constants at δ, and K its all-positive-height initial constant at δ. These are fixed before j, endpoints, phase and level. Set κ=16π, λ=π/16, A₀=max(1,6A), and use the reviewed scalar `choose_damping` with the final exponent ε:

    D=max(κ²,2κ,κ(4A₀)^(1/ε)),
    T=max(1,D/λ,sqrt(DX₀)),
    c=1+2T²,
    U=K[2(1+c)]^δ(1+2c),
    V=sqrt(D) E·2·6^δ,
    P=max(U,2V).

All are finite and P>0. Since κ>1, D≥κ² also gives D≥1. The damping inequality is 2A₀(κ/D)^ε≤1/2, hence 2(6A)(κ/D)^ε≤1/2. The source chooses P before the `fun j` binder. Neither M nor Q nor an interval, phase, induction depth, or spectral index enters D,T,P. No quantitative constant is extracted from the half-support proof.

The first scalar proof, `CriticalPrices.base`, allows M≥1/2 and 0<Q≤TH. With H=max(1,M), H≤2M and W(Q)=max(H,Q²/M), one gets W(Q)≤cH. Consequently

    (1+M)(1+W(Q)) ≤ 2(1+c)H²,
    Q+M+W(Q) ≤ (1+2c)(Q+M).

Raising the first inequality to δ gives the required H^ε. Since H≤max(1,Q)H, the initial estimate costs at most U N(Q), where N(Q)=[max(1,Q)H]^ε(Q+M)M. This proves the entire base band, including M=1/2, Q below one, and empty level sets. There is no unproved small-Y branch: the imported initial mean already holds for every positive height W(Q).

## Actual recursive scales and each child's price

On Q>TH, set Z=Q²/(DM), W=Q²/M. The actual output endpoints are B_l=2^(l−1)πMZ/Q, 0≤l<6. The proof uses `actual_scales` with mother index b=0; its broader bounds λQ/D≤B_l≤κQ/D remain valid. Applying `recursive_band` with the chosen D,T proves

    X₀≤Z,  H≤B_l≤Q/2,  B_l²/M≤Z.

These follow respectively from Q>sqrt(DX₀)H and H²≥M, from Q>(D/λ)H and D≥2κ, and from D≥κ². Thus W(Q)=Q²/M, W(B_l)=B_l²/M and Z≤W(Q). Both transports are in their allowed direction. Their product is exactly

    sqrt(W(Q)/Z) sqrt(Z/W(B_l))=Q/B_l.

The selected scalar scale-contraction source is `36a64acdb1b5de9b08d2674e52def7ffb246d31a45a651e5ab9f53eb6e5c6222`, reused under old independent allowlist `09c05acd03f065f836ca4e80e540720da2a323b767e17f720f94f586ebeb14cc`. I checked the actual definitions of λ,κ,endpoint, the two transport quotients, the damping conclusion and the normalized price arguments, rather than importing the old report's expository induction as a theorem.

Because Q,B_l≥1 and M≤B_l, the ratio of the transported child price to the parent price is

    A(B_l/Q)^ε Q(B_l+M)/(B_l(Q+M))
      ≤ 2A(κ/D)^ε ≤ 1/12.

`CriticalChild.child`, lines 12–47, implements this using `normalized_contribution` with argument 6A. It multiplies by the nonnegative P, M and powers, then cancels the positive B. Hence every actual returned prefix contributes at most P N(Q)/12. This bound is for the full prefix energy after summing all levels and slots, not for separately chosen maxima at different levels. The six genuine outputs cost at most P N(Q)/2. The earlier two Mellin signs and their integral moment were already incorporated into the imported A; they are not omitted and must not be charged a second time.

## All additive errors and the real-scale induction

The second scalar price lemma assumes M≥1/2, Q≥1, D≥1 and Z≥1, all proved on the recursive band. It uses

    (1+M)(1+Z) ≤ 6MZ ≤ 6Q²,
    MZ/Q=Q/D≤Q.

Therefore the exact all-paid recurrence error is at most 2·6^δ N(Q). The left parent transport adds sqrt(D), so its final cost is at most V N(Q)≤P N(Q)/2. This bound includes all ordinary principal, incoming, holomorphic and lower-order charges previously consolidated in E. It introduces neither a logarithm nor an extra Q^δ on the recurrent prefixes. Using δ=ε/2 is valid here because the product in this recurrence is (1+M)(1+Z), with no additional (1+Q) factor.

For fixed j, the source defines `good Q` simultaneously for all allowed a,b and every real ω. It proves `good Q` for 0<Q≤2^n TH by induction on n. The zero case is precisely the base-band estimate above. In the successor case already-covered Q use the induction hypothesis; otherwise Q>TH. Since B_l≤Q/2 and Q≤2^(n+1)TH, every B_l lies in the previous band. For each prefix a≤u≤b, the same induction hypothesis applies to [a,u), with the same lower dyadic bound and u≤b≤2^(j+1). The six child bounds and the additive bound give exactly P N(Q). Finally, unbounded powers of two cover any positive real Q. No natural-number rounding of Q and no induction hypothesis at the current level is used.

## Four mothers and the 24-window distinction

The scalar imported geometry covers all 24 endpoints at a **shared** test height Z(Q)=Q²/(DM):

    B_bl=2^(l−b−1)πQ/D,  0≤b<4, 0≤l<6,
    λQ/D≤B_bl≤κQ/D.

All these endpoints satisfy the same geometric descent inequalities when Q>TH. The selected critical proof, however, uses the six b=0 terms of a single entry recurrence. Its A₀=max(1,6A) budget must not be described as a direct contraction for a sum of 24 terms. Such a sum is not formed in this proof.

The original mother (Q,16Q] is recovered without weakening its range: after completing the dyadic theorem, apply it separately at Q_b=2^bQ for b=0,1,2,3. These four disjoint level dyads comprise the entire mother, including its upper endpoint. A common final X≤A max(M,Q²/M) satisfies the same allowed condition at each Q_b. The resulting constant is at most

    C Σ_(b=0)^3 2^(b(ε+1)) ≤ 4·8^(ε+1)C

times the same [(1+Q)(1+M)]^ε(Q+M)M. The interval and phase remain common. This gives the complete sixteenfold-mother estimate as an explicit finite deduction.

Each independent dyadic induction at Q_b uses its own Z_b=Q_b²/(DM)=4^bZ(Q), with child endpoint 2^(l+b−1)πQ/D. These are not the shared-Z endpoints B_bl above. Their descent is relative to their own mother Q_b, which is sufficient because each dyadic theorem has already been proved uniformly for all level scales. No larger mother's child is fed into the smaller mother's induction. This distinction accounts for all four mothers and all 24 applications without silently spending a six-window budget on 24 edges. No new literal 24-edge Lean induction theorem is claimed.

## The actual J terminal and retained condition

`NativeJFromHalfSupport.original_range_of_half_support`, lines 20–64, applies `critical coeff ε` to the actual full dyadic row. The inspected `full_window` identity is definitional, and `zero_frequency` simplifies the zero Mellin wave to the existing T08 `pascadiJ`. There is no provider substitution at this identification. Positivity of X^τ times a squared norm permits arbitrary subsets S⊆(Q,2Q].

The critical benchmark max(H,Q²/M) dominates the requested max(M,Q²/M). For fixed A≥0 and X≤A max(M,Q²/M), X/W≤A. The final source uses the already-proved positive-row 3/4 transport with the bounded factor max(1,A)^(3/4), selecting C=max(1,A)^(3/4)P. This does not replace the half-order transports inside the induction: their unbounded scale ratios have already used `coeff`, while A is fixed before all moving parameters. The norm price is then enlarged from max(1,Q)H to (1+Q)(1+M). Thus the exact terminal range and quantifier order are preserved.

No mathematical gap was found in these five conditional proof bodies or their inspected source interfaces. The selected code contains no new axiom, sorry/admit, hJ black box, or initial/recurrence premise. This source check cannot rule out future elaboration or dependency-installation failures. It does not audit every transitive axiom.

The missing native half-order coefficient provider remains substantive. actualpositive6 proves only the threshold 3/4, and its T25 arithmetic range does not imply the threshold 1/2. Accordingly this allowlist marks conditional critical/original-J-range proof true, but unconditional full J, proved half support, global Selberg/gap, 7/32 and P3.5 false. Formal credit and leaf changes are zero. No local Lean, Lake, LSP, helper, fixture, proof execution, Git mutation, download, or CI was used.
