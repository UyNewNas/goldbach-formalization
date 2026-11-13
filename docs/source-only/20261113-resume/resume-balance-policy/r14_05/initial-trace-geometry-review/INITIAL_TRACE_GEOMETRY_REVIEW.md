# Arithmetic bound for the complete first trace

The two R2 sources identify and bound the original positive-mark, same-infinity trace on Γ₀(q) for every positive integral level q. This is the arithmetic contribution in Drappeau's proof of (4.30), pages 17–18. The original medium manuscript, §10(v)–(vii) at 9731290e, uses the matching Kuznetsov convention and a single interval and phase across the exceptional m average. The comparison tree is 06f3e98f81031d292c99cee98fd14c78909e3254. Installation uses the previously audited two-prefix arithmetic and prescribed cutoff trace together with the three canonical proof-direction replacements in registry 557270c2 and independent allowlist c1b09d39.

## What is being summed

At j≥0 set L=2ʲ and M=L−1/2. For L≤a≤b≤2L, the same half-open positive-integer interval [a,b) supplies m and n at every q. The contraction total uses conjugate(e(mω)) e(nω) times spectral(q,m,n,Φ(Y·)). Here spectral is literally the sum of the full discrete and all-incoming continuous terms supplied by mass, and the full positive-weight Petersson term holSum. The prescribed trace already performs the matched diagonal cancellation, including m=n. Every surviving geometric modulus k satisfies q∣k, with summand S(m,n;k) Φ(4πY√(mn)/k)/k. Both marks and both signs are those of the identity-frame trace.

For fixed Y>0 a single integral cutoff C>32πMY works simultaneously for both marks, q and ω. For any term in the support, k≤8πY√(mn) and √(mn)≤2M. The looser cutoff used in the proof therefore contains every nonzero term. Positive multiples of q can be written uniquely as qd, including d=q. The finite mark sums then pass through the d sum and are identified with the genuine smoothSum(qd,a,b,a,b,−ω,Y)/(qd). Since kernel(ω) has phases e(mω)e(−nω), the negative common argument is necessary. The absolute value is taken after the signed mark contraction at each level. The inequality 0≤Φ(q/Q)≤1 is the only use of the level weight. The Lean estimate is even quantified over every real Q, including zero with the field division convention. Drappeau uses Q>0.

## Cover and exponent

Write K=πMY and X=16K. The support of a nonzero smoothSum is contained in [(8/5)K,16K]. Four closed intervals [v,2v] with v=K,2K,4K,8K cover it. Their endpoint overlap is harmless for the nonnegative majorant. For Y≥1 and M≥1/2, K≥π/2>1. An integral modulus in a window therefore satisfies v≤qd≤floor(2v)≤2v, and every floor endpoint is at least one. The previously proved factored_initial_mean applies to the entire selected subset of ordered positive pairs, using both true Abel prefixes. The original 1/(qd) and the paid divisor multiplicity are present. Applying broad_initial to the Cartesian product of the arbitrary input level set with the finite d range introduces neither a level count nor a further factor k. This yields Cδ (X L²)^δ (X+L²), with four windows included in Cδ.

Take δ=ε/3 and V=(1+M)(1+Y). With L≤2M, M≤V and MY≤V, one has X L²≤64πV³. Thus (X L²)^δ≤(64π)^δ V^ε. Also X+L²≤(16π+4)(M+Y)M. The resulting Dε is chosen before j,a,b,Y,Q,ω and the arbitrary finite level set S. The conclusion is

$$
\sum_{q\in S}|\Phi(q/Q)\,\mathrm{total}(q,a,b,Y,\omega)|
\le D_\varepsilon [(1+M)(1+Y)]^\varepsilon (M+Y)M.
$$

The argument includes j=0, Y=1, the empty interval and empty level set. Arbitrary finite S supplies the claimed bound in particular on each physical level window. The declared terminal statement quantifies over finite S. It does not export an infinite-series HasSum for the level variable.

## Source selection and analytical scope

The final R2 at fec16688 carries the original Y≥1 hypothesis into broad_initial when applying it to the full product of factor pairs. It was missing at this application in the unpublished 3cad106d predecessor. Independent byte comparison found only the added proof argument. The second module and author report retain their original bytes. The canonical provider registry and its independent review are both bound by their exact final hashes.

No lower estimate for a native complementary transform was used here. To extract the exceptional energy in (4.30) from the trace one still needs the lower positivity comparison, the regular spectral errors and the required control over the actual exceptional parameters. The holomorphic error has its own scoped review. The ordinary Maaß and incoming Eisenstein errors, any necessary uniform spectral cap, the full recurrence, (4.29), the final Pascadi J bound and 7/32 remain outside these two sources. Local elaboration, kernel checks and new accepted leaves were all zero.
