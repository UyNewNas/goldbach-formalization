# Holomorphic corrected window on the physical modulus progression

The selected sixteen sources give a weighted geometric estimate on the physical Kloosterman sums at every positive multiple of the level. They also give absolute convergence of the joint order and modulus series at fixed parameters. The source selection contains 104209 bytes and 166 named declarations. Compilation and kernel verification are pending. The exact paths, blob IDs, SHA-256 hashes and eight registry pairs are in [the source allowlist](HOLOMORPHIC_WINDOW_16_SOURCE_ALLOWLIST.json).

## Relation to the original argument

Deshouillers and Iwaniec start from the **same-observation** Petersson identity (4.4) on p. 258. Their equations (5.2)–(5.4) sum the even weights with an exponential cutoff on the odd order and give both a diagonal and a signed Bessel window. They use an earlier integral involving J₀ and split its Poisson integral. Page 259 makes the angular cut at √(c/N) for short moduli, treats the complementary moduli, and sums the physical progression for (5.5). The argument on pp. 260–261 starts again from (4.8) with a different transform for the Maaß and continuous spectra. [DI p. 258](https://gdz.sub.uni-goettingen.de/fulltext/PPN356556735_0070/00000282?_format=xml) · [p. 259](https://gdz.sub.uni-goettingen.de/fulltext/PPN356556735_0070/00000283?_format=xml) · [p. 260](https://gdz.sub.uni-goettingen.de/fulltext/PPN356556735_0070/00000284?_format=xml) · [p. 261](https://gdz.sub.uni-goettingen.de/fulltext/PPN356556735_0070/00000285?_format=xml)

Drappeau's Lemma 4.6 supplies the comparison with the twisted arithmetic form. Proposition 4.7 states the three spectral inequalities, and its proof starts with the fixed-weight Petersson factor 2πi⁻ᵏ. In the source the positive even k gives i⁻ᵏ=iᵏ. Applying the paper to the two actual observations also requires their spectral trace and coefficient normalization. [Drappeau, Lemma 4.6 and Proposition 4.7, PDF pp. 13–14](https://arxiv.org/pdf/1504.05549v4#page=13)

The sixteen sources supply an alternative derivation for the original holomorphic obligation. They correct the exponential cutoff by a fixed-scale subtraction, derive their circle kernel from the actual complex power series, and pay the long-modulus tail by the resulting vanishing first moment. Thus the selected estimate applies to a specific corrected window. It does not assert DI's printed J₀ formula for the uncorrected window.

## Weight, Fourier projection and constants

Put h=k−1 and t=1/K with K≥1. The identity Wₜ(h)=e⁻ʰᵗ(1−exp(−(h−1)(2−t))) gives Wₜ(1)=0 and Wₜ(h)≥exp(−1)(1−exp(−2)) for 3≤h≤K. Odd orders occur with the explicit odd mask, including its zero at h=1. The complete scalar diagonal satisfies Σodd hWₜ(h)≤exp(−t)/(1−exp(−t))²≤4K². Price k=2 separately on the native basis using the previously supplied single-shell result at j=0, which costs 2/π+32L/(z log(3/2)) times the packet energy. The weighted scalar calculation alone provides no positive lower bound for k=2.

The coefficient integrates exp(ix cos(2πy)) exp(−2πihy) over the unit interval. Its two absolutely summable Taylor series leave precisely k=j+h on integrating over y. The remaining Gamma denominator is j!(h+j)!, the phase is iʰ, and the alternating sign is (−1)ʲ. Consequently the coefficient is iʰJₕ(x). For u>0 the differentiated positive-order geometric series is Z/(1−Z)² with Z=exp(−u−2πiy). Changing variables from y to the angle gives 1/(2π). Integration by parts at 0 and 2π has zero boundary term. The two reflections give Im(Σₕh exp(−hu)iʰJₕ(x))=(x/π)∫wᵤ(y) cos(x cos y)dy on [0,π/2]. For positive x the reality of Jₕ(x) gives the weighted odd projection

    2 Σodd hWₜ(h)i^(h+1) Jₕ(x) = −(2/π)Vₜ(x).

All actual x=4π√m√n/c are strictly positive. The normalization left for a future same-observation spectral identity can be read from the project's existing mixed-frame fixed-weight convention. If that same-observation identity is established with 4πΓ(k−1)Pₖ=δ+2πiᵏΣSJ/c, multiplying by hWₜ(h)/(4π) yields the scalar diagonal divided by 4π and **one quarter** of the selected native geometric series. The spectral weight becomes Γ(k)Wₜ(h). The known mixed-frame trace uses two different observation columns.

## Cost over all moduli

Two independent complex rows range through m=M+i, n=M+j for 0≤i,j≤M, including the two integer endpoints. Each inner double sum is evaluated before its norm. The sign-reversed exponential uses conjugation of both input rows. The derivative and primitive on the quarter-circle supply ∫wᵤ=(π/2)exp(−u), which makes the corrected amplitude v have integral zero.

For positive c<M the cut Δ=√(c/M) satisfies 0<Δ≤1. Near zero the strong positive-frequency estimate applies at cos y≥cos(1), and the two square-root row multipliers together cost at most 2M. Integration by parts on [Δ,π/2] removes the external argument x. The upper boundary vanishes. The derivative bound contains cos y/sin²y, leaving √(cos y)/sin²y after the strong arithmetic bound. The endpoint cos y=0 has zero derivative and calls for no division by its square root. The integral of 1/sin²y is cot Δ, and sin Δ≥2Δ/π. Summing 1/c over the short multiples costs at most (1+log M)/z.

For c≥M the vanishing integral allows cos(x cos y)−1. Its exact second-order remainder introduces the scale parameter s∈[0,1] and two powers of x in addition to the original x. At q=s cos y the coarse two-sign cosine bound costs 12 exp(4π)c times the two row norms. The cubic square-root row factors cost at most 8M³ together. The resulting single-modulus estimate is A M³/c², where A=(π/2)(4π)³ cosh(2)(1+exp(2))·12 exp(4π)·8. The progression with c=z(j+1) and the trace divisor 1/c costs at most 4AM/z. This includes c=M, z>M and M=1.

Let B=[8π/√cos(1)+(π/2)/√cos(1)+π/2] cosh(2)(1+exp(2))exp(4π). The angular constant is the actual function cost(ε)=16B(1+2/ε)²+4A. Its definition fixes it from ε>0 before M,z,t and either row. The absolute series of the native odd Bessel geometric terms is bounded by (2/π)cost(ε)M^(1+ε)/z times the two dyadic row norms.

## Exchange of sums and scope

At fixed m,n let A₀=4π√m√n. The Gamma series gives |Jₕ(A₀/c)|≤((A₀/2)/c)ʰ exp((A₀/2)²)/h!. Every surviving odd h satisfies h≥3. The physical sum satisfies |S|/c≤1, and c=z(j+1)≥j+1. Together these give a summable product majorant proportional to h exp(−ht)/(j+1)². The finite pairs m,n may now be summed and the infinite h,j order exchanged. Its factor exp((A₀/2)²+A₀/2) depends on the fixed frequencies. The uniform norm inequality in the preceding paragraph was obtained independently.

The corrected circle generation reverses one equality at the use of HasSum.congr_fun to match mathlib e4c91783's new-function-equals-old-function premise. The three remaining circle/Fubini postimages are byte-identical to the previous generation. The Fubini registry now points to the corrected circle postimage. The direct Bessel and conjugation closures have 123 distinct existing project modules. Each listed SHA and Git blob has been checked against its file and commit 680fc11a. The arithmetic suppliers retain their separately reviewed 4.33.0-rc1 host source selection.

The outstanding native obligations include the same-observation full-basis Petersson identity at infinity, the Fricke transport to the second actual cusp, the dyadic packet and coefficient conventions on both frames, and the Maaß and all-incoming continuous spectral windows. The selected sources grant zero new kernel credit for these obligations or for the complete three-measure sieve.

