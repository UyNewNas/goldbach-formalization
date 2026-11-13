# The additive exceptional price in (4.29)

For each ε > 0 and fixed band 0 < s ≤ T < 1, the modulus of the Mellin-modulated positive kernel integral, including its native 1/cos(πs/2) denominator, is bounded by C(T,ε)(Yˢ + Yᵋ), uniformly in the Mellin frequency. The threshold for Y depends only on T and ε. The main Yˢ term has no factor growing with Y.

On s ≥ ε/2, sin(πs/2) ≥ s charges the denominator to ε alone. The two actual Bessel cores stay bounded on their compact order band. On s < ε/2, use the earlier estimate C(1+log(4Y))Yˢ. Both the logarithm and Yˢ are bounded by constants times Y^{ε/2}. The small-order contribution therefore enters the additive Yᵋ term. [Drappeau, proof of (4.29)](https://arxiv.org/html/1504.05549v4#S4.SS2)

`native_row_price` applies this estimate inside the actual reflected cutoff with D = dQ and preserves the native ρᴷ coefficients and the exterior cosine. With the common phase ω and fixed dyadic positive block, the two squared rows on the right have Mellin frequencies −t/2 and +t/2. Their density is the modulus of the actual angular Mellin transform of Φ, whose previously verified source estimate decays as (1+t⁴)⁻¹. Both original row sums remain inside the real integral. The factor 1/(2π) from Mellin inversion and 1/2 from the product-to-squares inequality enter the constant. T08's factor-four convention remains applicable when translating these rows to R.

This row estimate applies to each native slot in the prescribed band. A single band covering all moving levels, the two uniform regular error estimates and the scale induction for Theorem J remain outstanding. All three Lean sources are uncompiled.
