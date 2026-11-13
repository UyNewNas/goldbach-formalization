# The smoothed arithmetic term of (4.30)

These four Lean sources restore the two Mellin weights, the original test function, and the denominator on the arithmetic side of Drappeau’s initial estimate. They consume the modulus mean of the same physical phase-weighted Kloosterman sum. The cutoff is the common Φ of the previous switched-row source. [Drappeau, Proof 4.7](https://arxiv.org/html/1504.05549v4#S4.SS2)

`abel` expands the actual wave at an integer m in [a,b) into one boundary coefficient at b and differences indexed by a≤i<b. The coefficient at i multiplies the prefix [a,min(b,i+1)). Since |d(x^it)/dx|=|t|/x, all coefficients together have absolute sum at most 1+|t| when 1≤a≤b≤2a. `twisted_initial_mean` applies this twice. The prefix coefficients are independent of the summation modulus. Separate frequencies s,t cost (1+|s|)(1+|t|), and the estimate has the same epsilon constant as the previously proved prefix bound.

`smooth_initial_mean` uses angular Mellin inversion of Φ(Y·4π√(mn)/k) with measure dt/(2π). The phase (4πY/k)^it has modulus one, and the other two factors are the same m^it/2 and n^it/2 waves with half-frequency t/2. Finite-sum interchange is justified for every physical modulus. With |Φ̂(t)|≤D/(1+t⁴), the two Abel costs are bounded by 4D/(1+t²). Its real integral is 4πD, so the restored cutoff costs the fixed factor 2D. This factor is chosen before Y, either length, both endpoints, the moduli, and ω.

`factored_initial_mean` counts the actual pairs (q,d) with k=qd. The injection into the divisor antidiagonal gives at most τ(k) such pairs, even when q=d. On a block K≤qd≤X≤2K the 1/k factor and the two separate ε/2 bounds give

$$\sum_{(q,d)}\frac{1}{qd}\left|\sum_{m,n}e((m-n)\omega)S(m,n;qd)\Phi\!\left(\frac{4\pi Y\sqrt{mn}}{qd}\right)\right|
\le C_\varepsilon (XMN)^\varepsilon(X+MN).$$

Here M,N are bounds for the two integer prefix lengths. Each must be positive in the epsilon form. The sum may use any subset of factorizations in the stated block. `native_block_initial` takes both intervals equal to the actual [2^j,2^(j+1)) with their exact integer length 2^j. `smooth_modulus_support` also treats a real band N₀≤m,n≤2N₀. A nonzero smoothed sum forces (8/5)πN₀Y≤k≤16πN₀Y from the actual support [1/2,5/2]. Thus only a fixed finite number of full-modulus dyads intersect the support, independently of q and Y.

The remaining spectral step must estimate the native exceptional sum by this geometric term plus the regular, continuous and holomorphic remainders on the same identity frame of Γ₀(q). The second prescribed-test trace, complementary Bessel bounds and the level induction are still needed for (4.29) and the full level-averaged Pascadi bound. All four sources are uncompiled.
