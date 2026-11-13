# The positive Bruhat orbit for the prescribed height and ratio windows

`OriginalPositiveScalarGeometry20261112.original_positive_row` gives the two successive limits of the geometric pair for each fixed original source mark and common Poisson mark. The first limit sends the real height parameter R to infinity with the integer cutoff n fixed. The second sends n to infinity. Both limits include every positive integer modulus. The identity cell travels with the same pair. All six mathematical sources have received independent source-level mathematical readback from T14. Kernel elaboration is pending.

## The original positive row

Let z belong to the level carrier for the actual data D and block k. Fix the Poisson sign, assume the original residue is nonzero and take the branch `traceNegative D k negativeM = false`. The receiving cusp index is b = `traceIndex D k negativeM z m` for m in `nCarrier D k z`. The identity with `signedY` and positivity of the actual integer magnitude give b > 0. A mark p in `commonMBlock J j` satisfies p ≥ 2ʲ > 0. For d in ℕ⁺ let C = √z · d and q = 4π√(p |b|)/C. On the coprime branch the row uses the original `cuspOneMatrixSum z d hd p b` divided by C. On the complementary branch its summand is zero. The scalar test is the original complex period-64 test at fixed positive Y, including the manuscript's choice of its block scale.

The new statement is at a fixed pair of marks. The marked spatial identity already multiplies each pair by the original common coefficient W(p) and signed source coefficient β(m). Its external row assembly keeps the same coefficients and level scale through finite sums. The source path and fixed manuscript objects are identified under `original_manuscript_objects` in the registry. The physical argument and Fourier marks appear at lines 156–185 of the manuscript's Poisson spectral return. Section 10 of its medium-completion module fixes the infinity/one cusp convention. [Original argument and Fourier coefficients](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-S1-Poisson-spectral-return-20261010.txt#L156) · [Original spectral normalization](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L461)

## The two changes of variables

For a positive q write κ = (q/(4π))². Conjugating the original positive raw Bruhat integrand leaves H(a,b′) = ψ(a) · conjugate(φ(b′)) with b′ = κa/(X²+a²), a > 0. It changes the phase to e(X+κX/(X²+a²)), where e(t) = exp(2πit). The scalar outside the integral is 4π/q. The resulting functional is `induced`. Its value on each such product is literally `orbitTest 1 ψ φ q`. The statement requires the positive support of the first probe because the original test integrates its raw height on the full real axis.

Set σ = X/a and p′ = κ/(1+σ²). Then b′ = p′/a and w = log(a/√p′). The two original dilation formulas give dX = a dσ and da/a = dw. In these coordinates the positive phase has argument (a+b′)σ = 2√p′ σ cosh w. For the actual compact height H, its absolute integral is finite. After the height substitution it is bounded by the product of the compact σ amplitude and the L¹ norm of the actual ratio window. This proves the two changes of integration order in `plane_integrable` and `positive_slopes`.

The two signs of σ sum to the cosine at v = 4π√(κ−p′). On the positive branch the original product Jacobian is κ/(2p′√p′√(κ−p′)). Multiplying by the two branches, by 4π/q and by the √p′ from the physical height gives (q/v) dp′/p′. With s = log p′+R and Vₙ(v) = ∫ hₙ(w) cos(v cosh w) dw, the exact transformed value is

\[
 \Phi_{R,n}(q)=
 \int_{\exp(s-R)<\kappa}\eta(s)\,\frac{q}{v}\,V_n(v)\,ds,
 \qquad v=4\pi\sqrt{\kappa-\exp(s-R)} .
\]

Here η is T04's fixed unit bump of integral one and hₙ is T04's actual zero-integral ratio window. The same-sign formulas reuse the scale, slope and log-product Jacobians already proved for the earlier Abel orbit. They take the physical height directly from T04's `OriginalPositiveHeightTest20261112.original`. `induced_formula` includes the cutoff branch at v = 0.

## Uniform majorant and the two limits

The original ratio windows satisfy |hₙ(w)| ≤ K exp(−|w|) uniformly in n. Their integral vanishes exactly. Thus the factor cos(v cosh w) in Vₙ may be replaced by cos(v cosh w)−1. Combining its bounds 2 and (v cosh w)²/2 with cosh w ≤ exp(|w|) gives, for v > 0,

\[
 e^{-|w|}\,|\cos(v\cosh w)-1|
 \le 2v\,\exp\!\big(-\big||w|+\log v\big|\big).
\]

The last exponential has integral at most twice the full-line integral of exp(−|w|), by reflection on the negative half-line and translation. Hence |Vₙ(v)| ≤ A v with A independent of n and v. The integrand in the height formula is bounded by |η(s)| Aq for every R, including when exp(s−R) approaches κ. At fixed q > 0 and s, the positive branch eventually holds, and v → q. Dominated convergence and unit mass give Φᵣ,ₙ(q) → Vₙ(q). Dominated convergence in w then yields Vₙ(q) → Φc(q), with Φc the residual established in B① after subtracting the odd-J projection. `joint_price` supplies one B with |Φᵣ,ₙ(q)|, |Vₙ(q)| and |Φc(q)| all bounded by Bq.

T25's actual infinity/one matrix estimate bounds each of the three modulus summands in absolute value by

\[
 \frac{B\,4\pi\sqrt{p|b|}}{z}\,
 \frac{\operatorname{majorant}(p,d)}{d^2}.
\]

At positive d the second factor is exactly `FixedMarkTail.price (p:ℤ) 0 d`. T25 proves its sum finite for the fixed nonzero first mark. The bound retains the true coprimality test and second mark. The two uses of Tannery give `modulus_height_limit` and `modulus_window_limit` across the complete original ℕ⁺ series. `original_moduli_absolute` includes the summability of absolute values at both input stages and at the endpoint. Its fixed-mark constants suffice for the original finite marking sum.

## The identity cell

The old `pairDiagonal` has two scaled probes and the phase e(b/z). At the only active branch, z = 1 and b = p, this phase is e(p) = 1. The two 1/√p factors combine with the substitution a = p y and the original y⁻² weight. The resulting integral is ∫ H(a,a) da/a². For the actual packet, s = 2 log a+R yields `ratio.function 0/2` for every R. The second limit gives h(0)/2 = (2π)⁻¹∫ J₀(q)Φ(q) dq. `diagonal_rank_one` verifies the scaling and conjugation against the old physical object, and `original_diagonal_limit` transports the cell through the actual cutoff sequence. It occurs with positive sign alongside the residual geometric series. Isolating that series in the spectral identity therefore subtracts the cell once.

## Source selection and scope

Install the six mathematical files in the order in `REGISTRY.json`. Their namespace is `ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112`. T04's two shared input sources are pinned by their actual locked bytes. The B① raw and reviewed packet was published at `f60f8fc424a1f50eccc922dd137e319b64f3f2e1`. For a joint installation, apply its one-line proof-body selector in `api-selection`. It qualifies `intervalIntegral.integral_Iic_add_Ioi` and uses its pinned implicit variable `b`. Its preimage, postimage and delta are recorded individually. The earlier full-modulus test-jets and cosine-profile selectors remain explicit dependencies.

This packet closes the fixed-row geometry of the positive trace. T04 owns the physical tensor exchange, convergence of the complete spectral resolution, and the marked equality. The holomorphic Petersson component and level-uniform exceptional estimates have their own proof obligations. The fixed-mark arithmetic summability used here gives no uniform bound over growing p or z. No local Lean, Lake, LSP, numerical certificate, staging, CI, quota or remote-write operation was performed for this packet. The freeze records source identity and independent mathematical readback.
