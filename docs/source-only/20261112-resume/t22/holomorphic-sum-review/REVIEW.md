# Independent source review of the all-weight holomorphic projection

**PASS_SCOPED_SOURCE_ONLY.** The seven T21 sources implement the positive-mark holomorphic contribution for the manuscript's fixed level, marked pair and test. The terminal `original_holomorphic_projection` includes absolute summability of the physical modulus series, of the joint modulus–Bessel-order series and of the complex spectral summands over the dependent index of all weights and all basis vectors. The separate scalar contribution and the complete positive trace are outside this decision. No Lean elaboration, kernel checking, or transitive axiom audit was run.

| Source | Independently checked content |
| --- | --- |
| `Part3OriginalHolomorphicProjectionPrices` | The order-one endpoint retains the factor \(d^{-1}\) from \(J_{2j+1}(Q/d)\). The absolute group coefficient divided by \(d\sqrt N\) supplies the other denominator factor. The resulting positive product majorant uses the T25 fixed-mark Euler price at exponent zero and the original factorial moment estimate. |
| `Part3OriginalWeightedPetersson` | The true A21 cross-cusp identity is multiplied by \((2j+1)\dot\Phi(2j+2)/(4\pi)\). Gamma recurrence converts the spectral coefficient into \(\Gamma(2j+2)\dot\Phi(2j+2)\). The two powers of \(i\) cancel in the geometry. The double modulus/order series is absolutely convergent before its two sums are exchanged. |
| `Part3OriginalHolomorphicProjectionMarks` | The positive integer mark is recovered from its original `Int` value. The phase is the actual cusp-one matrix sum, the denominator is \(d\sqrt N\), and the Bessel argument is \(4\pi\sqrt{ph}/(d\sqrt N)\). The physical profile passed to `modulusTerm` is exactly the prescribed test minus T03's `residual`. |
| `Part3OriginalPeterssonHighStrip` | Every integer modular-cell translate is compared to a member of the actual carrier through its \(\Gamma_0(N)\) left coset. Width dilation takes the normalized high strip into at most \(W+1\) such translates with \(W\) the exact cusp width. Petersson density and hyperbolic measure transform with the actual determinant-one frame. The covering estimate allows overlapping charts and composite levels. |
| `Part3OriginalHighStripFourierMass` | Horizontal extraction uses the width-one q-expansion at arbitrary positive height, with probability measure on an interval of length one. Its squared decay is \(e^{-4\pi my}\). The chart pushforward is the product with vertical density \(y^{-2}\), giving \(y^{2r-2}\) also at \(r=1\). |
| `Part3OriginalHolomorphicBasisMass` | Translation of the incomplete Gamma integral gives the uniform loss \(e^{4\pi m}\), and the exact scale converting `raw` to `frameR` restores \(4\pi\Gamma(2j+1)\). Applying the estimate for arbitrary \(f\) to its own Riesz vector and using the same-cusp complete ONB Gram identity controls the sum of squares with no basis-cardinality factor. The zero-norm representative is treated separately. |
| `Part3OriginalHolomorphicWeightSum` | Two true diagonal bounds at infinity and cusp one dominate the absolute cross products term by term using \(uv\le u^2+v^2\). The sum over the dependent full ONB index is absolutely convergent, including the basis at weight two. The final positive sign and \(h=\mathrm{traceIndex}\) come from the genuine marked row. |

Write \(H=\sum_{j,i}\Gamma(2j+2)\dot\Phi(2j+2)\overline{R_{\infty,i}(p)}R_{1,i}(h)\), using the basis of the appropriate weight at each \(j\). The returned geometric quantity is

\[
 G_{\rm hol}=H+\mathbf1_{N=1,\,p=h}\,\frac1{2\pi}\int_0^\infty J_0(q)\Phi(q)\,dq.
\]

The surviving integral uses ordinary \(dq\). The indicator belongs to this holomorphic projection. The original complex test is used unchanged in both spectral and geometric factors. The estimates establish summability for each fixed marked row and permit constants depending on the fixed level, marks and test. Detailed independent calculations are in [DERIVATION.md](DERIVATION.md). Byte selections, upstream source witnesses and the precise scope of the decision are recorded in [ALLOWLIST.json](ALLOWLIST.json).
