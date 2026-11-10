# Independent review of the incomplete Eisenstein Gram calculation

**Source-level scoped pass for the seven frozen files.** At every positive level and pair of original integral cusp frames, the code identifies the Gram integral on the initial Mellin line, the normalized critical-line pairing on the physical quotient, and the pole contribution from the constant function. It gives a limit for the remaining horizontal contour integrals. Proving that limit zero remains necessary to obtain the spatial Gram identity.

The author registry `INCOMPLETE_GRAM_REGISTRY.json` has SHA-256 `dd6e1f046868dbf32d8d3f27c5735fb3417c03f58a8c888286b43c46d7c0a7d3`. The report `INCOMPLETE_GRAM_REPORT.md` has SHA-256 `64de2d2fde483c5b12687236a9882a9d8428355118fd6c7f76ea2fa8618738a8`. I read all seven proof sources, matched 100/100 length and SHA-256 entries, matched the ordered direct imports (16 distinct names), and matched the 29 printed signatures at their indicated source lines. I checked the prior physical scattering, actual residual projection, sharp-strip Mellin synthesis and relevant mathlib API statements. No proof was executed or kernel-verified.

| Source | SHA-256 |
| --- | --- |
| `Part3ActualRegularEisensteinQuotient.lean` | `1b827c7d30b38dd8ee38f68d7427de2dbf57f4d7b8b9a50cda6cb5d968995582` |
| `Part3ActualIncompleteEisensteinTransform.lean` | `892c1f4ae23a3985a1ffe88d710b05c40c21c4f0477823c1bda544f98d63d334` |
| `Part3ActualIncompleteEisensteinGram.lean` | `640e2cd57540a2cc541970201feaf3ba5054d193f718c9afe6b5c944ddcf92ac` |
| `Part3ActualIncompleteMellinFactors.lean` | `f8bcb61908353235af3e6da3328ebd60cb8c2e4e8b6a135fc0cec47e82e22bf2` |
| `Part3ActualIncompleteCriticalColumns.lean` | `969f51fc0764c15bb0ee92f3cbb753e2e07b60c62b226d2b9739b11bbc17a249` |
| `Part3ActualIncompleteContinuousGram.lean` | `8dc1878a14b2eaf6f5096b50b037b6d78a88c14d60d29a1076df021ec1eb2c5c` |
| `Part3ActualIncompleteResidualContour.lean` | `0afb73639d78a44ebc4a8f1153419cb8a7a8aee5e37d95e24f6607545503e165` |

## How the physical pairing is obtained

The quotient lift uses the genuine finite Young dilation and inverse character formulas, including the conductor-one ordinary family. For each regular contour point, the function is invariant under Γ₀(N), spatially continuous upstairs and continuous and measurable on the orbit quotient. At critical points it agrees with the previously realized incoming family. The zero mode uses the original sharp half-open unit strip, transported by its normalized frame. A compact frame image contains all nonzero seed terms. Clipping the Eisenstein function at its bound on that compact image preserves the lifted product term by term, its periodization almost everywhere, and its horocycle product on every contributing positive height. Only the clipped function needs an L² bound. This establishes absolute convergence of the original pairing and permits unfolding at every Re(s)≥1/2 away from 1.

For a compact test ψ the moment is Jψ(s)=∫conj(ψ(y)) y^s dy/y². With source frame g and observing frame h the exact pairing is δₕᵍJψ(s)+Φgh(s)Jψ(1−s), with δ computed on actual cusp orbits. On σ>1 the previously proved sharp-strip synthesis of the second vector uses Hφ(σ+it)dt/(2π). Conjugate-first spatial orientation therefore gives G(s)=Hφ(s)[δₕᵍJψ(s)+Φgh(s)Jψ(1−s)]. Fubini uses the absolutely integrable quotient majorant |Pₕ,ψ|·|Eᵍ(σ)| times the integrable Schwartz Mellin factor in t. The majorant is on the physical space and includes the original widths and stabilizer multiplicities through the older synthesis.

The log-height substitution gives Jψ(s)=conj(Hψ(1−conj(s))). At s=1/2+it this supplies the conjugated incident wave at t and conjugated scattered wave at −t. Φ(−t)=Φ(t)* and Φ(t)*Φ(t)=1 hold on all actual cusp indices, including t=0. They bound every column entry and turn the sum over source cusps of Vₕ,ψ(t)conj(Vg,φ(t)) into G(1/2+it)+G(1/2−it). Both boundary columns are L²(dt) by the Schwartz angular Mellin transform. Integrating the two actual terms accounts exactly for the single factor 1/(4π) in the physical Gram. This is a quotient-pairing calculation for zero-mode tests. The dt/cosh(πt) convention of the manuscript's marked nonzero Fourier rows requires its separate radial transform and trace comparison.

## What the contour proves

The scalar residue is Hφ(1) Jψ(0)/vol. The earlier genuine projection formula for the constant quotient vector identifies this number with ⟨V,Proj₁W⟩. Subtracting r/(s−1) removes the pole on the whole finite rectangle. With right side 3/2 and left side 1/2, the difference of the two oriented pole kernels is 1/(1/4+t²). Its integral from −T to T is 4 arctan(2T). For the horizontal difference multiplied by i as defined in the source, the limiting value after division by 2π is continuous Gram − ⟨V,W⟩ + ⟨V,Proj₁W⟩. The sign, order of tests, real Jacobian and factors of two agree with the actual Cauchy rectangle and the conjugate-first Hilbert inner product.

The full limit exists for each pair of frames and tests. To finish this generator calculation it suffices to exhibit unbounded heights along which the normalized horizontal difference tends to zero for that pair. Holomorphy on each finite rectangle and integrable boundary lines alone supply no such bound. Extension by the actual dense span and identification of the resulting full quotient resolution would follow only with additional proofs. This review supplies zero kernel credit or absolute spectral-estimate credit. The full Kuznetsov trace and original (24)–(25) remain open.
