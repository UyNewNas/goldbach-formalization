# T08 · The physical scattering coefficient at every cusp

**For every positive level, every pair of normalized integral cusp frames, every height $y>0$ and every real spectral parameter $t$, the horizontal mean of the continued native parabolic Eisenstein function now has its two-power constant term.** The outgoing coefficient continues the original absolutely convergent cusp-pair Dirichlet series with its gamma factor. P3.5 remains yellow. These five modules are uncompiled source.

## The initial coefficient

Let $g,h$ be the source and observing frames, $w_g,w_h$ their widths and $r_{g,h}(c)$ the existing count of admissible residues. A residue $0\le d<c w_h$ is admissible exactly when some $\gamma\in\Gamma_0(N)$ gives bottom row $(c,d)$ in $g^{-1}\gamma h$. The source establishes, on $\Re s>1$,

```
Φ_g,h(s) = √π Γ(s−½)/Γ(s) · (w_g w_h)^(−s) · Σ_{c≥1} r_g,h(c)c^(−2s).
```

The proof starts from the native normalized parabolic function, reindexes its actual signed primitive rows and uses the existing framed-row period $c w_h$. The two oriented axis rows contribute one copy of $y^s$ when the two cusp orbits agree. Negative and positive first coordinates give equal contributions to the outgoing row and cancel the global $1/2$. Each positive residue contributes a physical translate by (d/$c w_h$) of the existing periodized kernel. All translates on the unit integration interval lie in one compact interval. The original absolutely convergent series therefore dominates the integrated row norms. The already evaluated real zero Fourier integral and holomorphic uniqueness supply its exact complex beta factor.

## The critical coefficient

The function $\Phi_{g,h}$ is continued by observing the same native parabolic family at height one and subtracting its diagonal incoming amplitude. Its agreement with the independently defined Dirichlet series is proved throughout the initial half-plane. For all $\Re s\ge 1/2$, $s\ne1$, the resulting physical identity is

```
∫₀¹ E_g(σ_h(x+iy),s) dx = δ_[g],[h] y^s + Φ_g,h(s) y^(1−s).
```

For a compact path in the upper half-plane, its imaginary part has a strictly positive minimum and a finite maximum. The conductor-greater-than-one completed family admits a simultaneous polynomial-times-exponential majorant in the frequency, uniform on compact parameter and height regions. The conductor-one family uses R22’s completed spatial and parameter-disk estimates, including its regularized center. The native Cauchy estimate and finite-measure dominated differentiation prove regularity of the physical integrals. Finite Cramer and character inversion transport those integrals through every legal dilation and back to the ordinary cusp family. The true reciprocal of the Dirichlet $L$-factor treats principal squares through $2s=1$. The determinant and level factor have their original nonvanishing in the regular range.

The difference of the two sides at an arbitrary observation height is meromorphic on $\mathbb C\setminus\{0,1\}$. It has zero germ at $s=2$. Uniqueness on that connected domain and regularity of the actual value give pointwise equality across the critical line. In particular the formula at $t=0$ requires neither division by the difference of the two exponents nor a separate choice of representative at the center. The function $\Phi$ here has proved meromorphy on the two-point complement and full-complex differentiability throughout the stated closed half-plane except at $1$.

## Original dependency and remaining hypotheses

The constant term is an input to the Maass–Selberg truncation for the actual quotient continuous spectrum in the manuscript’s classical correspondence and medium-completion §§7–8. This supplement supplies that physical row for all actual singular cusps of the trivial-nebentypus level. It uses the pinned Young dilation families and the upstream native arithmetic; it assumes no normalized continuous spectral formula. [Original classical correspondence](../../../../../chen-imbalanced-semiprimes/paper/source/modules/final-classical-input-correspondence-20261010.txt) · [Original medium completion](../../../../../chen-imbalanced-semiprimes/paper/source/modules/distribution-medium-completion-20261010.txt) · [Young §§3, 4, 7, 8](https://arxiv.org/html/1710.03624v2) · [Drappeau Lemma 4.3 and Proposition 4.7](https://arxiv.org/pdf/1504.05549v4)

Scattering reciprocity, the physical functional equation, critical unitarity, all-cusp truncation with the residual term, global continuous Plancherel and identification with the orthogonal complement of the cusp space are still required. For the original normalized trace, the specific geometric Bessel test and its inversion, holomorphic basis and oldform norms, native Maass Hecke compatibility, large-sieve estimates on the actual regular and exceptional rows, the spectral gap and the uniform $7/32$ energy also remain. The earlier spatial packet and global relative ABL results retain their exact published scope. This is a missing classical formalization and conversion step. The work supplies no evidence of a mathematical defect in the manuscript.

All preceding source bytes and author records are separate from this supplement. The source registry records the exact declarations, upstream dependencies, manuscript revisions and scope status. Local work used text inspection and SHA-256 comparison only. Formal credit remains zero.
