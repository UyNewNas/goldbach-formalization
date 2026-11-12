# Original same-sign Petersson pretrace

The 21 Lean source candidates construct the full Petersson space at the original level and identify its fixed-weight cross-cusp Gram sum with the old matrix Kloosterman–Bessel row. The terminal declarations are \(\mathtt{OriginalPositivePeterssonTrace20261112.petersson}\) and \(\mathtt{original\_positive\_petersson}\) in the namespace \(\mathtt{ImbalancedChen.Part3}\). The second uses the original sign licence, positive first mark, trace index, and both finite carrier memberships. The package is source-only and uncompiled.

For \(N=z>0,\ k=2r,\ r\ge1,\ m,h>0\), put \(C_d=\sqrt N\,d\). The original hyperbolic measure is \(dx\,dy/y^2\). Its Petersson ONB gives

\[
4\pi\Gamma(k-1)\sum_f\overline{R_{f,\infty}(m)}R_{f,1}(h)
={\bf1}_{N=1,\ m=h}
+2\pi i^{-k}\sum_{\substack{d\ge1\\(N,d)=1}}
\frac{\mathtt{cuspOneMatrixSum}(N,d,m,h)}{C_d}
J_{k-1}\!\left(\frac{4\pi\sqrt m\sqrt h}{C_d}\right).
\]

The terminal includes absolute summability of the individual complex modulus terms. For \(d\) coprime to \(N\), the old matrix sum is \(e(h/N)S(m\overline N,h;d)\). In \(\mathtt{original\_positive\_petersson}\), \(h=\lvert\mathtt{traceIndex}\rvert\), and the sign licence identifies its integer cast with the signed trace index. The previously published \(\mathtt{original\_positive\_holomorphic\_product}\) supplies the factor \((4\pi)^k\) between the native sieve product and \(\overline R_{\infty}R_1\). The new \(\mathtt{original\_positive\_basis\_pretrace}\) takes that product over every vector in the actual basis.

## Manuscript normalization

The manuscript’s S1 spectral-return source uses the two cusp charts and the sign of the physical indices. Its medium-completion module specializes the spectral sources. In Drappeau, the same-sign formula is (4.13), the holomorphic summand is (4.15), and its multiplier is \(\Gamma(k)\dot\Phi(k)\), with \(\dot\Phi(k)=4i^k\int J_{k-1}(q)\Phi(q)\,dq/q\) in (4.9). Equations (4.18) and (4.19) are the opposite-sign continuous and Maass terms. [Drappeau, §§4.1–4.3](https://arxiv.org/pdf/1504.05549v4)

The same-cusp display (4.26) on page 16 prints \(4\Gamma(k-1)\) multiplying the \(R\)-product. With (4.7) and the original unscaled Petersson integral, unfolding gives \(\Gamma(k-1)/(4\pi m)^{k-1}\) against the native \(m\)-th \(q\)-coefficient. Substituting \(a_f(m)=(4\pi m)^{k/2}\rho_f(m)\), \(R_f(m)=\sqrt m\,\rho_f(m)\), gives \(4\pi\Gamma(k-1)\). The candidate uses the factor derived from the integral. Converting the modulus term back to \(\Gamma(k)\dot\Phi(k)\) retains the quotient \(\Gamma(k)/\Gamma(k-1)=k-1\). [Drappeau, (4.7), (4.9), (4.15), (4.26)](https://arxiv.org/pdf/1504.05549v4)

## Construction in the candidate sources

| Sources | Result |
|---|---|
| 1–4 | A finite set of evaluations detects all level-one forms. The modular-form norm transfers detection to \(\Gamma_0(N)\). The map \(f\mapsto y^r f\) into the original carrier \(L^2\) is injective and gives exactly the unscaled integral. Finite-dimensional completeness provides the full ONB, actual Fourier Riesz vectors, and the explicit normalization. |
| 5–8 | The original regularized Poincaré series unfolds against every native form for \(s>0\). The horizontal integral extracts the native coefficient and the vertical integral gives its real Gamma factor. General integral cusps have an exact finite congruence filter. The pinned Lipschitz expansion gives the translated holomorphic orbit and its positive integer Bessel series. |
| 9–11 | Two real Fourier integrations by parts bound the dimensionless Hecke kernel uniformly. The T25 Euler majorant, including the zero horizontal frequency, controls the joint \(C,n\) sum for every integral cusp, all \(0\le s\le1\), and \(y\ge y_0>0\). Real Poisson summation identifies each denominator's periodization with that sum. |
| 12–15 | Primitive bottom rows with an oriented central sign are in bijection with the original parabolic positions in each integral chart. All \(D=u+Cj+CNl\), including negative lifts, occur exactly once. The physical slash summand equals its real Fourier kernel. Regrouping the absolutely convergent \(s>0\) series gives the common expansion, including the unique possible zero row. |
| 16–17 | The sequence \(s=1/(n+1)\) has the same explicit zero-parameter limit in every chart. Individual fixed-denominator orbit sums are holomorphic by local normal convergence. The summed majorant gives the same property for the full \(C\)-sum, and \(O(y^{1-k})\) gives zero at each cusp. Full modular reduction yields a global bound for \(y^r|P_{m,s}|\). Dominated convergence on the finite original carrier then identifies the actual limiting cusp form with the Riesz vector. |
| 18–21 | Period-one Fourier orthogonality on \(\Im w=1\) extracts the fixed positive mode. The cusp-one congruence filter collapses to the exact old arithmetic sum. Its true \(\sqrt N\) dilation supplies \(N^r\) in the slash and \(C_d=\sqrt N\,d\) in the Bessel kernel. Taking the horizontal functional through the common absolutely summable \(C\)-series gives the displayed terminal for all \(r\ge1\). |

The written derivation, including the weight-two Hecke regularization, is in [CONSTRUCTION.md](CONSTRUCTION.md). The proof uses the independently reviewed fixed-mark bound \(\sum_{d\ge1}B_m(d)/d^2<\infty\), uniform in the other integer argument. This bound is sufficient at weight two.

## Source selection and verification

The formalization base is \(\mathtt{212cbdcbdaf9ce267febd21bdfbc6d1f7fb0dc6f}\) in \(\mathtt{UyNewNas/goldbach-formalization}\). Both manuscript objects belong to the separate paper repository at \(\mathtt{9731290e8f53cffda44129906cde6a965eaa869b}\). The registry pins both source texts, the primary PDF, all new modules, direct external imports, the T25/T20 package, and the T13 selected Poincaré coefficient source. It records the published or archived origin of each physical dependency. [REGISTRY.json](REGISTRY.json)

The older native holomorphic Fourier normalization needed by the published cusp-frames source survives as a 5,431-byte S21 archive. This package carries its exact bytes as \(\mathtt{Part3NativeHolomorphicFourierNormalization.lean.txt}\), SHA-256 \(\mathtt{84bab008864a35cab849cff7c2f84606724acb278b660e2d07c3ad29551fbe85}\). Its two imports are pinned Mathlib modules. The registry gives its Lean destination for source selection.

Verification here consists of direct source and primary-manuscript comparison, declaration and dependency inspection, and byte-hash checks. Lean elaboration and compilation remain unverified. The fixed-weight result is the A input to the separate prescribed positive-test and weight-summation work. The full same-sign Kuznetsov identity and the full manuscript trace retain their own acceptance conditions.
