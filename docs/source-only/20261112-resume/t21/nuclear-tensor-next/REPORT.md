# 原指定测试在一条异号标记行上的 Kuznetsov 等式

九份 Lean 候选源的终点是 `OriginalPrescribedOppositeTrace20261112.original_prescribed_opposite_trace`。参数为原 `D,r,k,z,ha,upper,negativeM,J,j,ell`、`hs : traceNegative D k negativeM = true` 及任意固定 `Y>0`。取 `Φ = spectralTest ell Y`，终点给出原 `continuousDensity Φ` 的可积性、全离散级数的可和性、每对原算术标记的模数级数可和性，以及下式。这里的等式左侧保留原 `commonPoissonCompleted` 权、`traceBeta`、`traceIndex`、互素条件和实际 `traceModulus`。

\[
\sum_{n,p}W(p)\,\beta(n)\sum_{d>0}\operatorname{modulusTerm}
  (\Phi,z,p,h_n,d)
=\sum_i 8\widehat\Phi_K(\nu_i)\,\overline{M_i}\,N_i+
 \int_{\mathbb R}\frac{8\cosh(\pi t)\widehat\Phi_K(it)}
 {4\pi\cosh(\pi t)}\sum_{a\in\mathrm{Parameters}(z)}
 \overline{M_a(t)}\,N_a(t)\,dt .
\]

\(\widehat\Phi_K(\nu)=\int_0^\infty K_{2\nu}(t)\Phi(t)\,dt/t\). Each \(i\) ranges over the original `actualCuspBasisIndex`. Its `basisOrder` can be real or imaginary. Each \(a\) is an incoming cusp of the original level against the two original observation frames. The scale in a physical chart is obtained with `OriginalFullModulusSupport20261102.original_spectral_scale_pos`. The separate arithmetic chart conversion `original_chartModeAtom_eq_normalized_cuspOne` retains its exterior normalization.

## The common tensor and the actual spatial price

1. Write \(x=\log a,y=\log b\). The function used throughout is T03's \(H_{\ell,Y}(a,b)=h_{\ell,Y}(ab)\,2\sqrt\pi\cosh w\,e^{-4\pi^2\sinh^2 w}\), \(w=(x-y)/2\), with its defined zero extension. The actual log lift has all ordered mixed derivatives bounded by \(C_{r,s,A}\exp[-A(|x|+|y|)]\) and vanishes on \(ab\le p_0=(Y/(64\pi))^2\). The integer translates of the previously constructed \(\rho\) sum to one. Multiply by \(\rho(x-i)\rho(y-j)\) and take the existing period-64 double Fourier coefficients. The first variable passed to `C2` is the second height. Consequently its mixed \(\partial_2^2\partial_1^2\) bound takes the lift's derivatives in exactly T03's proved order. Finite Leibniz sums and \(|i|+|j|\le |x|+|y|+64\) on the two full periods give, for every \(A\ge0\),

   \[
   |c_{ijkl}|\le C_A e^{-A(|i|+|j|)}(1+|k|)^{-2}(1+|l|)^{-2}.
   \]

   In particular \(\sum |c_{ijkl}|e^{A(|i|+|j|)}<\infty\), by applying the coefficient estimate with \(A+1\). The height probes are \(\psi_{ik}(a)=\chi(x-i)e^{2\pi i k(x-i)/64}\) and \(\phi_{jl}(b)=\overline{\chi(y-j)e^{2\pi i l(y-j)/64}}\). The compact smooth cutoff \(\chi\) equals one on \([-1,1]\) and has support in \([-2,2]\). Fourier inversion inside each period, zero extension beyond the cutoff and the partition give a pointwise absolute `HasSum` for \(H=\sum c_{ijkl}\psi_{ik}\overline{\phi_{jl}}\). This places \(c\) linearly outside the native Gram. If \(c_{ijkl}\ne0\), the core meets \(ab>p_0\), so \(e^{i+j+2}>p_0\). Both enlarged probes together satisfy \(ab\ge\delta=p_0e^{-6}\) wherever their product is nonzero.

2. For the original signed integer \(m\ne0\), `scaledSeed` evaluates at \(|m|y\) with amplitude \(|m|^{-1/2}\). Every frequency on the same window has identical modulus. Let \(b(u)=e^{-u/2}\chi(u)\), \(s=\log|m|-i\), and take the positive spatial zero-mode envelope `fromLog` of the compact test \(e^{-i/2}b(u+s)\). Its height value on \(y>0\) is exactly \(|m|^{-1/2}\chi(\log(|m|y)-i)\). Lebesgue translation of its log energy gives \(e^{-i}\int|b|^2\); translation of its zero Mellin moment gives \(\sqrt{|m|}\,e^{-i}\int e^{-u/2}\overline{b(u)}\,du\). T04's `signed_envelope_norm_sq` then bounds each true signed `framedVector` by \(C(z,m)(e^{-i/2}+e^{-i})\), including the original level-volume residue. The estimate is uniform in the frame and the modulation. The original finite spatial packet is the \(L^2\) sum with weights \(\overline{w_b}\) on `originalFrame false/true`, as follows from the a.e. representatives of the finite sum. This proves `marked_trace_class` for the actual `originalMVector` and `originalNVector` by the previous centre estimate with \(A=1\).

3. For each pair of marked vectors \(v,w\), `basis_packet_inner` identifies each native discrete term with \(\overline{\langle v,B_i\rangle}\langle w,B_i\rangle\). Finite Cauchy–Schwarz and the original basis Bessel bound give \(\sum_i|F_i|\le\|v\|\|w\|\), over the entire basis. For the continuous spectrum, `original_marked_weak` identifies each component with the conjugate of the physical analysis vector at \(dt/(2\pi)\). The diagonal `continuous_projection_gram` gives \(\sum_a\|A_a v\|^2=2\|P_{\rm cont}v\|^2\). Applying integral Cauchy–Schwarz in each cusp and then finite Cauchy–Schwarz across cusps yields \(\sum_a\int|G_a(t)|\,dt\le\|v\|\|w\|\), with the manuscript's \(1/(4\pi)\) in each \(G_a\). Multiplication by \(|c|\) gives absolute joint summability on the discrete set and finite total absolute mass over all modes, cusps and real parameters. These bounds allow the signed interchanges used in the terminal equality.

## Scalar transform and finite physical modulus range

At a positive argument \(t=4\pi\sqrt\kappa\), T03's `plane` has second height \(b=\kappa a/(x^2+a^2)\). A nonzero weighted integrand satisfies \(a\in[L,U]=[e^{i-2},e^{i+2}]\), \(\delta\le ab\le\kappa\) and \(|x|\le U\sqrt{\kappa/\delta}\). Its norm is at most \(|c|L^{-2}\) on that rectangle. Multiplying by its area, using \(U^2/L^2=e^8\), and then by \(4\pi/t\), bounds the absolute orbital contribution by \(2e^8|c|/\sqrt\delta\). It vanishes at \(t<4\pi\sqrt\delta\). Fubini on the original product measure and T03's exact `rank_one`, `plane_integrable`, `prescribed` imply \(\Phi(t)=\sum c\,\operatorname{orbit}(t)\) at every \(t>0\).

For a fixed \(\nu\in\mathbb C\), choose an integer \(n>|\operatorname{Re}(2\nu)|\). The old absolute Mellin integral gives \(\int_{t>0}t^n|K_{2\nu}(t)|\,dt<\infty\). On \(t\ge D=4\pi\sqrt\delta\) one has \(1/t\le t^n/D^{n+1}\). Thus the scalar \(K\)-transform of the series has an absolutely integrable majorant summable over the tiles, and the reconstructed transform equals \(\widehat\Phi_K(\nu)\) at the specified order. The old rank-one transform has left factor \(\overline{\operatorname{orderProbe}(\psi,\bar\nu)}\). At every actual basis index, the old order symmetry supplies exactly the left probe used by the projected trace.

For the finite \((n,p)\) on one original row put \(A=\sum_{n,p}p|h_n|\). Since the actual modulus is \(d\sqrt z\) with \(z\ge1\), any integer \(D_0>4\pi(1+A)/(4\pi\sqrt\delta)\) suffices simultaneously for all original marks and all four integer indices. Above it both the weighted atoms and the reconstructed prescribed term vanish. This gives `common_modulus_cutoff` before the outer sum over the atoms. The terminal module sums the original `original_opposite_trace` identity with these same coefficients. Its three proven `HasSum` statements identify the common geometric sum with the sum of its original discrete and continuous sides.

## Selected source and verification

The nine install targets and their direct imports are listed in `REGISTRY.json`, with byte counts, SHA-256 and Git blob IDs. The original manuscript revision is `9731290e8f53cffda44129906cde6a965eaa869b`. The preceding physical trace, the selected integer partition and the double Fourier source are pinned at `32d541884c85748e3fb18f7a83801b2f8b16e359`. The incoming Abel-lift author registry is `5015265ce2a76abacc55d97b845c92c24d68fa35b1b2ef12ae7eb1f6db970358` and its T14 allowlist is `509d66dd21ea0f387da780aa1a6b3fa01f7ed3a778dd0e7c896cc7de45769180`. The incoming signed-envelope author registry is `c25c9c2220788e678d49318c3011e2adeb29185837989a45d22e8c33975975bd`, with T06 allowlist `fc5500a1a34e825cdee08d44e5831c4879a8a8322b5a7afad5731a907cd8ceba`. The source selections in these upstream registries apply, including the prior full-modulus test notation overlay and the projection API selection.

This package has authorial source and dependency checks. Lean elaboration, a complete executable dependency closure and kernel readback were outside the authorized run. Formal credit remains zero. The constants here may depend on the fixed original marks, level and scale. Same-sign and holomorphic terms, variation in the level, a uniform DI large-sieve estimate, the outer source assembly and the manuscript's final \(7/32\) estimate have separate obligations.

One provenance-only lookup used the manuscript commit in the formalization repository. The local partial clone attempted a read-only upload-pack despite its no-lazy-fetch environment flag and returned `not our ref`. The manuscript objects below come from T03’s frozen records of the correct manuscript repository. Subsequent repository reads use a file-only protocol allowlist. No remote write, CI or proof job was run.
