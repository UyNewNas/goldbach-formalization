# Returning all physical windows to the original J range

The exceptional sequence on the positive $m$-leg is $1_I(m)e(mω)$, where $I$ is any subinterval of the native block $[2^j,2^{j+1})$. The same $I$ and $ω$ apply to every level and every spectral label. Put $M=2^j-1/2$, $H=\max(1,M)$ and $W(Q)=\max(1,M,Q^2/M)$. Write $E_I(Q,Y;t)$ for the native nonnegative quadratic form $Y^{τ_i}|\sum_{m∈I}e(mω)m^{it}ρ^K_{q,i}(m)|^2$ summed over $Q<q≤16Q$ and strict exceptional slots. The phase is also a parameter of $E_I$. The finite subsets of $Q<q≤2Q$ in the manuscript are dominated by this form. The zero-frequency target is $E_I(Q,X;0)\ll_{A,ε}[(1+Q)(1+M)]^ε(Q+M)M$ for $0<X≤A\max(M,Q^2/M)$. The two versions of the epsilon factor with and without the ones are equivalent on nonempty outer windows, since $Q≥1/16$, $M≥1/2$. [Original Medium §10(vi)–(vii)](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L463)

Drappeau defines the left window by $Q<q≤16Q$. Proof 4.6 specifies a single Φ supported in [1/2,5/2], equal to one on [1,2], and uses $Φ(q/Q)$. Its plateau covers the first dyad. In each of the four input pieces use $Q_b=2^b Q$, $0≤b<4$, and use six dyadic returns with lower scale $B_{bl}=2^{l-1}π M Y/(2^bQ)$, $0≤l<6$. Their union is contained in $(C/16,32C]$, $C=πMY/Q$. At $M=1/2,m=n=1,C=1,d=20$, both cutoff arguments equal $\sqrt{2/5}$ for a suitable positive $x$, and the actual manuscript bump is positive there. This checks the support discrepancy for fixed $b=0$ even before the other input pieces are added. It affects the printed intermediate support assertion and does not decide the claimed final inequality. [Drappeau, Lemma 4.10 and Proofs 4.6–4.8](https://arxiv.org/html/1504.05549v4#S4.SS2)

## Quantified scale calculation

The following is a deduction about the analytic estimates used by the published argument. It identifies exactly which estimates still require native proofs. There is no Lean declaration taking a recurrence or the initial estimate as an axiom.

* For every $δ>0$, after fixing a family bound $τ≤1/2$, choose $Y_0≥1$ and finite positive constants $K_δ,D_δ$, independent of all $I,ω,j,Q,Y$. The native recurrence needed at $Q≥1,Y≥Y_0$ is
$$
  E_I(Q,Y;0)≤K_δ\sum_{b,l,σ=±1}\int |\widehat Φ(t)| E_I(B_{bl},Y;σ t/2)\,dt+
       D_δ[(1+Q)(1+M)(1+Y)]^δ(Q+M+MY/Q)M .
$$
  Here the sum means four choices of $b$, six of $l$, and two signs. A returned dyad $(B,2B]$ can be enlarged to $(B,16B]$ since its energy is nonnegative. Include any fixed $2π$ normalization in $K_δ$. All constants from the 4-by-6 cover in the error may be included once in $D_δ$. The term $Y^δ$ accompanying the additive transformed ceiling is included in the error via the $X=1$ baseline.
* The native initial estimate required for every $Y≥Y_0,Q>0$ and the same family of intervals and phases is $E_I(Q,Y;0)≤L_δ[(1+M)(1+Y)]^δ(Q+M+Y)M$. For $0<Y<Y_0$ one can instead use the fixed $X=1$ bound, monotonicity and $τ≤1/2$, at cost $\sqrt{Y_0}$. This baseline holds for subinterval coefficients by zero extension in the signed sieve. The proved modulus estimate treats intervals, both weights and the factorization count. A full native spectral (4.30) additionally needs its regular terms.
* Let $L=\int |\widehat Φ(t)|(1+|t|/2)^2\,dt<∞$ and $A_0=\max(1,48K_δ L)$. The integrability follows from the fourth-order Mellin tail. For each fixed level window view $E_I(Q,Y;t)^{1/2}$ as the Euclidean norm over all levels and exceptional rows, including $Y^{τ_i/2}$. Abel summation for $m^{it}$ writes this vector as a sum of prefix vectors with scalar coefficient total variation at most $1+|t|$. The triangle inequality in that one Euclidean space gives $E_I(Q,Y;t)≤(1+|t|)^2\max_{J⊆I,\,J\text{ prefix}} E_J(Q,Y;0)$. Thus the supremum may be taken jointly over physical intervals **after** forming each full level-and-row energy. This also removes the Mellin twist before applying the inductive bound. Every prefix is still an interval with the same additive phase. No exponent accumulates in the Mellin kernel as the depth increases.

Fix $ε>0$ and $δ=ε/4$. Set $κ=16π$, $λ=π/16$. Choose $D≥\max(1,κ^2,2κ,κ(4A_0)^{1/ε})$ after the recurrence, transform, and Mellin constants have been chosen. Fix for example $T=2\max(1,D/λ,\sqrt{DY_0})$. Use induction over the possibly real scale $Q$ in the bands $Q≤TH$, then $2^{v-1}TH<Q≤2^vTH$, for each fixed $j$. The induction bound at the benchmark is
$$
 E_I(Q,W(Q);0)≤P_ε [\max(1,Q)H]^ε(Q+M)M .
$$
Its constant $P_ε$ is independent of $v,j,Q,I,ω$.

1. On the initial band, $W(Q)≤\max(1,2T^2)H$, since $H/M≤2$. The interval initial estimate gives $Q+M+W(Q)≤c_T(Q+M)$. Its epsilon cost is at most $c_{T,δ}H^{2δ}≤c_{T,δ}[\max(1,Q)H]^ε$. Use the preceding baseline below $Y_0$. This includes $j=0$ and real $Q<1$. Hence a finite $P_{\rm base}$ depending only on $ε$, the fixed analytic constants and $T$ suffices.
2. For $Q>TH$, $W(Q)=Q^2/M$. Evaluate the recurrence at $Z=Q^2/(DM)≥Y_0$, multiplying it by $\sqrt D$ to transport the left side up to $W(Q)$. The band $τ≤1/2$ justifies this monotonicity price at every native slot. The actual 24 lower endpoints satisfy $λQ/D≤B≤κQ/D≤Q/2$ and $B≥H$, so the inductive bound applies at $W(B)=B^2/M$. The choice $D≥κ^2$ gives $W(B)≤Z$. Transport the child from $W(B)$ to $Z$ at cost $Q/(\sqrt D B)$, exactly. Multiplication of the two prices gives $Q/B$.
3. Normalize by $[QH]^ε(Q+M)M$. After the Abel step and summing the two signs and 24 windows, the entire recurrent contribution is at most
$$
 A_0 P_ε \sup_B (B/Q)^ε\frac{Q(B+M)}{B(Q+M)}
 ≤2A_0(κ/D)^εP_ε≤P_ε/2 .
$$
The inequality uses $B≥M$. This is the point at which every one of the physical windows and its constant is paid at every recursion depth.
4. The returned error after left transport is at most $c_{D,δ} Q^{3δ}(Q+M)M$, because $MZ=Q^2/D$, the three arguments $Q,M,Z$ lie at least at fixed positive lower bounds, and $MZ/Q=Q/D$. Since $3δ≤ε$, one finite normalized constant $P_{\rm err}$ works across all bands. Taking $P_ε≥\max(P_{\rm base},2P_{\rm err})$ closes the induction at every depth. Finally $X≤A\max(M,Q^2/M)≤A W(Q)$ costs at most $\max(1,\sqrt A)$. Monotonicity treats $0<X≤W(Q)$.
   
The constants and the shrinking parameter repair the scale handling at the mathematical level, conditional on native versions of the displayed analytic inputs. Source-level exact double trace, physical windows, Mellin separation, transformed bounds on a fixed band, and the arithmetic modulus mean have been independently audited. The actual all-level spectral-gap provider, the regular spectral errors in the native recurrence and initial estimate, and their assembly over every permitted subinterval remain necessary. No part of this calculation supplies those estimates or changes the statement of Theorem J.
