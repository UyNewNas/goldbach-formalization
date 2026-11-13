# Complementary spectrum on common subintervals of the level switch

For a positive native block with $M=2^j-1/2$, let $2^j\le a\le b\le2^{j+1}$ and $L_B=\{d:B<d\le2B\}$. At every $d$ the interval $[a,b)$ and additive phase $\omega$ are identical. For each fixed $0\le T<1$ and $\varepsilon>0$, the constants $C,Y_0$ are chosen before $Y,Q,B,j,a,b,\omega$.

Let $E(L,Y;a,c)$ be the complete native T08 energy with weight $Y^{\tau_{d,i}}$ and marks in $[a,c)$. Let $R_{d,i}$ be the double-mark trace term at the identity cusp with the actual switched test $\Phi(Yx)\Phi(4\pi\sqrt{mn}/(dQx))$, including its exterior cosine. For $Y\ge Y_0$, $B,Q>0$, the five sources give

$$
4\sum_{d\in L_B}\sum_{i:\,\tau_{d,i}\le T}|R_{d,i}|
\ \le\ C\left(\max_{a\le c\le b}E(L_B,Y;a,c)+Y^\varepsilon(B+M)M\right).
$$

The finite maximum in Lean is taken over $c=\min(b,n+1)$ for $a\le n\le b$. This includes every nonempty prefix, and the empty prefix has energy zero. The two Mellin signs $-t/2,+t/2$ both enter before partial summation. The maximum is taken after summing over the complete level set and all exceptional multiplicities. The quartic decay of the fixed Mellin density pays the squared variation uniformly. On the term with $Y^\varepsilon$, the unit-weight fixed-level sieve applies directly to each short interval with any common Mellin twist, giving the displayed $B+M$ without a frequency cost.

On the entry side, the real part of the single-bump trace restricted to the same band bounds the retained native energy times a positive constant for any finite level set. On both sides the factor four comes from $\rho^K=2R$ on the two marked legs. The comparison uses the actual values of $\tau_{d,i}$ to select the band. Covering every slot at a common fixed $T$ still needs the uniform congruence spectral-gap provider. Complete real-parameter Maass and Eisenstein error bounds are also required for (4.29) and (4.30). These are source-level results with no Lean elaboration or kernel verification. [Drappeau, proof of Lemma 4.10](https://arxiv.org/html/1504.05549v4#S4.SS2)
