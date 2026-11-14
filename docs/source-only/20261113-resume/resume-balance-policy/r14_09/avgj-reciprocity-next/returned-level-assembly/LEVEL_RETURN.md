# Six actual return levels and the retained exceptional estimate

Fix a dyadic entry $(Q,2Q]$, a subinterval $[a,b)$ of the original positive Fourier block and one phase $\omega$. On the full support of the input cutoff, including its shoulders, the single-bump lower bound gives a nonnegative contribution at every retained complementary slot. The cutoff equals one on the entry dyad. The complete complex level trace therefore bounds the entry energy once the other marked spectra have been retained as explicit remainders.

For each input scale $Q$, put $M=2^j-1/2$, $C=\pi MY/Q$, $B_l=2^l C/2$ for $0\le l<6$, and $A_v=2^v Q/4$ for $0\le v<4$. The $A_v$ cover the support of this one input bump. The six $B_l$ cover the entire support of the reflected trace. To cover the printed parent interval $(Q,16Q]$, one separately applies the resulting single-entry estimate at $Q,2Q,4Q,8Q$. The child windows then extend from $C/16$ up to $32C$.

For fixed $0\le T<1$ and $\varepsilon>0$, `retained_recurrence` provides constants $c,K>0$, $D\ge0$, and $Y_0\ge1$ before the scales and the common subinterval. For $Y\ge Y_0$, the contribution to $cJ_T((Q,2Q],Y)$ from the six retained exceptional return sums is bounded by

$$
K\sum_{l<6}\left(\max_{a\le k\le b}J((B_l,2B_l],Y;[a,k))+
 Y^\varepsilon(B_l+M)M\right).
$$

The input and output holomorphic contributions together cost at most $4D M\big(\sum_{l<6}(B_l+M^{1+\varepsilon})+\sum_{v<4}(A_v+M^{1+\varepsilon})\big)$. The additional price is four times the sums of the norms of the real cuspidal, continuous and $\tau>T$ complementary contributions over the actual input and output level unions. All three are defined directly from the native spectrum and the two prescribed tests. The coefficient $K$ multiplies the child price just once per window and remains independent of the varying scales.

This source-level estimate retains the explicit residuals of (4.29). The removal of the high complementary band still needs the uniform native gap, and the two real-parameter measures still need the uniform quadratic sieve bounds. The three Lean files are uncompiled. [Drappeau, equation (4.29)](https://arxiv.org/html/1504.05549v4#S4.SS2)
