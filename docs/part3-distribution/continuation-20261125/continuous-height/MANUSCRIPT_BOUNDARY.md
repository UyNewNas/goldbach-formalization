# P3.5 continuous spectrum over all heights

At mathematical commit `94cff537f2e60173aaf936c2345d5af0ee5e6585`, the three modules implement the regular height summation in Appendix A.5 for continuous rows with supplied cumulative energies and test bounds. This is one component of the derivation of (96), `ana:spectral-polynomial`. The subsequent return to the physical kernel in (97), `ana:returned-polynomial`, already has a separate Lean consumer. [Frozen A.5, lines 731–825](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex#L731)

## Normalization and bound

The paired row is $P(t)=\sum_i \overline{M_i(t)}S_i(t)/\pi$. Both cumulative energies integrate $\sum_i |M_i(t)|^2/\pi$ or $\sum_i |S_i(t)|^2/\pi$ against ordinary $dt$ on $[-T,T]$. This realizes the continuous measure $dt/\pi$ of (104), `ana:regular-norm`, with the same finite cusp family throughout. The printed Eisenstein normalization is the one used in Y04. The older raw-coefficient formula with a hyperbolic density requires its own change of normalization. [Frozen Appendix B, lines 984–1028](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex#L984)

For $T\ge1$, the two supplied energy bounds are $(T^2+u)A_2$ and $(T^2+v)B_2$. With $Y>0$, the test $H$ has the low-height bound $C(1+|\log Y|)/(1+Y)$ up to $\max(1,2Y)$ and the high-height bound $C(|t|^{-5/2}+Y|t|^{-3})$ from that height onward. The shell and positive-measure modules sum the tail. The printed-row consumer proves absolute integrability on the line, the bound below, and convergence of the complex integrals over $[-4^jK,4^jK]$ for $K\ge1$.

$$
\int_{\mathbb R}|H(t)P(t)|\,dt
\le 516\,C\frac{1+|\log Y|}{1+Y}
\sqrt{(1+Y^2+u)A_2\,(1+Y^2+v)B_2}.
$$

The factor 516 is an explicit constant in the general shell bound implementing the manuscript's implied constant. The exponent $7/32$ enters later, in the spectral estimates and their assembly. [Shell payment](../../../../ImbalancedChen/Part3RegularCumulativeShellPayment.lean) · [Positive-measure exhaustion](../../../../ImbalancedChen/Part3RegularPositiveMeasureExhaustion.lean) · [Printed-row consumer](../../../../ImbalancedChen/Part3ContinuousTraceExhaustion.lean)

## Remaining physical application

Y04's `original_two_cumulative_windows` supplies source-level energy bounds and `original_printed_six_spectrum` identifies the two sign lanes and six scales. The physical application must use $Y=\mathtt{chartY0}$ at the actual indices, feed the prescribed positive or opposite test with its factor $1/4$, and keep the source divisor payment through Cauchy. Its constants and Fourier-mode derivative costs must remain uniform over the physical family. The full (96) also combines the regular Maass and holomorphic components, the exceptional inputs, and the level and Fourier sums. The cited ABL, Kim–Sarnak and Pascadi results enter through their stated hypotheses. An application to the actual rows still owes the support, normalization and uniformity checks. [Frozen A.5, lines 705–801](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex#L705)

The actual-window adapter remains source-only. Recovery searches, including the restored cloud workspace, did not locate byte-identical copies of six registered sources. This leaves a dependency and implementation gap. The audit established no substantive gap in the frozen manuscript. [Actual-window adapter](../../../source-only/20261125-p35-continuous-trace/Part3OriginalGeometricWindowEnergy.lean) · [Registered source hashes](../../../source-only/20261125-p35-continuous-trace/REUSE.json)

P3 task `cbcebb66105f4036a00789cc806ce176` subsequently passed strict compilation, bundled kernel replay and the complete owned-declaration/type/transitive-axiom audit for all three modules: 81 owned declarations, including helpers. See [the acceptance receipt](RECEIPT.json) and [independent review](INDEPENDENT_REVIEW.md). This acceptance does not close the physical-family obligations above.
