# Conditional critical induction on the original positive row

This five-source package retains the sole additional premise

\[
 \forall q,m\in\mathbb N_{>0}\;\forall i\in\mathrm{exc}(q),\quad
 \tau_{q,i}>1/2\Longrightarrow\rho^K_{q,i,\infty}(m)=0.
\]

It is the definition `positiveHalfSupport`. Neither an averaged J estimate nor an initial estimate nor a level recurrence is assumed. The actual initial estimate and six-window recurrence are imported from frozen positive6. That package proves the analogous coefficient statement only above `3/4` and therefore does not discharge this premise. No assertion about the entire native eigenvalue spectrum or the manuscript's `7/32` follows from the conditional package.

The five Lean files preserve the existing draft bytes. The static audit checked their dependence order: scalar prices, coefficient transport, child price, real-scale induction, and the original T08 endpoint. There was no Lean, Lake, LSP or proof-helper execution. This is a conditional source proof, not a kernel-verified theorem or an unconditional closure.

Fix `epsilon>0` and set `delta=epsilon/2`. Write

\[
 H=\max(1,M),\quad W(Q)=\max(H,Q^2/M),\quad
 N(Q)=[\max(1,Q)H]^\varepsilon(Q+M)M.
\]

Let `A,E,X0` be the positive6 six-window constants at `delta`, and `K` its all-height initial-mean constant at `delta`. Put `kappa=16*pi`, `lambda=pi/16`, `A0=max(1,6*A)`, and choose

\[
 D=\max\big(\kappa^2,2\kappa,\kappa(4A_0)^{1/\varepsilon}\big),\qquad
 T=\max(1,D/\lambda,\sqrt{DX_0}),\qquad c=1+2T^2.
\]

These quantities depend on the fixed exponent and prior fixed analytic constants, before any `j,Q,a,b,omega`. They satisfy `D>=1` and `2*A0*(kappa/D)^epsilon<=1/2`. The chosen induction constant is

\[
 U=K[2(1+c)]^{\varepsilon/2}(1+2c),\qquad
 V=\sqrt D\,E\,2\,6^{\varepsilon/2},\qquad P=\max(U,2V)>0.
\]

On the initial real-scale band `0<Q<=T*H`, the scalar lemma gives `W(Q)<=c*H` and pays the all-height initial mean by `U*N(Q)`. This includes `j=0`, `M=1/2`, small real `Q`, and empty intervals.

On the recursive band `Q>T*H`, put `Z=Q^2/(D*M)`. Use the actual single entry dyad `(Q,2Q]` and its six returned lower endpoints `B_l=2^(l-1)*pi*M*Z/Q`. The previously proved geometric bounds imply

\[
 X_0\le Z,\quad H\le B_l\le Q/2,\quad
 W(B_l)=B_l^2/M\le Z,\quad W(Q)=Q^2/M.
\]

The half-support premise gives the two genuine row transports, at every common prefix, with factors `sqrt(W(Q)/Z)` and `sqrt(Z/W(B_l))`. Their product is exactly `Q/B_l`. Normalizing the child by `N(Q)` yields

\[
 A P (B_l/Q)^\varepsilon\frac{Q(B_l+M)}{B_l(Q+M)}\le P/12.
\]

The factor six has already entered `A0`; summing all six terms costs at most `P/2`. The proof takes the actual prefix maximum after the full level-and-slot sum. For each returned prefix, the induction hypothesis applies because its endpoints stay inside the original interval, and its level scale lies in the preceding dyadic band.

The additive charge is separate. Since `M>=1/2`, `Z>=1`, `D>=1`,

\[
 (1+M)(1+Z)\le6MZ\le6Q^2,\qquad MZ/Q=Q/D\le Q.
\]

Thus, including the left transport `sqrt(D)`, it is at most `V*N(Q)<=P*N(Q)/2`. No logarithm, epsilon power, or cost from a shoulder dyad multiplies the recursive child coefficient. Induction on the bands `Q<=2^n*T*H` proves the critical estimate simultaneously for all allowed `a,b,omega` at each fixed `j`. Unbounded powers of two cover every positive real `Q`.

The terminal `original_range_of_half_support` states, under the displayed coefficient premise, that for every `epsilon>0,A>=0` there is `C>0` before `S,j,Q,X,omega` such that

\[
 J(S,X;j,\omega)\le C[(1+Q)(1+M)]^\varepsilon(Q+M)M,
 \quad S\subseteq\{q:Q<q\le2Q\},\quad
 0<X\le A\max(M,Q^2/M).
\]

The literal final source uses the already proved unconditional `3/4` transport for the bounded multiplier `A`, choosing `C=max(1,A)^(3/4)*P`. This is harmless because `A` is fixed before the moving scales; the half-order premise has already been used at the two unbounded critical transports inside the induction. Nonnegative energies permit the arbitrary finite subset of the original level dyad. The stronger critical estimate itself covers every common short interval.

For a parent interval `(Q,16Q]`, apply the same dyadic theorem separately at `Q,2Q,4Q,8Q`. This does not change the actual six-window proof or discard their support constants.

The outstanding half-order coefficient premise is substantive. The existing T25 summability range `delta<1/4` provides only the `3/4` endpoint used in positive6. A valid provider for the displayed half-order premise, or a different proof of the original critical estimate, is still required before any unconditional full J claim. The separate native `7/32` step also remains outside this package.
