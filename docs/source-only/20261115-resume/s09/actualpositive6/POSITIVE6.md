# Complete original positive row through the initial region and six-window recurrence

This package contains six unchanged Lean source drafts from the previously unfinished `native-fixed-mark-order` directory. It is source-only, with no elaboration or kernel verification. Its precise endpoints are the positive-frequency support at `3/4`, the complete short-interval initial mean for all positive heights, the actual T08 initial region, and the actual six-window recurrence. It does not prove full Pascadi J or a global spectral gap.

Write `M=2^j-1/2`, `L_Q={q:Q<q<=2Q}`, and

\[
 E(L,Y,\omega;a,b;t)=\sum_{q\in L}\sum_{i\in\mathrm{exc}(q)}
 Y^{\tau_{q,i}}\left|\sum_{a\le m<b}e(m\omega)m^{it}\rho^K_{q,i}(m)\right|^2.
\]

Every sum uses the original native exceptional multiplicities and the infinity frame. All positive marks satisfy the same interval and phase across levels. Empty intervals are allowed.

For each fixed positive integer `m` and real `delta<1/4`, put

\[
 v=1-\delta,\quad S_{m,\delta}=\sum_{k\ge1} B_m(k)k^{-2+\delta},\quad
 K_{m,\delta}=(8\pi m)^v S_{m,\delta}.
\]

T25 proves that `S` is finite and that the physical Kloosterman norm is bounded by `B_m(k)` for every second mark. The actual diagonal arithmetic summand is `1[q|k]*S(m,m;k)/k*Phi(4*pi*Y*m/k)`. A nonzero cutoff forces `k<=8*pi*m*Y`; since `v>0`, its norm is bounded by `(8*pi*m*Y)^v*B_m(k)*k^(-2+delta)`. The full prescribed same-infinity trace identity therefore gives

\[
 |\mathrm{spectral}_{q,m,m}(\Phi(Y\cdot))|\le K_{m,\delta}Y^{1-\delta}
 \qquad(q\ge1,\;Y>0).
\]

Only this nonnegative arithmetic estimate drops the condition `q|k`. Every later spectral identity keeps the fixed original quotient. The constant depends on `m,delta`, and no uniform fixed-mark estimate is used after taking the limit.

Fix `q,m`. The finite maximum `T_q=max({0} union {tau(q,i):i exceptional})` lies below one. The native test floor, with its original exterior cosine, supplies `c_q>0,Y_q>=1` for the entire family. Thus every exceptional diagonal term has nonnegative real part for `Y>=Y_q`, and each chosen term contributes at least

\[
 c_qY^{\tau_{q,i}}|R_{q,i}(m)|^2.
\]

The complete regular price at the level dyad with lower endpoint `q/2`, and the singleton interval `[m,m+1)`, pays the actual principal and incoming components by a fixed multiple of `1+log^2(2Y)`. The complete holomorphic singleton price is bounded independently of `Y`. For `tau>3/4`, choose `v=(tau+3/4)/2`, `delta=1-v`; then `3/4<v<tau`, `delta<1/4`. The paid trace implies `c_q|R|^2*Y^(tau-v)<=C` for every sufficiently large `Y`. Its unbounded positive power forces `R=0`, and `rhoK=2R` gives the actual native coefficient vanishing. No `hJ`, recurrence premise or spectral-gap premise is introduced.

The resulting vanishing annihilates every high slot on both physical traces, even after arbitrary common Mellin modulation. It restores the full native interval energy from the retained `tau<=3/4` sum. The elementary transport is

\[
 E(L,Y,\omega;a,b;t)\le\max(1,Y/X)^{3/4}E(L,X,\omega;a,b;t)
 \qquad(X,Y>0,\ a>0).
\]

For every `epsilon>0` there is `C_epsilon>0`, chosen before `j,a,b,Q,Y,omega`, such that

\[
 E(L_Q,Y,\omega;a,b;0)\le
 C_\varepsilon[(1+M)(1+Y)]^\varepsilon(Q+M+Y)M
\]

for `2^j<=a<=b<=2^(j+1)`, `Q,Y>0`. Concretely take `delta=epsilon/2`, use the paid initial constants `c,K,Y0`, and let `P` be the `delta` logarithmic allowance constant. The proof selects

\[
 C_0=32C_{\rm sieve}Y_0^{3/4},\qquad
 C_1=K(1+2P)/c,\qquad C_\varepsilon=\max(C_0,C_1).
\]

For `Y<Y0`, the short-interval unit estimate is `32*C_sieve*(Q+M)*M`, and the preceding transport costs at most `Y0^(3/4)`. This is a bound for the original short interval, not an arbitrary-coefficient use of J.

For every fixed `epsilon>0,A>=0`, the actual full-window T08 `pascadiJ` consequently satisfies

\[
 J(S,X;j,\omega)\le C_{\varepsilon,A}
 [(1+Q)(1+M)]^\varepsilon(Q+M)M,
 \quad S\subseteq L_Q,\quad 0<X\le A(Q+M).
\]

The chosen constant is `K*(1+A)^(epsilon/2)*(1+A)`, where `K` is the preceding initial constant at `epsilon/2`. A subset is dominated using nonnegative actual slot energies. With `Q<=B*M`, the full allowed range `X<=A*max(M,Q^2/M)` follows by replacing `A` by `A*max(1,B)`.

For the recurrence set `B_l=2^(l-1)*pi*M*Y/Q`, `0<=l<6`. For every `epsilon>0` there are `A_epsilon,D_epsilon>0` and `Y0>=1`, chosen before all scales, endpoints and phases, such that

\[
 E(L_Q,Y,\omega;a,b;0)\le
 A_\varepsilon\sum_{l<6}\max_{a\le u\le b}E(L_{B_l},Y,\omega;a,u;0)
 +D_\varepsilon[(1+M)(1+Y)]^\varepsilon(Q+M+MY/Q)M.
\]

This holds for `Y>=Y0`, every real `Q>0,omega`, and every allowed common interval. The actual Lean maximum runs over `u=min(b,n+1)`, `a<=n<=b`; it contains all nonempty prefixes, while the omitted empty prefix has energy zero. It is taken after the full level-and-slot sum. No spectral-label-dependent or level-dependent endpoint is substituted.

Use `delta=epsilon/2` in the paid recurrence with constants `c,K,D,Y0`, and let `L` be the `delta` logarithmic allowance constant. Put `Z=2+16*pi`, `W=Z+1`. The source gives the explicit choices

\[
 A_\varepsilon=K/c,\qquad D_\varepsilon=(6K+40DL)W/c.
\]

Indeed the six return scales are at most `16*pi*M*Y/Q`; the four real input shoulders `2^l*Q/4`, `0<=l<4`, are at most `2Q`. Each is at most `Z*(Q+M+M*Y/Q)`. There are exactly six child additive costs and ten paid regular costs; the exterior normalization contributes the factor four. Multiplying the two `delta` costs gives `epsilon`, entirely in the additive term. The child coefficient has no logarithmic or small-power multiplier. For a parent interval `(Q,16Q]`, apply this dyadic result separately at `2^b*Q`, `0<=b<4`.

The unbounded-ratio critical range is deliberately outside this package. The separate conditional critical induction requires `forall q,i,m>0, tau(q,i)>1/2 -> rhoK(q,i,m)=0`. The current package supplies only the same statement with `3/4`. This is a substantive input difference and cannot be erased by its recurrence, by the finiteness of each fixed exceptional family, or by renaming coefficient support as a global gap. The manuscript's `7/32` provider remains separate.

Dependency selection: use the existing `regular-paid-recurrence-r2` source SHA-256 `f8b012e5afc0e35422a4662d0152eaaff01fd99a40443573a09b66c91de95e81`, which directly imports the reviewed initial spectral projection. All six source hashes and the selected external import hashes are recorded in `FREEZE.json`. See `MANUSCRIPT_AUDIT.md` for the manuscript comparison and limits.
