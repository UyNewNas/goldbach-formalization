# Part 5: current Chen mean ledger and scale audit

## Status and frozen inputs

This ledger fixes the **entire current eleven-term lower-mean obligation**. It
does not assert that its analytic row estimates, the adopted finite table, or
the final `hLower` have been proved.

- Formalization baseline: `1a80c1bcce67886f699d097fc37fd245cd3620bf`,
  from `codex/variable-envelope-boxes`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes` at
  `ba6ec11d800eccc54406490631895e174de85766`.
- Main body: `paper/source/manuscript-body.tex`, Git blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Current constants:
  \(K=8452171/1250000=6.7617368\),
  \(c=49044063/25000000=1.96176252\).
- The normalization is the repository's literal `singularNormalization N`.
  It uses \(C_N N/\log^2N\), with **no leading factor two in \(C_N\)**.
- Scope: actual current cutoffs \(a=417/5000\), \(h=19/125\),
  \(d=59/250\), and cube-root cutoff \(1/3\). The old
  `chenFixedElevenWeight` and `chenUpsilon1` through `chenUpsilon11Full`
  have different cutoffs and are not aliases for these objects.

Source authority is [CURRENT_MANUSCRIPT_MAP.md](CURRENT_MANUSCRIPT_MAP.md),
[CurrentMainTheorem.lean](../ImbalancedChen/CurrentMainTheorem.lean),
[CurrentNumericalTransfer.lean](../ImbalancedChen/CurrentNumericalTransfer.lean),
and the pinned manuscript sources listed in the final section. The baseline
already proves the current pointwise weight, same-region paired injection,
and actual additive-prime count bridge. Its map explicitly leaves the
current signed mean and adopted certificate semantics open.

The new companion modules are
[CurrentChenMeanLedger.lean](../ImbalancedChen/CurrentChenMeanLedger.lean),
[CurrentChenLowerScale.lean](../ImbalancedChen/CurrentChenLowerScale.lean),
and [CurrentChenBuchstabRefinement.lean](../ImbalancedChen/CurrentChenBuchstabRefinement.lean).
Their finite identities, scale transfer, and genuine Buchstab lower barrier
are independent work toward this obligation. The mean ledger supplies
actual prime-source identities for all eleven rows, including the moving
cutoffs and selected last pair in rows seven through eleven. These are
identities, not the missing mean estimates. The Buchstab module now proves
the manuscript's literal \(11/20\) barrier for the actual pinned function
on \([7/3,\infty)\), with strict compilation, bundled kernel replay and
transitive axiom audit passed at
`db97d0fe03250f4d9a8aea34b23e9c20f67010b8`. See
[CHEN_P5_BUCHSTAB_HANDOFF.md](CHEN_P5_BUCHSTAB_HANDOFF.md).
This does not certify the retained fibre quadrature. The current finite
and scale validation status is recorded in
[CHEN_P5_ROUND2_HANDOFF.md](CHEN_P5_ROUND2_HANDOFF.md); these components do
not close the missing analytic rows. The independently verified
[CurrentChenInitialSource.lean](../ImbalancedChen/CurrentChenInitialSource.lean)
now supplies the actual S1 source comparison, exact singular-series
identifications, fixed-ratio sieve coefficient and negligible prime-factor
correction. The separate `CurrentChenInitialMean.lean` remains an
uncompiled candidate, with its supplier validation backlog recorded in
the round-2 handoff; it is not an adopted endpoint certificate.

The later fixed P0 acceptance
`c9f407efe66240c08c2e8a678330ba7b98b74db5` also verifies P2's actual
first-cell certificate and its real-variable Buchstab bridge. This
first-cell result is received in the round-2 handoff with its complete
compiler-confirmed types. All 17,572 adopted cells and the actual
U6/U11 arithmetic parent remain separate requirements.

## 1. Carrier, quotient semantics, and the unchanged factor four

For a natural target \(N\), put

\[
 \mathcal P_N=\{P<N:P\text{ prime},\ (P,N)=1\},\qquad n=N-P.
\]

This is exactly

~~~lean
def chenAdditivePrimeCarrier (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun P => Nat.Prime P ∧ Nat.Coprime P N
~~~

Every entry below sums over this **same unweighted prime carrier**. A prime
\(P\) occurs once in the outer sum. A tuple inside a row retains that row's
original multiplicity. The carrier gives \(n>0\); it does not remove \(n=1\).
Replacing \(P<N\) by \(P\le N\) is harmless only by the already-proved
`mem_chenAdditivePrimeCarrier_iff_le`: primality and coprimality make the
endpoint impossible.

For real \(y\) and natural \(b,n\),

\[
 Q_b(y;n)=\mathbf1_{b\mid n}\mathbf1_{P^-(n/b)\ge y}.
\]

The Lean predicate is `ChenQuotient b y n`. Its roughness is inclusive:
every prime divisor of the literal natural quotient is at least \(y\).
The quotient one is permitted, with vacuous roughness. The tuple definitions
use actual prime divisors of \(n\); their membership theorems identify exactly
the nonzero quotient summands. Distinctness comes from the strict tuple order
or the disjoint half-open bands, rather than from an omitted multiplicity
factor.

Write

\[
 A=N^a,\quad H=N^h,\quad D=N^d,\quad C=N^{1/3},
 \qquad H_N=\operatorname{singularNormalization}(N).
\]

Here \(H\) is a **cutoff**, while \(H_N\) is the **normalization**. The table
defect \(H_{248}\) or \(H_{430}\) is a third distinct object.

The actual total is

~~~lean
W_N = currentChenPairedPrimeSum N (E N)
H_N = singularNormalization N
~~~

The existing finite bridge is

\[
 W_N\le 4D_{1,2}(N)+246\,\frac{N}{N^a-1}+4.
\]

For \(N^a\ge2\), the stated error is at most
\(492N^{1-a}+4\). The baseline proves that this is \(o(H_N)\), uniformly
over every pair predicate. In particular,

~~~lean
eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12
  (epsilon : ℝ) (hepsilon : 0 < epsilon) :
  ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop,
    currentChenPairedPrimeSum N E - epsilon * singularNormalization N ≤
      4 * (D12 N : ℝ)
~~~

This is a proved **upper bound on the weight in terms of the count**. The
missing matching estimate is

\[
 W_N\ge (4c-\eta)H_N,\qquad
 4c=\frac{49044063}{6250000}=7.84705008,
\]

eventually for even targets, for every \(\eta>0\), with the adopted mask.
A bound \(W_N\ge(c-\eta)H_N\) has the wrong scale.

The current Lean bridge improves the manuscript's sufficient
\(2032N^{1-a}+4\) exception budget by using only the needed one-sided upper
weight bound \(246\). This changes neither the weight nor the normalization.
There is no obsolete lower receiver-size band in the current bridge.

## 2. The complete eleven-row ledger

Let \(\widetilde Y_6=Y_6-Y_6(E_N)\) and
\(\widetilde Y_{11}=Y_{11}^{\rm full}-Y_{11}(E_N)\).
These differences are exactly cardinalities of the corresponding complement
filters. No truncated natural subtraction is used in the signed identity.

In the table, every displayed prefix variable is prime. Each quotient
indicator includes divisibility of the full displayed prefix product.
The “mean direction” is the direction needed for a lower bound on \(W_N\).

| Row | Actual receiver summand and support | Coefficient in \(W_N\) | Mean direction |
| --- | --- | ---: | --- |
| 1 | `chenY1 n A`: \(Q_1(A;n)\) | \(+3\) | Lower bound \(L_1\) |
| 2 | `chenY2 n H`: \(Q_1(H;n)\) | \(+1\) | Lower bound \(L_2\) |
| 3 | `chenY3 n A C`: \(\sum_{A\le p<C}Q_p(A;n)\) | \(-1\) | Upper bound \(U_3\) |
| 4 | `chenY4 n A D`: \(\sum_{A\le p<D}Q_p(A;n)\) | \(-1\) | Upper bound \(U_4\) |
| 5 | `chenY5 n A H`: \(\sum_{A\le p_1<p_2<H}Q_{p_1p_2}(A;n)\) | \(+1\) | Lower bound \(L_5\) |
| 6 | `chenY6Selected n A H D (fun t => ¬ E_N t)`: \(\sum_{A\le p_1<H\le p_2<D,\ \neg E_N(p_1,p_2)}Q_{p_1p_2}(A;n)\) | \(+1\) | Lower bound for the **retained** sixth count \(L_6\) |
| 7 | `chenY7 n N D`: \(\sum_{D\le p_1<p_2<\sqrt{N/p_1}}Q_{p_1p_2}(p_2;n)\) | \(-2\) | Upper bound \(U_7\), counted twice |
| 8 | `chenY8 n N A C`: \(\sum_{A\le p_1<C\le p_2<\sqrt{N/p_1}}Q_{p_1p_2}(p_2;n)\) | \(-1\) | Upper bound \(U_8\) |
| 9 | `chenY9 n N H D`: \(\sum_{H\le p_1<D\le p_2<\sqrt{N/p_1}}Q_{p_1p_2}(\sqrt{N/(p_1p_2)};n)\) | \(-1\) | Upper bound \(U_9\), with its actual tuple multiplicity |
| 10 | `chenY10 n A H`: \(\sum_{A\le p_1<p_2<p_3<p_4<H}Q_{p_1p_2p_3p_4}(p_2;n)\) | \(-1\) | Upper bound \(U_{10}\) over the whole retained domain |
| 11 | `chenY11Selected n A H D (fun t => ¬ E_N t)`: \(\sum_{A\le p_1<p_2<p_3<H\le p_4<D,\ \neg E_N(p_3,p_4)}Q_{p_1p_2p_3p_4}(p_2;n)\) | \(-1\) | Upper bound for the **retained full-range** eleventh count \(U_{11}\) |

Define \(\Upsilon_j(N)\) by summing that row over \(P\in\mathcal P_N\),
with \(n=N-P\). In `CurrentChenMeanLedger` these are
`currentChenUpsilon1` through `currentChenUpsilon11`; only rows six and
eleven take the mask argument. Their complete identity is

\[
 \begin{split}
 W_N={}&3\Upsilon_1+\Upsilon_2-\Upsilon_3-\Upsilon_4
       +\Upsilon_5+\Upsilon_6\\
     &-2\Upsilon_7-\Upsilon_8-\Upsilon_9-\Upsilon_{10}-\Upsilon_{11}.
 \end{split}
\]

The scalar functional, in **Chen-quarter units**, is

\[
 \mathcal C=\frac14
 (3L_1+L_2-U_3-U_4+L_5+L_6-2U_7-U_8-U_9-U_{10}-U_{11}).
\]

The coefficient absolute sum is \(14\), and the quarter-normalized root
norm is \(14/4=7/2\). Consequently eleven oriented row errors each of size
\(\delta H_N\) cost at most \(14\delta H_N\) in the weight, or
\((7/2)\delta H_N\) in the count coefficient.

### The exact eventual row obligations

A complete analytic insertion must produce the eleven estimates on the
same finite construction. For every \(\delta>0\), after one common threshold
and for every even \(N\),

\[
\begin{array}{rclcrcl}
 (L_1-\delta)H_N&\le&\Upsilon_1(N),&
 &(L_2-\delta)H_N&\le&\Upsilon_2(N),\\
 \Upsilon_3(N)&\le&(U_3+\delta)H_N,&
 &\Upsilon_4(N)&\le&(U_4+\delta)H_N,\\
 (L_5-\delta)H_N&\le&\Upsilon_5(N),&
 &(L_6-\delta)H_N&\le&\Upsilon_6(N,E_N),\\
 \Upsilon_7(N)&\le&(U_7+\delta)H_N,&
 &\Upsilon_8(N)&\le&(U_8+\delta)H_N,\\
 \Upsilon_9(N)&\le&(U_9+\delta)H_N,&
 &\Upsilon_{10}(N)&\le&(U_{10}+\delta)H_N,\\
 \Upsilon_{11}(N,E_N)&\le&(U_{11}+\delta)H_N.&&&&
\end{array}
\]

A certificate may instead provide a joint bound on
\(\Upsilon_{10}+\Upsilon_{11}\). That is acceptable if the actual joint
family and its error budget are stated and proved. One must not invent two
independent endpoints from the single selected `U10_plus_U11` field.
The finite `currentChenPairedPrimeSum_ge_of_joint_last_bounds` consumes
that joint inequality directly. Its normalized companion uses
\((b_{10,11}+2\delta)H_N\) for the combined last two rows, so the complete
weight error remains \(14\delta H_N\).

These formulas specify proof obligations, not accepted unproved hypotheses
of a claimed completed theorem. Finite signed assembly of supplied bounds is
only an independent lemma until every required analytic bound is discharged.

## 3. The adopted mask, pairing, and sign-sensitive deletion

The mask is a fixed finite rational rectangle family, pulled back for each
target:

\[
 E_N(p,q)\quad\Longleftrightarrow\quad
 \left(\frac{\log q}{\log N},\frac{\log p}{\log N}\right)\in E_0\cup E_1.
\]

The predicate takes the **increasing prime pair** \((p,q)\); its rectangle
coordinates are in the **opposite order**, larger exponent first.
The sixth row uses \(E_N(p_1,p_2)\), while the eleventh uses
\(E_N(p_3,p_4)\), i.e. `E t.2` in the grouped four-prime tuple.

The adopted records identify \(6091\) cells in \(E_0\) and \(11481\) cells
in \(E_1\), total \(17572\). The inherited number \(17772\) is a transcription
error, not another mask. The `E1` record has \(227\) crossing cells with zero
saved lower floors and \(11254\) positive cells. A zero saved floor does
**not** mean that the actual sixth-row count is zero.

The finite pairing already proves, for squarefree \(n\),

\[
 Y_{11}(E_N;n)\le Y_6(E_N;n).
\]

The map sends a four-prime tuple to its last pair. Quotient roughness forces
its first pair to be the two smallest prime factors of \(n\), proving
injectivity. The finite complement identities need no squarefreeness; the
pointwise inequality uses this injection only on the squarefree part.

There are two valid accounting operations:

1. Prove a lower estimator for the retained sixth count by restricting its
   original lower construction to the complement. Pay an upper bound on the
   **discarded saved lower estimator**.
2. Prove an upper estimator for the retained eleventh count by restricting
   the already proved **positive parent majorant** to the same complement.
   Remove a lower bound on that majorant's removed mass.

One cannot infer a retained lower bound by subtracting a lower bound for
the removed actual sixth count. Nor can one infer a better negative-cost
upper bound by subtracting an upper bound for a removed actual eleventh
count. The injection alone supplies neither analytic operation.

For the baseline complement restriction, the source checks that the
selected parents use the switched option of the `n48` cover and avoid all
`priority40000` replacements. If \(A_B\) is a saved parent mass and \(s_B\)
its feedback slope at \(K_0=6.7619\), the required inequality is

\[
 0\le s_B\le A_B/K_0,\qquad
 A'_B=A_B-(K_0-K)s_B\ge(K/K_0)A_B.
\]

It gives an explicit positive density majorant that can be restricted;
a global minimum or maximum without such a decomposition cannot be cropped
cell by cell. Positive savings may omit nonnegative parts. Upper bounds
for negative costs must cover their whole retained domains.

## 4. Wu product constraint and actual endpoint checks

The frozen source audit [Wu] distinguishes two weights. In Wu's contracted
comparison, with \(B=1/2-2a\), the corrected positive sixth range retains

\[
 p_1p_2<N^B,
\]

and the contracted eleventh range retains \(p_3p_4<N^B\). The removed sets
use the complementary non-strict condition, including equality. Projection
to the last pair preserves that exact condition, so the same generic paired
injection proves the simultaneous deletion valid.

The current project instead proves its rectangular sixth row together with
the **full eleventh endpoint \(p_4<N^d\)**. Accordingly:

- Do not add the old product triangle to the current sixth definition while
  continuing to use its rectangular saved lower certificate.
- Do not contract the current negative eleventh range without its paired
  positive deletion.
- If the Wu product-gate specialization is used as a separate lemma, the
  same strict retained / non-strict deleted endpoint must be used in both
  places.
- The present ledger's claim about the published correction is based on the
  pinned project audit [Wu]; it is not an independent fresh review of the
  journal PDF.

At the classical fixed half-level the ordinary lower contribution is zero
when \(s=(1/2-t-u)/a\le2\). This does not prove that Wu's double-sieve
function \(h(s)\) itself is zero below two. The current selected lower
insertion deliberately uses zero there.

The current sixth-row level is different. With

\[
 v(t)=\min((1+t)/2,57/64-3t/2),
\]

its actual positive region is \(v(t)-t-u\ge2a\). The frozen audit shows
that the extra candidate levels do not win anywhere in the current
sixth rectangle, so \(V=v(t)\) there. For example
\(t=11/50,\ u=7/50\) is in the old classically deleted strip but has current
\(s=2675/1112>2\). Its legitimacy requires the full current eleventh range
and the current level/support proof, rather than a continuation of a lower
formula outside its domain.

Other endpoints to retain:

- Row seven has a strict square-root switching cap and coefficient two.
- Row eight owns equality at \(p_2=N^{1/3}\).
- Row nine owns equality at \(p_2=N^d\), uses
  \(\sqrt{N/(p_1p_2)}\) as its quotient cutoff, and retains its tuple
  multiplicity. The source inequalities do not turn it into a global
  indicator.
- Rows five and ten use strict internal increasing order; no factorial
  division is available without the required reindexing and diagonal proof.
- The unit correction remains \(+4\) in the four-times-count bridge.
  Nonrough receivers need only have nonpositive weight there.

## 5. Required actual analytic constructions and ownership

The following are the adopted occurrences from [M] and [L]. They are more
specific than “use an upper/lower sieve.”

| Occurrence | Required selected analytic construction | Receiving inputs |
| --- | --- | --- |
| \(L_1,L_2\) | The two actual causal lower starts at \(a,h\), ordinary cap \(249/448\), preserving inherited third/fourth/fifth decisions; the adopted fourth-own-cube restoration is outside the old retained fourth/fifth regions | Part 1 actual lower policy, support and genuine historical integrals; Part 2 lower certificate; Part 3 original-prime endpoint/distribution |
| \(U_3,U_4\) | \(H_{430}\) at \(\max(2,L/a)\), \(L=v(t)-t\), in the enhanced range \(t<57/224\); the remaining third-row tail uses the half-level limit from below | Parts 1–3; same finite table and actual quotient families |
| \(L_5,L_6\) | \(h_{248}\), only where \(L/a\ge2\), on the actual pair families; lower option zero below two; row six restricted to the adopted mask complement | Parts 1–3 and Part 2 same-mask cells |
| \(U_7,U_8,U_9\) | Positive labelled product masses with the original slot constraints, unit cases and multiplicities; common coefficient \(K\) | Part 4-A same-\(\rho\) coefficient and density, together with Part 3 product distribution and the actual mass computation |
| \(U_{10},U_{11}\) | One common full four-prefix partition, minimum of switched and each eligible ordinary upper option; retain all full/selected-square gates and the prime ceiling; priority children replace parents; restrict only the eleventh family to the mask complement | Parts 1–3 plus Part 4-A; Part 2 whole negative-cost cover and restrictable-majorant certificate |
| Finite \(H/h\) feedback | Real estimates on nonnegative marked families at one common total level \(Q\), with all child physical levels and ceilings preserved | Part 1/Part 5 typed family construction; Part 3 analytic estimates; Part 2 finite action/table certificate; Part 4-A common \(K\) |

For the two pair occurrences, with \(t>u\),

\[
 \mu=25/128,\quad \Lambda=153/256,\qquad
 V=\begin{cases}
 \max(v(t),v(t+u),\Lambda-3a/8),&t<\mu,\\
 v(t),&t\ge\mu,
 \end{cases}\quad L=V-t-u.
\]

Eligibility requires the actual square gates and stable ceilings, not merely
a favorable numeric \(L/a\). On the selected \(L_6\) rectangle this reduces
to \(V=v(t)\), as described above.

For decreasing four-prefix exponents \(x>y>z>w\), the switched option is

\[
 K\,\omega((1-S_4)/z)/z,
\]

and an eligible ordinary option is

\[
 4\bigl(1-H_{248}(\max(2,L/w))\bigr)/L.
\]

The source's selected `n48` cost covers \(1190700\) ordered rows including
tied-bin simplices. Its \(40000\) priority parents have \(516779\)
replacement children. These are required coverage counts in the records,
not fresh Lean enumerations performed by this ledger.

### Lower coefficient and original-prime endpoint

The actual lower physical coefficient attaches beta-minus to a positive
rough coefficient and beta-plus to a negative one. The needed statements
are a pointwise minorant and a lower density estimate for that **same**
coefficient. The lower full-to-rough projection has the opposite direction
from the upper one; coefficient order alone does not prove its density
bound.

The baseline already has generic actual lower attachment/projection
suppliers in `ActualLowerSmallRoughAttachment`,
`ActualLowerFirstExitDensityProjection` and
`ActualLowerNormalizedRhoError`. These are not instantiations of the
adopted historical lower policies.

The mean estimate also needs the original-prime endpoint conversion, not
only smooth individual factor slots. [M, Lemma current-sharp-prime] requires

\[
 \sum_q\rho_N(q)
   \left(\pi(N;q,N)-\frac{\pi(N)}{\varphi(q)}\right)
   =O_A(N/\log^A N).
\]

It retains the endpoint collar after summing all divisors, the original
small-product trim, and the exact-coprime correction. Since \(N>2\) is
even, the endpoint \(p=N\) is absent, so no zero-difference divisor count
is introduced. These analytic inputs are assigned to Part 3; a generic
finite remainder identity is not the estimate.

### Finite feedback, without a circular lower-count hypothesis

The source uses a seed \(H\ge2327/100000\) on \([1,11/5]\), obtained from
four finite steps starting at \(0.02\). Its bank has \(70\) one-step and
\(36\) repaired two-step actions. The final arrays have \(200\) closed
cells at endpoints \(1+i/50\). Every right-hand side takes preceding
generation estimates; alternatives are maximized, not added.

Only \(U_3,U_4\) receive the final \(430\)-round table. The \(248\)
occurrences in \(L_5,L_6\) and ordinary four-prefix options remain the
adopted \(248\) occurrences. Replacing the second causal start also removes
its entire old \(H_{248}\) least-prime correction.

Every child keeps the same total \(Q=N^\lambda\). For a singleton child
with relative exponent \(u\),

\[
 L'=L(1-u),\qquad
 \alpha'=1+\frac{\alpha-1}{1-u},\quad
 \alpha=(1-\log_N B)/L\ge2.
\]

For a two-prime child replace \(u\) by \(u+v\). In particular \(\alpha\)
cannot be reset to two after switching. The repaired two-step ordinary
domains retain \(2v<1\) and \(v+2u<1\); the excluded part receives positive
product cost, not ordinary feedback.

Finite depth is not a substitute for a simultaneous finite approximation.
The source bounds transition mass by \(12\) and root norm by \(7/2\);
local oriented error propagates at most
\(\delta(12^{441}-1)/11\) before quarter normalization. A common nested
refinement must be chosen inside the fixed reserve, with positive leaf
exponents and zero-mass cases controlled by absolute errors.

## 6. Concrete selected numerical records and exact arithmetic

The selected numeric record is identified by source references and fields,
not its filename alone:

- `global-selected-numeric-completion-20261010.json` binds the baseline
  direct root ledger and the \(29\) finite obligations. Its `selected_c`
  is the **old baseline** \(12258223/6250000=1.96131568\).
- `corpus-renewal-improvement-assembly-20261010.json` selects
  `selected_version = "7/3 v2 replaces12/5 candidate; gains not added together"`
  and binds the current `safe_K`, `safe_c`, raw lower endpoint, both
  reserves, the exact mask, and the v2 certificate/review.
- The adoption chain in [M] explicitly supersedes the old lower endpoint
  while retaining the baseline analytic inputs. Neither scalar JSON file
  is already a Lean proof of its analytic interpretation.

### Initial reconstruction fields

The baseline record's `direct_lower_terms` fields have the following exact
numerators on the common denominator \(Q_{80}=2^{80}\). These are
**initial reconstruction inputs before the listed start, history,
priority, feedback and mask changes**; they are not eleven ready-to-use
final current analytic suppliers.

| Field | Numerator on \(Q_{80}\) | Signed multiplicity |
| --- | ---: | ---: |
| `L1` | 16277054284462455830437051 | \(3\) |
| `L2` | 8586547972866441938526945 | \(1\) |
| `L5` | 2870595040977434131076026 | \(1\) |
| `L6` | 3650774173156900914101685 | \(1\) |
| `U3` | 24556212011015763559960381 | \(-1\) |
| `U4` | 16995904880905900972965867 | \(-1\) |
| `U7` | 1672464594622060236183097 | \(-2\) |
| `U8` | 4904703865205402441361491 | \(-1\) |
| `U9` | 3937512077512215599969887 | \(-1\) |
| `U10_plus_U11` | 816855501842065519420698 | \(-1\), applied to the joint cost |

Their signed sum divided by four is exactly

\[
 \frac{9382962514662675908971291}{4835703278458516698824704}.
\]

The direct reconstruction then applies each of the following once:
priority replacements; changed ordinary start minus the full obsolete
\(H_{248}\) correction; the six selected \(I_{3,4,5}\) values with weights
\(3\) at \(a\) and \(1\) at \(h\); selected slanted restoration; fixed-\(K\)
feedback; only the two \(U_3/U_4\) table differences; and both paired masks.
The adopted conservative endpoint is slightly below the direct
reconstruction. That surplus is not another gain to add.

### Same-mask v2 refinement

For \(B=[t_l,t_r]\times[u_l,u_r]\), define

\[
 Z_B=\min\!\left(u_l,\frac{3(1-t_r-u_r)}{13}\right),\qquad
 M_B=\log(t_r/t_l)\log(u_r/u_l).
\]

The certificate must prove \(Z_B>a\) for **every adopted cell** and the
inner-fibre geometry. The actual Buchstab statement required is

\[
 \omega(s)\ge11/20\quad(s\ge7/3).
\]

Relative to the already paid \(\omega\ge1/2\), its additional quarter-unit
mass is

\[
 G_B=\frac K{80}M_B
 \left[\frac1a-\frac{1+\log(Z_B/a)}{Z_B}\right].
\]

There is no extra factor two and no permutation factor. The source adopts

\[
 g=\frac{558583}{10^9}.
\]

The literal discarded saved sixth estimator is

\[
 L_{\rm lit}=\frac{11290806845175652020270}{4Q_{80}}
 <\lambda=\frac{466977}{200000000}.
\]

Thus the current retained sixth lower endpoint in the source ledger is the
old `L6` endpoint minus \(4\lambda\), namely

\[
 \frac{1421673188323272382945058469141}
      {472236648286964521369600000000}.
\]

Again, \(L_{\rm lit}\) and \(\lambda\) concern saved estimators, not the
removed actual count. The source retains both a literal saved-floor replay
and an independent upper proxy. Their equality/inequality to the same
adopted cells is part of Part 2's delivery.

The recovered old payment and the sole current raw increment are

\[
 \frac{2372094}{10^9}-\lambda=\frac{37209}{10^9},\qquad
 \Delta=g+\frac{37209}{10^9}
       =\frac{37237}{62500000}.
\]

Each of the two distinct reserves increases by
\(\Delta/8=37237/500000000\). The net increase is
\(3\Delta/4=111711/250000000\).

The old \(12/5\) candidate is the superseded evaluation of this same
increment. It must not be added to \(g\) or \(\Delta\). The mask, its parent
assignments, the \(248/430\) occurrence policy and \(K\) are unchanged.

### Final scalar ledger, before any analytic proof claim

The current adopted raw endpoint and each reserve are

\[
 R=\frac{1345983686820460038728276256001756964104092721}
          {685738127494661151198444592354557952000000000},
 \qquad
 B_0=\frac{2913305608548241964824517919947906098888971}
           {5485905019957289209587556738836463616000000000}.
\]

Exact subtraction yields

\[
 R-2B_0-c=
 \frac{13457260926863633771775678584711245753}
      {2742952509978644604793778369418231808000000000}
 =4.906122463989873\ldots\times10^{-9}>0.
\]

The base-plus-\(\Delta\) identity, both reserve updates, the retained
sixth endpoint, the initial signed reconstruction, and this positive
slack were independently recomputed with Python `fractions.Fraction` in
this audit. That check used no floating-point decision. It did **not**
rerun the \(17572\) cells, all quadratures, the delay-function meshes, the
finite action graph, or Lean.

## 7. Common \(K\), dependency boundary, and exact handoff

Part 5 uses Part 4-A's common \(K\), but does not require Part 4-B's final
bad-semiprime `hUpper`. The dependency is the positive product consequence
in [M, Proposition current-positive-product]:

\[
 \limsup \frac{\log N}{N}X_W\le J
 \quad\Longrightarrow\quad
 \limsup \frac{\#_W\{m<N:N-m\text{ prime}\}}{H_N}\le KJ.
\]

It applies to fixed finite nonnegative labelled product families with
bounded rank, positive fixed prime exponents, and the admitted geometry.
A density number alone does not prove this proposition. Part 5 must also
receive or combine the same-\(\rho\) pointwise majorant/support, Part 3's
signed physical distribution, coprime correction, actual mass asymptotic,
and smoothing/endpoint losses. The family may differ from the ordered
bad-semiprime family; `RealHalfProductMassSuppliers` alone is not a supplier
for every switched \(U_j\).

| Missing input at this baseline | Required producer / recipient | Completion criterion |
| --- | --- | --- |
| The concrete adopted \(E_0,E_1\) cell data and log-coordinate pullback \(E_N\) | Part 2 → Part 5, Part 0 | Exact cells, endpoints, coordinate order, parent ownership and no-duplicate proof; finite mask bound to the adopted certificate |
| The complete actual lower policies at \(a,h\), historical joint integrals and restoration | Part 1 → Part 5 | Policies instantiated by adopted tables; causal history and all physical support gates proved; each saved integral identified with the actual density |
| Real finite \(H/h\) action semantics and adopted generation insertion | Part 1 / Part 5 with Part 2 | Derive estimates on actual marked families from preceding generations; preserve levels, full/selected squares and ceilings; common approximation |
| Adopted lower integral and table certificate, including same-mask v2 | Part 2 → Part 5 | One-sided integral inequalities for the actual functions and complete negative covers; literal lower-floor payment; \(7/3\) fibre bound; exact \(R,B_0,c\) accounting |
| Original-prime sharp endpoint and selected quotient distribution | Part 3 → Part 5 | Actual prime sequence, physical moduli, common interval/phase and moving residues; absolute all-even error with one threshold |
| Positive switched-product consequence at the exact shared \(K\) | Part 4-A + Part 3 → Part 5 | Same coefficient in pointwise bound, density and distribution; genuine labelled product masses; no use of Part 4-B `hUpper` as a premise |
| All eleven final retained row estimates | Part 5 → Part 0 | Prove every oriented row or explicit joint row bound on the adopted construction; assemble the actual \(W_N\) at coefficient \(4c\) |
| Final `hLower` | Part 5 → Part 0 | Combine the proved mean with the already proved uniform squareful/unit bridge and correctly divide by four |

The order of choices is: fixed query graph, compact/tail accuracy, causal
caps and support reserves; common beta/rough and fine-label parameters;
finite divisor orders, permitted product trim and logarithmic accuracy;
then one sufficiently large threshold for all even \(N\). The finite
certificate does not permit policies whose past decisions change when
later primes are revealed, or an almost-all-target distribution result in
place of an all-even result.

The final interface must have exactly the existing type:

~~~lean
∀ epsilon : ℝ, 0 < epsilon →
  ∀ᶠ N in Filter.atTop, Even N →
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
~~~

For example, after the actual row constants give at least \(4c\), choose
\(\delta=\epsilon/7\); the eleven-row error is at most \(2\epsilon H_N\).
Use another \(2\epsilon H_N\) for the already proved count bridge. Then
\(4D_{1,2}(N)\ge(4c-4\epsilon)H_N\), giving exactly the required
`hLower`. This scale calculation neither supplies the row estimates nor
changes the fixed certificate reserves.

## 8. Reuse and source evidence

The baseline sources relevant to reuse are:

- `CurrentChenPointwise.currentChenElevenWeight_le_four_indicator`:
  all squarefree \(n\le N\), including the unit and \(N=1\).
- `CurrentChenPairedDeletion.chenY11Selected_le_chenY6Selected` and
  `currentChenPairedWeight_le_four_indicator`:
  arbitrary same-region injection, not a numerical mean.
- `CurrentChenSummedBridge`:
  actual additive-prime carrier, squareful correction, unit removal,
  and uniform normalized weight-to-count error.
- `ChenInitialPrimeSource.chenInitialBoundingSieve_siftedSum_eq_Y1`:
  real initial prime source at arbitrary current cutoff.
- `ChenQuotientPrimeSource.sum_chenY3_eq_siftedQuotientPrimeSource`,
  `sum_chenY5_eq_siftedQuotientPrimeSource` and
  `sum_chenY6_eq_siftedQuotientPrimeSource`:
  generic cutoff identities that can be specialized to current parameters.
  Their old `chenUpsilon...` corollaries cannot.
- `ChenPooledQuotientAP` and the quotient correction/budget modules:
  finite product-modulus pooling and explicit corrections, not the required
  restricted signed distribution estimate by themselves.
- `FirstExitHistoricalLevels` and the actual own-cube integral modules:
  reusable finite history and genuine integral components; their arbitrary
  level functions have not been bound to all current selected tables.
- `EXTERNAL_REUSE.md`:
  the pinned external ordinary BV/PNT/Mertens suppliers do not by themselves
  close the current high-support same-\(\rho\) or full Chen-mean obligation.

The baseline file inventory contains the variable-envelope reference
records; it does not contain the adopted same-mask-v2 cells or their
current lower certificate as Lean data. The manuscript repository does
contain the adopted numerical files. Their absence from the Lean baseline
is an integration/proof obligation, not a claim that the numerical files
cannot be obtained.

All manuscript references below are pinned to
`ba6ec11d800eccc54406490631895e174de85766`:

- [M: main body](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/manuscript-body.tex):
  rows and pairing at lines 562–690; lower coefficient and endpoint at
  692–785; finite feedback/root insertion at 787–973; adopted refinement
  and reserves at 1000–1308; adoption/reproducibility at 1310–1434.
- [L: lower completion module](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/modules/global-chen-lower-completion-20261010.txt):
  sections 2–5 give actual lower coefficient, finite marked-family states,
  all eleven root occurrences and complementary majorant restriction.
  Its old baseline endpoint is superseded by [M].
- [X: lower cross-review](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/modules/final-lower-cross-review-20261010.txt).
- [Wu: product-constraint audit](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/proof-library/source/wu-y6-weight-impact-20261010.txt):
  sections 2–5 distinguish the corrected contracted weight, the full
  current weight, and the actual current pair lower gates.
- [N: baseline selected record](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/verification/data/global-selected-numeric-completion-20261010.json)
  and [its 29 obligations](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/verification/data/global-selected-numeric-completion-20261010-obligations.json).
- [R: adopted refinement assembly](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/verification/data/corpus-renewal-improvement-assembly-20261010.json).
- [Exact reconstruction program](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/verification/replay_selected_ledger.py):
  direct signed root and retained choices at lines 176–230.
- [Adopted refinement replay](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/verification/replay_refinement_author.py):
  literal saved-floor and sole-increment accounting.

The following fetched files were checked byte-for-byte against their Git
blob hashes. Their SHA-256 values are recorded for cross-session handoff;
hash equality is provenance evidence, not a proof of their mathematical
claims.

| File | Git blob | SHA-256 |
| --- | --- | --- |
| `global-chen-lower-completion-20261010.txt` | `2233732a41d6ba65fc1dfbe1b6519b3db1c4bb3d` | `8597fd1dc01d3fc49e5b31d28afeab3cf48e88ae23908fb6777a1c23f5b360e5` |
| `final-lower-cross-review-20261010.txt` | `ec5f0e6bb1259ca67e5ff12ace5bd94d67b80bfd` | `4ca0d6799ff2b9b8616e10ec5ed6c4bae0d881bf4ece09165bc336e4a755ee48` |
| `global-selected-numeric-completion-20261010-obligations.json` | `434be0e085dde5a18ff0f181af828649d39ee1cc` | `0185582f3c2e172320119d3f0f1d818805bccebbafc8f4fff272ee52b86ea6c0` |
| `global-selected-numeric-completion-20261010.json` | `34c8bb0facc3e24597c09d6b2e410e63c344ef5e` | `9101ddb9d109782aa99385cb02895c13cfa3f492306f8f5aab0f576335ab90b8` |
| `corpus-renewal-improvement-assembly-20261010.json` | `154a3d0e73a84d774bc21d3da07a0e337560d11c` | `9254e419145a0a48954c3ca9af1d76a4312dd280dcdbac5bfd216d8b2f49e27c` |
| `replay_selected_ledger.py` | `01f8f0ed811e2c7dc526c544268679446ffd69bf` | `3e83eae04f7ebf8cd185a0c0715feec20793d0a124239df1ead51e2900ff0288` |
| `replay_refinement_author.py` | `9036fd59f2d0b4f95c771664118c9466a700d0d5` | `757bfba400a6d8615b6ee2a399cb5074da535e3027642db3f3774344283ece07` |

### Verification boundary

The first-round documentation audit read the fixed source, checked the eleven supports
and signs against Lean, identified the adopted source/field chain, and
performed the exact scalar arithmetic listed above. It did not establish
the complete actual masked mean. The new row seven through eleven source
adapters and Buchstab argument received independent static mathematical
review; that review is not an elaboration or kernel check.

In that first round, the exact pinned compiler and dependency sources
were acquired, but a local compiler startup attempt was blocked when Lean's `getAppPath` tried
to read `/proc/<pid>/exe`. The environment denied that operation before
elaboration. This is neither a Lean syntax diagnostic nor a successful
build. No permission mechanism was bypassed. That historical startup
result has now been supplemented by actual round-2 verification:
Buchstab, MeanLedger, LowerScale and InitialSource have each passed the
official trust-zero frontend through stock Lake, original bundled
production-module replay and a full defining-module transitive axiom
audit. The recorded inventories cover 111 distinct declarations. The
ordinary first-row eventual mean in InitialMean is still an uncompiled
candidate. Neither inventory proves the complete adopted-mask mean.

The shared project entry point is unchanged. Its default aggregate build
does not import the new modules. Part 0 must either integrate the verified
leaves in its canonical entry point or explicitly build their module
targets and run `verification/parts/p5/ChenP5Audit.lean` together with
`verification/parts/p5/InitialSourceAudit.lean`. The handoff provides those
explicit commands; merely pushing the new files does not establish that
the default aggregate CI checks them.

Existing branch CI runs were also observed failing before their jobs
exposed any executed build steps. The failure alone does not identify a
specific infrastructure cause or establish a Lean failure. The exact run
for the final branch commit, its execution stage, and any accessible logs
must be reported separately. The final Part 5 handoff must give the fixed
commit SHA, each new theorem's full type, the executed Lean/build/kernel/
axiom gates and their results, and every remaining producer input. A
candidate that cannot be compiled remains a candidate; adding the entire
desired mean as an assumption cannot upgrade that status.
