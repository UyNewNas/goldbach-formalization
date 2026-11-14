# S05 independent review: actual regular-paid initial and recurrence

Decision: mathematical source pass for the stated retained-band estimates; select the existing R2 source for use. The originally requested freeze `11260b5287fc3a9a07eff02a4fd8ed152171f51506142fb7878e9a9a280db47c` is the audited predecessor. Its one Lean file uses `paid_initial` and `residual` from the sibling initial-spectra module without importing that sibling. This is a repairable source dependency omission, not a missing analytic estimate. The existing R2 freeze is `d80da5e655ddf99f8ee15655048b1279ee7b519927717a29a797d9127d1980f3`, and its source is `f8b012e5afc0e35422a4662d0152eaaff01fd99a40443573a09b66c91de95e81`. Removing its one added `import ImbalancedChen.Part3OriginalSwitchedInitialSpectra` line reproduces the predecessor text exactly. No author source was edited.

## Reuse and manuscript comparison

Before reviewing the new payment, I read the existing cubic-six, finite-returned-level, trace-projection, holomorphic-error and low-order reviews. The six direct freeze/review pins in the author freeze were rehashed and all match. The approved cubic-six source already supplies the full principal and all-incoming prices on both physical tests, including the principal endpoint t=0 and both continuous half-lines. Its earlier proof and the fullregular12 supplier are not re-proved or credited again here.

I compared medium manuscript commit `9731290e8f53cffda44129906cde6a965eaa869b`, module `paper/source/modules/distribution-medium-completion-20261010.txt`, Git blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §10(v)–(vii), lines 463–481. It requires the matching Fourier convention and the same interval and phase across levels. Drappeau's original §4.2 defines the sixteenfold parent S before Lemma 4.10, then uses the two trace tests in Proof 4.6 and a separate square-root transport in Proof 4.8. The four-entry accounting below is the explicit finite cover needed for this implementation's actual cutoff. It is not an assertion that its six physical windows equal the paper's displayed single window. [Drappeau, Lemma 4.10 and Proofs 4.6–4.8](https://arxiv.org/html/1504.05549v4#S4.SS2)

## Complete payment at one entry scale

Fix 0≤T<1 and ε>0, M=2^j−1/2≥1/2, L(Y)=1+log²(2Y), and the original 2^j≤a≤b≤2^(j+1). Every row uses the same ω and interval [a,b), and both observation frames are infinity. The input test is Φ(Yx); the output test is Φ(Yx)Φ(4π√(mn)/(dQx)). Define C=πMY/Q, A_v=2^v Q/4 for 0≤v<4, and B_l=2^l C/2 for 0≤l<6. U and V are the respective unions of the genuine positive-integer dyads (A_v,2A_v] and (B_l,2B_l].

The imported `regular_dyad` gives one A_ε≥0 before Boolean side, j,a,b,Y,Q,B,ω, with Y≥1 and Q,B>0:

    Σ_(B<d≤2B) (|R_s(d)|+|C_s(d)|)
      ≤ A_ε L(Y) (B+M^(1+ε))M.

R and C are the complete actual principal and incoming contractions, not one mark, one mode, a cumulative spectral cutoff, or a replacement quadratic form. Charging the nonnegative norm cost on U or V by its component dyads is legitimate without disjointness. The input external bump has already been bounded by one in the retained predecessor; this payment therefore needs no second bump factor or sign claim.

For the initial estimate set G=[(1+M)(1+Y)]^ε(M+Y)M, V₀=(Q+M^(1+ε))M, H=Σ_(Q<q≤2Q)|outsideSlot(q)| and U₀=Σ_(Q<q≤2Q)(|R_in(q)|+|C_in(q)|). The exact residual decomposition is H+U₀. The predecessor gives cJ_T≤D(G+V₀)+4(H+U₀). Since U₀≤A_εL(Y)V₀ and L(Y)≥1, the source's coefficient D+4A_ε pays the advertised G+L(Y)V₀ and leaves exactly 4H. Positivity of D ensures the new coefficient remains positive. The holomorphic initial payment was already inside D V₀; it is not discarded.

For recurrence, the exact unpaid decomposition on each side is |high_s|+(|R_s|+|C_s|). Put

    W = M[Σ_l B_l + Σ_v A_v + 10M^(1+ε)].

The predecessor's holomorphic charge is 4D W. The new two-sided regular charge is at most 4A_εL(Y)W. As L(Y)≥1, their sum is at most 4(D+A_ε)L(Y)W. The new D is therefore nonnegative. What remains is exactly

    cJ_T((Q,2Q]) ≤ K Σ_(l<6)[P_l + Y^ε(B_l+M)M]
       +4[Σ_(d∈V)|high_out(d)|+Σ_(q∈U)|high_in(q)|
           +(D+A_ε)L(Y)W].

P_l is the predecessor's true common-prefix maximum after summing all native exceptional slots and all levels in its dyad. The K and c are unchanged by this payment. In particular L(Y) multiplies only the additive bill and never P_l. The six Y^ε(B_l+M)M terms retain the already-paid lower-order Mellin baseline, including both signs, the density integral and the actual Abel/prefix cost. The source neither deletes a regular contribution nor leaves an unmentioned holomorphic or lower-order term.

The genuine high complementary norms remain on both sides. They are norms of the summed complex high slots, with no sign assumed. This theorem alone does not identify its retained parent energy with the entire exceptional energy. All constants precede Y,Q,ω,j,a,b; only T and ε and the already fixed cutoff/dependency constants can enter them. Empty rows, sub-unit dyads, and j=0 are allowed. The two existential tuples in `initial` and `recurrence` need not be numerically identical; common constants, if wanted, can be chosen by minima/maxima before the moving parameters.

## Six windows and all four mother scales

The literal input support [Q/2,5Q/2] is contained in (Q/4,4Q], including both support endpoints. The returned support condition is 16C/25≤d≤32C, hence V⊆(C/2,32C]. The lower endpoint is strict because 16/25>1/2; the upper endpoint is included. The direct sums are Σ_l B_l=63C/2 and Σ_v A_v=15Q/4. Thus this entry's ordinary-plus-holomorphic bill is

    4(D+A_ε)L(Y)M(63C/2+15Q/4+10M^(1+ε)).

For the printed mother (Q,16Q], apply the same inequality at Q_b=2^bQ, b=0,1,2,3. Each application retains Q_b inside its actual reflected test. Its radius is C_b=C/2^b, shoulders are A_bv=2^(b+v−2)Q, and outputs are B_bl=2^(l−b−1)C. Therefore the 24 returned dyads cover within (C/16,32C], while the sixteen shoulder dyads lie within (Q/4,32Q]. Equal child endpoints arising from distinct b still carry distinct physical tests; one may charge their nonnegative bounds with multiplicity, not identify their complex traces.

Summing the exact bills over b gives

    4(D+A_ε)L(Y)M(945C/16+225Q/4+40M^(1+ε)).

There are 24 prefix terms, each with coefficient K/c after division; bounding every child by a common expression incurs at most 24K/c. No new dependence on Q,Y,j or ω is hidden here. At a shared damped Y=Q²/(D_damp M), the 24 child lower endpoints run from πQ/(16D_damp) to 16πQ/D_damp. The shoulder Q/4 is not a new mother and must not be substituted into the damping formula. These computations verify the existing finite-cover interpretation; no new 24-return Lean declaration is claimed.

## Decision boundaries

The original missing import is a formal-expression/dependency omission, repaired by the already-existing R2. The four-mother extension is an explicitly supplied elementary finite deduction. Uniform high-order removal and critical transport are genuinely separate mathematical obligations. A later proof that positive infinity coefficients vanish for τ>3/4 can remove the actual high slots at T=3/4; it cannot by itself supply the τ>1/2 coefficient provider used by the critical induction.

This review permits the R2 paid initial and retained recurrence only at mathematical source level. It grants no unconditional full Pascadi J, global Selberg bound, 7/32, P3.5, kernel validation, formal credit or leaf closure. Verification consisted of exact raw hashes, direct source algebra and manuscript comparison. No Lean, Lake, LSP, helper, fixture, proof execution, Git mutation, download, or CI was run.
