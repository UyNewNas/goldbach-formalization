# P3.6 — manuscript-internal primitive integrated Euler derivative budget

**SOURCE_ONLY / UNCOMPILED / KERNEL-UNVERIFIED; P3.6 remains YELLOW.**

Base: fb78cf705549dc978a526152d4d6f129f01e0e36
Branch: chatgpt/p3-internal-original-w-20261105
Paper pin: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b
Source: paper/source/modules/distribution-prime-product-completion-20261010.txt, §§1–2, 4 (F).

## Precise change from the previous source-only packet

The previous 79d5ad9 pointwise-norm theorem controlled the original
W*HB mixed derivatives using sup_x |partial_js W(x)| <= M. The immediately
previous fb78cf7 packet bound W_T to its **original labelled group products**.
Neither proved the integrated Euler derivative class permitted in the
manuscript's PP source.

This increment makes the following primitive class explicit for a fixed
q and M >= 0, with C = [-2,2]^d the *old* HB logarithmic chart cube:

  * WDerivCompatible W (the existing genuine coordinate derivative operator);
  * continuity of every ordinary mixed derivative of W;
  * integral_{x in C} |mixed_js W(x)| <= M, for ALL ordered lists
    js of length <= q.

The new class concerns only W and does not assume any derivative, Fourier,
energy, or discrepancy estimate of W*HB. It is meaningful for the exact
physical pullback pulledOriginalW W_T U group from fb78cf7. The actual
source-family verification of the class remains a separate obligation.

## Finite real-analysis proof

1. Reuse the true finite Leibniz expression
   mixed_is (W*H) = sum_{p in splits is} mixed_{p.1} W * mixed_{p.2} H.
   It is a LIST of precisely 2^q terms; the multiplicity of repeated
   differentiation directions is retained. Do not convert it to a finset.
2. Uniformly bound only the already constructed HB factor derivatives
   |mixed_js H(x)| <= Ch*(m+1)^q (for all |js| <= q).
3. Apply the pointwise triangle inequality, then integrate on the fixed
   cube. By continuity and compactness the finite sum is integrable;
   linearity gives at most (2^q)*Ch*M*(m+1)^q.
4. The old compact window forces each combined derivative to vanish on
   the open cube complement. Its **whole-space** L1 integral therefore
   equals the computed cube integral. No global L1 of uncut W is required.
5. Sum these actual integrals over the doubled-direction lists for all
   S subset Fin d. Since length(doubled S) <= 2d and m+1 >= 1,
   the result is

       D_(W*HB) <= C_(d,g,a) * M * (m+1)^(2d).

   Here D is the **actual** existing originalWD, not a new assumed
   bound variable.

With M <= A*(log N)^E and m+1 <= (log N)^B the polylog endpoint is

       D_(W*HB) <= C_(d,g,a) * A * (log N)^(E + B*(2d)).

This pays the integrated W degree E exactly once, with no pointwise
W derivative assumption. C is chosen after d,g,a,E,B but before N,
original W_T, dyadic bases, slot/group assignment, lane and m.

## Actual source linkage

The final terminal is
  ImbalancedChen.P3OriginalWIntegratedDerivative.exists_physicalW_integrated_polylog

Its W argument is the original labelled function
  W_T : (Fin g -> Real) -> Real
and the explicit source pullback is
  pulledOriginalW W_T U group.

The geometric class condition is imposed on this precise pullback,
without attaching any q-dependent arithmetic filter. The prior
physical-source equality and same-rho finite signed identities remain
unchanged; this packet reuses those identities instead of redefining
rho, the complete product, or the coprime mean.

## Remaining gaps (manuscript internal)

* Verify each actual original W_T family (and its scalar labels) meets
  the primitive integrated Euler budget uniformly in its genuine
  parameters and all permitted length blocks; merely naming W_T smooth
  does not provide a quantitative log-degree or its N-uniform constants.
* Prove the actual Fourier transform/inversion and tail calculation
  in (F) with the same 2*pi normalization; C-infinity by itself is
  insufficient. Pay tails AFTER the full signed modulus sum, including
  the separate complete-product=T case, and do not call a fiber-level
  relative error a requirement.
* Complete the whole-atom/causal admission, all genuine HB source terms,
  empty Gamma mother words, high-rank/enhanced classes and final same-rho
  PP assembly. Do not exchange fixed-m harmonic convergence for a rate
  uniform in m(N).

Classical distribution inputs remain in the inherited external register
and are NOT implemented, strengthened, or added as new Lean axioms.
No work on the excluded full87 nodes.

## Actual checks

* Read and pinned the fb78cf7 commit/branch and its physical W files;
  confirmed original signed/source correspondence and source-only status.
* Inspected fixed Mathlib e4c9178 source for integral_add and
  integral_const_mul, and reused existing project's mixed-Leibniz,
  compact support, integrability and L1 interfaces.
* The new 343-line Lean candidate has 9 named definitions/lemmas/theorems
  (including three private helpers), zero disallowed proof-escape tokens
  after comment stripping, and balanced (), [], {} by lexical check.
* The independent SymPy exact polynomial regression passed 90/90 cases
  over dimensions 1–2 and derivative order 0–4. It checks Leibniz
  multiplicity and a discrete absolute-sum majorant on a rational grid;
  it is NOT integration over a continuum, a test of smoothTransition,
  or a verification of Lean syntax/kernel correctness.
* No Lean/Lake compile, kernel replay, transitive axiom audit, CI,
  producer, Codex, PR, merge, dependency update or outside-file change.
  No green transition is asserted.

## Next exact action

First identify each actual W_T family's primitive integrated Euler
seminorm and uniformity (including the original class of signed scalar
labels). Then implement the Fourier factorized (1+xi_j^2)^-1 majorant,
normalization, and integrated tail as a separate manuscript-internal
packet. Keep the complete modulus sum and the b=T branch separate.
