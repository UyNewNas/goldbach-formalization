# P1.4 exact external-input boundary — rank-nine inherited-square split

Manuscript: `UyNewNas/chen-imbalanced-semiprimes`
`9731290e8f53cffda44129906cde6a965eaa869b`;
`paper/source/manuscript-body.tex` Git blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`,
§4 lines 355–490, especially exit identity and literal densities.

Fixed toolchain (unchanged): Lean `leanprover/lean4:v4.33.0-rc1`;
mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`;
native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.
Constants c=49044063/25000000, K=8452171/1250000.

## Internal finite inputs: exact source and application
- `FirstExitTree.lean`: actual select/skip recursion; used for literal
  HEAD first-rejection absence of a select subtree.
- `OrdinaryRosserFirstExitPolicy.lean`: upper odd retained Boolean is
  full product cutoff AND `UpperAdmissibleSet`.
- `P4AOriginalFull87Post8GuardExtraction.lean`: already established
  exact rejected-iff product-or-square lemma.
- `P4AOriginalFull87ActualEighthCarrier.lean`: actual owned original87
  state, eight-prime history and strict cross-order / Nodup.
- New proof packet: complete old/new square filters at rank nine and
  actual frozen-level adaptation; no analytic input is used.
These previous source-only imports have NOT been compiled in this packet.

## External analytic input registry — unchanged, UNVERIFIED, NOT INVOKED
1. Ordinary Rosser exit density (manuscript §4 and Appendix upper):
   claimed `V_N⁺(R,y)/V_N(y) = F(log R/log y)+o(1)` for s>1;
   `V_N⁻/V_N=f(s)+o(1)` for s≥2. Intended after real same-source
   first-exit identification and fixed compact positive parameter bounds.
   Exact independent source edition, uniformity, target-prime deletion and
   hypotheses remain UNVERIFIED.
2. PNT/Mertens (manuscript eq:current-mertens):
   `V_N(N^u)=2exp(-gamma) C_N/(u log N) (1+o(1))`, fixed u>0 and
   even target N→∞; uniformity and normalization UNVERIFIED.
3. Prime-progression discrepancy (manuscript eq:current-PP):
   claimed `rho_N` signed-family `O_{A,W}(N/(log N)^A)`;
   family, source edition, parameter order and sharp domain
   qualification UNVERIFIED.

No external input is proved here. Rank-nine historical-square control,
same-source error propagation, residual integral, reserves and
same-rho assembly are explicitly INTERNAL obligations. No new axiom,
result-bearing assumption fields, sieve weights or mask are introduced.
