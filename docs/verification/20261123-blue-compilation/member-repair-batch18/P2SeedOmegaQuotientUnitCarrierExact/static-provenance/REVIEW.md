# Exact unit carrier: pinned Nat.div_self API

Status: **UNCOMPILED**. No Lean/Lake/compiler/kernel/type/axiom probe was run;
no live Member/main/P6/native/frozen source, old data, or build output changed.

Module: `ImbalancedChen.P2SeedOmegaQuotientUnitCarrierExact`.
Original SHA256: `7d13e8c49bca022d8833e56df7d70842b6a370f4021cbabe9ec08b229b1d645a`.
Candidate SHA256: `a24e203e128b415e04bf2005742c5c0e37e2fb5d58b1c9c7d031796c3b87af99`.
Full original/candidate sources, patch, and exact raw failure slice are included.

Only two proof applications change. Pinned Lean
`Init/Data/Nat/Div/Basic.lean:443` declares
`Nat.div_self (H : 0 < n) : n / n = 1`.
The original calls incorrectly pass `Nat.ne_of_gt` of the existing positivity
proof. The candidate passes that same positivity proof directly:

* `Nat.div_self hprod` in `quotientUnit_eq_originalUnit`;
* `Nat.div_self (specified_product_pos hd hpre hp hq)` in
  `quotientUnit_disjoint_collision`.

The five complete headers, four theorem statements, sole definition,
imports, hypotheses, quantifiers, every numeric token, and original EOL counts
remain byte-exact. No header exception or new mathematical premise is needed.
The selected original Git blob is verified against the archived baseline;
main has that same baseline, also at `b2c20e78`, and P6 has no canonical file.
Bounded exact-path source history was inspected first; no published fixed
version was found. No global history or legacy-family scan was performed.

The unit carrier remains literally the original quotient carrier filtered by
`N-ell=d*l.prod`. It keeps the original mask `d*N`, complete specified product,
next-to-last prime cutoff, and actual natural receiver `ell`. Positivity of
that same product was already derived from the unchanged `hd,hpre,hp,hq`.
The original receiver equality, singleton-or-empty prime test, retained
predicates, and disjointness from the collision carrier are unchanged. The
patch does not enlarge a carrier, discard an endpoint/unit atom, infer a
negligibility estimate, or substitute a sorted merge.

The imported existing `HighUnitPrimeOutput.unit_mem_iff` and `unit_card` were
checked at native09b: they concern the same list `pre++[p,q]`, same ordered
last two primes (`p≤q`, including equality), same receiver and exact unit
output. No downstream Wu endpoint theorem is used as a shortcut.

Nov6 `sieve-appendix.tex:778–792` retains the quotient-one surface separately
from the ordinary Buchstab integral; this exact finite carrier equality
preserves the corresponding unit contribution before averaging. It adds no
asymptotic or weighted-sum assertion.

`STATIC_RECEIPT.json` binds pre/post source SHA, complete headers, current API
source SHA, pinned versions and verbatim original failure byte range. The
sole source owner can adopt this two-call API correction and perform normal,
kernel and all-public validation under the existing guard.
