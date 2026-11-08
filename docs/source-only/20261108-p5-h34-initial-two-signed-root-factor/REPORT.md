# P5.6 → h34 — literal initial-two factors in the actual signed native depth-k mass

Date: 2026-11-08 UTC. Branch: `chatgpt/p5-h34-request-admission-20261105`.
Incoming remote HEAD: `8a311bda4e69fb8c616e0edcf36c9da645b607a1`.
Mathematical candidate source commit: `c5cbab0def342cce9067a491bc1c4057cfe62f22`.
Source blob: `f42071b9d490afd477906779de1ed933530b891b`.
Status: **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
Neither manuscript nor toolchain changed.

## Recovery and dependency

Read the initial 20261105 request-admission REPORT/REGISTRY/EXTERNAL_INPUTS
and the actual newest previous packet
`20261108-p5-h34-actual-initial-two-extension-mass`. The latter
already transports the real arbitrary-depth initial-two prime group
to the admitted tuples, and explicitly leaves the owner unmatched.

The fixed manuscript, lines 790–905, places H430 at the upper U3/U4
root cost, and assigns full/selected squares, preceding finite
generations, real alpha and one nested 430+11 refinement.
The manuscript does not authorize identifying those original
arithmetic q/tag roots with any ordinary-Rosser native history
position. This packet makes no such identification.

## New local mathematical source increment

New source:
`Part5OriginalH430ActualInitialTwoSignedRootFactor.lean`
(177 lines, five public theorem bodies, one private theorem,
three definitions).

1. `actualInitialTwoRootFactor` uses exactly
   `(p-1)^{-1}(ell-1)^{-1}`, the two native prime factors,
   explicitly NOT the original U3/U4 count root weight.
2. `actualFirstTwoSuffixWeight` takes `selectedPrefix.reverse.drop 2`
   rather than `selectedPrefix.drop 2`. This respects the true
   reverse-stored frontier and keeps every later selected prime.
3. `actual_depth_first_two_mass_factor_of_mem` derives
   `state.mass = rootFactor * suffixWeight` for a genuinely admitted
   state with first two original primes `[p,ell]`. It reuses the
   existing exact native product theorem; no extra history or owner
   assumption is introduced.
4. `actual_depth_first_two_signed_root_factor` factors the same
   literal two-prime native contribution from ALL physical depth-k
   list occurrences even when the full-prefix test F is SIGNED.
   No sign cancellation is used to establish an inequality; this is
   an equality. There is no claim that the full-prefix F is the
   manuscript full/selected/inherited consumer.
5. `actual_depth_first_two_native_root_factor` and
   `actual_depth_first_two_admitted_tuple_root_factor` connect that
   identity back to the EXISTING exact native first-two mass and the
   original admitted finite tuple enumeration. Different later
   extensions remain distinct, and the same arithmetic q/tag is
   not silently paid twice.

This is the **native two-factor vs continuation mass split** only.
It neither identifies the genuine H430 upper-count owner nor pays
the historical signed Euler suffix or the extra U3/U4 tag.

## Still manuscript-INTERNAL and OPEN

- Exact H430 U3/U4 full/selected/inherited stage and owner, physical
  z0, native depth, root weight and literal filter; identify the
  genuinely used history before using this native factorization.
- Relate original q/tag quotient receivers (including cross-q same
  slot collisions) and signed count weights to that owner. Retain
  unmatched receipt mass and every rejected lane explicitly.
- Request-level all-action CLOSED-CELL count induction, actual
  Buchstab/retention consumption, original base/switched/seed/floor.
- Correct feedback rounding and integral–Theta–count transfer,
  manuscript-local PP/same-rho and native proper/equality/inherit mass.
- One common 430+11 nested causal refinement, not separate
  approximations, retaining c/K, norm 7/2, row norm 12, real alpha
  and unchanged reserve order.
- Lean elaboration, compilation, kernel replay, transitive axiom
  audit and numerical430 finite certification.

## Validation

Source written and commit `c5cbab0def342cce9067a491bc1c4057cfe62f22` remotely read back; GitHub
comparison against `8a311bda4e69fb8c616e0edcf36c9da645b607a1` reported exactly one new Lean file,
177 added lines, zero deletions. Static forbidden-token and delimiter
balance checks passed before creating the source blob.
No Lean or Lake run, no CI dispatch, no kernel replay or transitive
axiom audit. All proofs are **CANDIDATES**, not green. The numerical430
finite assertions stay **UNEVALUATED**. No new external analytic
input or axiom, no P1.4/P3.6, old-file, manuscript or CI change.

**Next exact action:** follow the fixed manuscript H430 U3/U4
count-root consumer down to its literal full/selected/inherited owner
and physical z0/depth, then instantiate this factorization only at
that actual owner and separately account for q/tag weight and
rejection/first-excluded Euler payments. Do not turn rootFactor
into the actual arithmetic root weight by definition.

**完整h34稿内证明仍未闭合。**
