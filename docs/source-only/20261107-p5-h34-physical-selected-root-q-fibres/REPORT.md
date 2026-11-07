# P5.6 → h34 — actual per-root Q on the original selected U3/U4 count fibres

Date: 2026-11-07 UTC.
Repository: UyNewNas/goldbach-formalization.
Branch: chatgpt/p5-h34-request-admission-20261105.
Verified predecessor: b61d60ed58af3be3a4324ea4cb68e96e8f5c6b43.
Mathematical source commit: 38cc36c9061736f4663180b47d684b809f8d2b01.
Source blob: 613571f1154e675ddbdd8880c0102269576e90dd.
Fixed manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766;
paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79.

**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**

## Concrete increment

The predecessor \`OriginalSelectedRootFibres\` separated original U3/U4
selected-count cutoff and Rosser-policy failures *at one supplied constant Q*.
That was insufficient for the genuine frozen-root source:
\`rootQ N precision k tau p\` varies with the original prime \`p\`, and may
also differ between overlapping U3/U4 bands. Reusing a single Q for all
receivers would be an unjustified consumer substitution.

New candidate file:
\`Part5OriginalH430PhysicalSelectedRootQFibres.lean\`
(281 lines; 13 public candidate theorems, two private helper proofs,
six definitions; one source-only new file).

1. \`originalPhysicalQ\` reads EXACTLY \`rootQ N precision .U3/.U4 tau p\`
   from each genuine tagged receiver, independent of its quotient q.
   \`physical_Q_U3_history\` and \`physical_Q_U4_history\` connect this
   physical Q to the already implemented original 430-request history's
   unchanged total-Q dictionary, for each root separately. They do NOT
   assert a common Q between different roots.
2. \`original_physical_licence_iff\` consumes the previously proved genuine
   selected-root prime/coprime fact, retaining both real remaining licence
   tests: strict \`p < z0\` and original singleton ordinary-Rosser retention
   at THIS root's Q. The lower/upper sign and physical \`z0\` are explicit
   parameters awaiting final manuscript-consumer binding.
3. \`physical_root_blocked_split\` proves an exact source-level partition
   into cutoff failure and the actual varying-Q policy failure.
   \`physical_policy_actual_fibres/card/signed\` rewrite the policy failures
   as entire original (tag,p,q) quotient fibres. They preserve U3/U4
   overlap and arbitrary signed q/tag-dependent weights; none of the
   distinct original q occurrences is mapped to one history mark.
4. \`actual_physical_selected_count_three_terms\` gives a candidate
   arithmetic identity for the GENUINE \`currentChenUpsilon3 +
   currentChenUpsilon4\`, split into physically root-accepted receipts and
   the TWO UNPAID root-failure counts. The signed counterpart retains
   the original per-receiver weights with no sign assumption.
   \`physical_selected_all_cutoff_if_small\` keeps the conditional
   \`z0 <= N^a\` obstruction valid at the real variable Q; this condition
   is NOT asserted for the manuscript's unspecified presieve exponent.

These are source-level root-gate count identities only. In particular,
\`physicalRootAccepted\` is NOT identified with a full/selected/inherited
historical count owner; its cardinality is NOT the root-history mark-one
mass, and nothing has been paid by a signed Euler correction. This packet
does not repeat the prior constant-Q partition as if Q were physical.

## Verification and ownership

- Added only this task's independent source-only directory. No production
  module, P1.4, P3.6, other task-owned file, manuscript, dependency, CI
  configuration or toolchain was changed. No merge, force-push or CI run.
- Remote commit and source blob were read back; comparison shows only
  the new Lean source, 281 additions and zero deletions before this report.
- Static scans: 15 candidate proof bodies (13 public and two private),
  no forbidden proof placeholders/escape tokens, balanced brackets and
  nested comments. These DO NOT establish Lean parsing or type checking.
- Lean/Lake executable unavailable here. Not compiled, not elaborated,
  no kernel replay, no transitive axiom audit, no independent review.
  Inherited finite/numerical430 certificates remain UNEVALUATED.
  Zero engineering-green or formal-closure credit.

## Remaining genuinely manuscript-internal obligations

1. Identify the actual historical root \`z0\`, parity/lower flag and
   its stage, and instantiate the physically varying root Q and alpha at
   the correct full/selected/inherited owner. The pinned manuscript
   leaves projection-presieve omega symbolic at the cited location;
   do not assume \`z0 <= N^a\` or its negation.
2. Bind true original U3/U4 q/tag multiplicity and outer root count weight
   to real history occurrences and full/selected/inherited masks. Account
   for cutoff, policy, carrier-outside and policy-pass receivers and
   multiple q/tag receipts per signed first-excluded event without double pay.
3. Resolve sign/orientation of genuine \`historicalExitValue\` versus
   original selected-count mass and establish a DIRECTIONAL payment inequality,
   not merely an exact residual decomposition.
4. Connect actual all-action CLOSED-CELL induction and original base,
   switched, seed, feedback floor/integral and Theta/outer counts; discharge
   manuscript-local PP/same-rho, native-history mass and one nested
   430+11 causal refinement with the original constants.
5. Stage and compile source, kernel replay, transitive axioms and complete
   independent finite guard checks under the fixed toolchain.

## Next bounded action

Compare physicalRootAccepted and the two genuinely unpaid failing families
against the fixed manuscript's actual full/selected/inherited *history owner*
and the first-excluded signed correction with physical root Q. Identify
which accepted q receipts get a true repeated owner and which fail; do not
create another constant-Q surrogate or infer historical count equality from
this root-filter identity.

**完整 h34 稿内证明仍未闭合。**
