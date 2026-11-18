# P1.4 — actual stopped upper-half prime fibre: centre mask discharged from original support

## Recovery / immutable inputs
- Verified immediate predecessor: `aa3827eba073f516fee3d2241585a51262834f39`, branch `chatgpt/p1-full87-stopped-upper-half-prime-fibre-20261118-1910`. Read its complete candidate Lean source, REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and remote branch ref.
- Independent task branch: `chatgpt/p1-full87-stopped-upper-half-coprime-unmask-20261118-2010`; created at exactly that predecessor. No changes to main, other task branches, or the existing proof packets.
- New proof: `docs/source-only/20261118-stopped-upper-half-coprime-unmask/P4AOriginalFull87StoppedUpperHalfCoprimeUnmask.lean`.
- New source first committed as `abd5437b4ff58aaf66f9b50c54e816b25f84f40e`; corrected original full-modulus statement to retain generic strict X filter in `e44f403c7397e9fef7a7c31dd94e711efd932576`.
- Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Re-read PP premise at manuscript lines 245–315.
- Reused `ImbalancedChen/ActualSmallRosser.lean`: `actualSmallRosserSupport_coprime_target`; `ImbalancedChen/RoughPrimeUniverse.lean`: actual membership, prime and non-divisibility. Reused the actual stopped sixth source and joined-history lemma in `P4AOriginalFull87OrderedSixthSuffix`, plus previous `original_upper_half_prime_rosser_reindex`.
- Checked applicable AGENTS.md at root, docs, docs/source-only and previous proof packet: absent; new directory initially absent.

## Actual mathematical progress (finite exact, not an asymptotic)
For an **actual** fifthExclusive event generated from `receiverTest N` on the original `sharedRankFour` state, the selected fifth history and each literal sixth occurrence are members of `roughPrimeUniverse N cap w z`. Thus all six primes are coprime to N, without substituting the upper endpoint z for the lower endpoint w. For every original large-fifth Rosser index
`a ∈ largeFifthRosserIndices N cap w X pre`,
`a ∈ actualSmallRosserSupport N cap w`, so `Coprime a N` from the existing actual small Rosser support theorem.

Consequently, the **complete** `q=a*(p::pre).prod` is coprime to N. If the exact original prime fibre admits `q=N-P`, then `P≤N` and `Coprime (N-P) N` imply `Coprime P N` by the finite subtraction identity. For P prime, the exclusion condition `P∤N` is automatic.

The new candidate `original_upper_half_unmasked_prime_prefix` replaces precisely `chenAdditivePrimeCarrier N` by `chenPrimePrefix N` in the prior upper-half prime-fibre finite sum, **not** by an unverified asymptotic prime mass. The original quotient filter `a=(N-P)/(p::pre).prod`, exact multiplication `a*(p::pre).prod=N-P`, original PLUS beta, and strict `2P<N`, `X<N-P` all stay. `actual_common_sixth_unmasked_prime_prefix` proves the same change on the real ordered sixth occurrence list, retaining fifth signed mass and duplicates; its membership proof uses the original joined-history sublist.

This removes a redundant **centre-divisor mask** only on these *admitted* actual full moduli. It does not show that any prime sum is small, that an arbitrary modulus is coprime, or that the frozen PP admits the residual quotient/support arithmetic filter. The fixed same-rho PP is not invoked.

## Checks and validation
- Host: `command -v lean`, `command -v lake`, `command -v elan` absent; `git` present. No matching pinned Lake closure is available; no Lean type check, no kernel replay, no transitive axiom check. Status **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**.
- Independent reproducible Python finite arithmetic diagnostic (seed 20261118): 40,000 randomly generated N, six distinct N-coprime small primes and a with gcd(a,N)=1; 4,388 admitted cases q=a*b≤N, of which 1,261 had prime P=N-q; **0 coprimality failures**. This checks only the elementary arithmetic, not the actual Lean producer or candidate proof elaboration.
- Earlier candidate branch and all frozen pins unchanged. No new CI, Codex, dependency upgrade, main/master edit, or resource increase.
- Exact Git blob and final remote HEAD are to be read from REGISTRY and the branch ref after documentation commits.

## Still open
1. Correctly stage source-only imports and compile at frozen Lean 4 v4.33.0-rc1 / mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 / native 09b97db5764ade1246bfb77206baa1b124760958. Fix any actual elaboration errors before claiming COMPILED.
2. Show an admissible smooth no-extra-filter manuscript PP weight for actual signed primitive full-q discrepancy, or prove a separately justified bound. **Removing P∤N does not remove exact-quotient Rosser arithmetic support.** Reconcile same signed physical rho, physical level, original H_N and all occurrence multiplicities.
3. Source-map actual upper producer w (lower) and z (upper) independently; continue lower-half primitive discrepancy, modulus-prime and centre-prime corrections without double payment.
4. Ordinary residual integral and complete87 actualParent/saved87 original certificates; unfiltered sixth BOTH, RAW eighth, rank9 changed/tagged; three physical invoices and separate compiler/density reserves.

**P1.4 parent YELLOW. No new certified H_N saving.**
