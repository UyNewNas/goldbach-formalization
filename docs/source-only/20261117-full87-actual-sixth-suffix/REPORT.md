# P1.4 — source-derived original sixth suffix for every genuine fifth/sixth one-sided occurrence

Baseline **c1cdaea92e318fbbb21b04885dd4ee4a1f221dba**, branch `chatgpt/p1-full87-sixth-positive-carrier-cut-20261117`.
Current independent branch: `chatgpt/p1-full87-actual-sixth-suffix-20261117`.
Candidate: `P4AOriginalFull87ActualSixthSuffix.lean`.
Initial new-source commit: **040d171d738ffdfbd76f3fdf4b2a037bf81d877b**.
New Lean source blob (remote readback): **b00e3aeacc46c2b8b97ae6da6d4996636a264b91**.

## Exact candidate progress

Last packet proved that, for a fifth prefix `pre`, its unchanged sixth-positive high-q continuation is zero whenever (i) its original sixth suffix lies in `roughPrimeUniverse N cap w z`, (ii) `L>=0`, and (iii) `(L * pre.prod) * z <= X`. Its missing *source membership* premise is addressed in this packet; the cutoff condition itself is not assumed automatically.

Read the original producer definitions in the actual prior packets:
- `20261108-full87-first-fifth-stopped-events/P4AOriginalFull87FirstFifthStoppedEvents.lean`
- `20261112-full87-sixth-both-zero-invoice/P4AOriginalFull87SixthBothInvoice.lean`
- `20261108-full87-rank4-stopped-localization/P4AOriginalFull87RankFourStoppedLocalization.lean`
- core `ImbalancedChen/FirstExitFrontierInvariants.lean`, `ImbalancedChen/FirstExitDepthSplice.lean`, and `ImbalancedChen/RoughPrimeUniverse.lean`.

In the new source, two finite inductions prove that the incoming order is unchanged:
1. Every actual `firstFifthEvents` occurrence stores a suffix sublist of its incoming carrier.
2. Every occurrence in the unmodified `fifthSixthWithoutBoth` generator, whether `.fifthExclusive` or `.sixthFromBoth`, has an `eventSixthSuffix` sublist of its incoming fourth-state `remaining`. The sixth-BOTH filter only affects membership of an inner event; it never rewrites the suffix.

Then the existing core theorem `firstExitDepthFrontier_selected_remaining_sublist` takes the *same actual* `sharedRankFour` root into the original ordered `roughPrimeUniverse N cap w z`. Chaining those two original sublist proofs establishes `actual_event_suffix_mem_original_rough` for **every actual event occurrence**. As a direct application, `actual_fifth_exclusive_sixth_zero_of_level` instantiates the previous plus-beta cutoff for both RAW and LICENSED on the actual fifth-exclusive suffix (not an invented rough universe).

**Scope:** This discharges the previously free *suffix membership* hypothesis for true fifth-exclusive events. It does not prove `(L * b5) * z <= X` uniformly, does not cancel even-sixth high-q tails outside that range, does not treat the separate direct rank-six `sixthFromBoth` terminal as zero, and does not change the old signed or absolute invoices. It makes no assertion of saved87 numeric gains or a uniform physical rho level.

## Version and execution evidence

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`; re-read pinned blob **d529bea2ecfcc74d64fc1664ac770a3becaa7c79**. Fixed toolchain: Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. `c=49044063/25000000`, `K=8452171/1250000` unchanged.

Actual local checks:
- `lean --version`: exit **127**, `bash: lean: command not found`.
- `lake --version`: exit **127**, `bash: lake: command not found`.
- `elan --version`: exit **127**, `bash: elan: command not found`.
- Searched working runtime's usual .lake/packages paths: no pinned project closure. Memory cgroup limit 4 GiB; no extra resources or external runner were used.
- GitHub source file remotely read back at exact blob above. No forbidden proof-escape tokens detected in the candidate source.

**Status: SOURCE_ONLY / UNEVALUATED / UNCOMPILED.** No Lean elaboration or local Lake typecheck, kernel replay, transitive axiom audit, actual 87-domain archived replay or independent review. Proof-script syntax/type correctness remains unconfirmed. These are mathematical source candidates only. No CI dispatch, main/master edits, merge, force-push, Codex, user machine or external analytic proof.

## Remaining manuscript-local obligations

1. Determine from frozen parameter formulas whether the *actual* fifth-exclusive history satisfies `L * selectedAfter.prod * z <= X` in the intended full range. If not, retain the original large-sixth-prime tail and prove an **on-the-same-rho_N** quantitative high-q estimate. Do not convert a geometric cap into a signed arithmetic saving.
2. Independently handle the direct sixth-from-both positive terminal; prove the actual RAW rank-eight and all early/physical full `a*b` support, with the same fixed epsilon, density and both reserves.
3. Adapt registered external signed sharp-prime PP only at its original exact conditions: common W, \(X_W^{(q)}\), endpoints, singleton, modulus-/centre-prime corrections, same signed physical rho. The external proof is NOT implemented.
4. Ordinary residual integral, actualParent weighted loss, original saved87 archive numerical certification, changed/tagged/rank9, compiler/density reserves and final same-rho connection.
5. Pin-correct source import adaptation, actual Lean/Lake elaboration, kernel replay, axiom audit, independent validation. P1.4 remains YELLOW.
