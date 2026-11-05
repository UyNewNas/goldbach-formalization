# P1.4 original87 post-eight odd-exit continuation checkpoint — 2026-11-05

- **Parent:** \`9607e158c55b09aa709b7830f7b1cc69d5ad1ab4\`, verified as HEAD of \`chatgpt/p1-full87-fixed-rank-exit-20261105\` at branch creation.
- **Continuation:** \`chatgpt/p1-full87-post8-suffix-20261105\`, **new independent branch**, no rewrite of the parent or master.
- **Proof source:** \`P4AOriginalFull87Post8SuffixExit.lean\` (install target \`ImbalancedChen/P4AOriginalFull87Post8SuffixExit.lean\`).
- **Initial proof commit:** \`acb1dfc5770bda2604714f0c63f552ead67832c7\`; **Git blob:** \`6d05633404346c7e77fba49eb8fae9cffba2b044\`.
- **Status:** SOURCE_ONLY / UNCOMPILED / UNEVALUATED / no kernel, axiom, numerical-certificate, CI or independent-review credit.

## This round's mathematical correction

The preceding fixed-rank proof required every earlier odd full-square test at the *same* frozen ordinary level beta. That cannot be inferred from the REAL rank-eight original87 ancestor because its first eight decisions were made at historical (possibly different) levels. Neither a cap increase nor inclusion of an eighth prefix transports those tests to the final level.

A frozen ordinary continuation starts at the rank-eight selected prefix, so **restart the potential at the eighth prefix mass**:
S8 = sum(t1,...,t8), u_i = t_(9+i) (one-based).
For the first failed later odd test at rank j=9+2m, the only previous tests needed are
S8 + sum_(i<2k)u_i + 3u_(2k) < beta for k<m, plus u_(2k+1)<=u_(2k).
Failure means beta <= S8 + sum_(i<2m)u_i + 3u_(2m).
The proved finite potential now yields:
**beta - S8 <= 3^(m+1) u_(2m).**
No pre-eighth full-square test at beta occurs in this statement. This specifically corrects the inherited-level gap; it does not alter historical admissions.

The existing \`actual_eighth_kernel_transport\`, on the EXACT realized original87 owned trimmed eighth source, gives
cutoff < t8 < actualParent-S8, and actualParent <= comparison < finiteCap.
Hence **both** actual frozen continuation levels have beta-S8 > cutoff,
where cutoff=53/13824. As 261*cutoff=1537/1536>1, an exact prime reconstruction p=N^u_(2m) and the *post-eight* ordinary guards imply N<p^(261*3^(m+1)).
The existing \`fixed_odd_exit_deletion_sandwich\` is reused with the conservative count k=261*3^(m+1) (power k+1) on the same target-factor multiplier.

The core arithmetic is NOT another pair of unrelated sieve bounds. It uses the identical owned eighth history, actualParent, rounded finiteCap and actual target-prime correction. No source state, owner, signed beta or occurrence list was redefined.

## Scope of the new Lean candidates

1. \`post8_first_odd_exit_log_lower\`: restarted post-eight potential, no inherited test assumption.
2. \`post8_integer_power_gap\`: exact integer-power reduction from beta-S8.
3. \`owned87_old_and_new_residual_floor\`: actual source \`ht\` + \`RealizedHistory\` + old kernel transport imply both genuine residual floors.
4. \`post8_uniform_integer_factor\`: fixed integer 261*3^(m+1), certified by rational cutoff.
5. \`owned87_post8_ordinary_deletion\`: the same original87 source, either existing actual frozen level, and the already defined target-deletion factor. All post-eight guards and the actual terminal prime reconstruction remain explicit premises; they are not hidden in a new structure.

## Checks and boundary

- 210-line candidate; five theorem bodies. GitHub readback verified correct file blob and commit.
- Local exact rational diagnostics tested 10,000 sorted post-eight first exits with varied positive residual and checked beta-S8 <= 3^(m+1)u_last. This is finite model evidence, **not** universal proof validation.
- Static declaration inventory, forbidden proof-escape scan, bracket-balance and exact 261*53/13824 calculation inspected. These are **not** Lean parser, elaborator or kernel checks.
- No Lean/Lake, kernel replay, transitive-axiom inspection, raw saved87 archive replay, CI dispatch, Codex invocation or user-computer connection.
- The manuscript remains \`chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\` at \`paper/source/manuscript-body.tex\`, blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`. Pins: Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, subfish native 09b97db5764ade1246bfb77206baa1b124760958.

## Unpaid manuscript-internal obligations / exact next move

**Next:** inspect the literal \`ordinaryParityRosserPolicy false (N^beta)\` descendant selection and \`firstExitRetainedLeaves\` definitions on the same full-q original87 state. Prove for the selected post-eight list that every *retained* previous odd full-square guard equals the finite post-eight \`hprior\`, in the same processing order and frozen beta, and that the first discarded odd branch provides \`hexit\`. Then derive \`hpair\` from actual sorted rough carrier and prime-log reconstruction from \`primeHistoryLogCoordinates\`. Do **not** reconstruct or require earlier ranks 1,3,5,7 at the new beta. If the ordinary policy includes selected-complement squares, retain their independent guards and check whether the full-square guard is the one relevant for this exit.

Further gaps: fixed-source ordinary positive exit-series to residual integral and uniformity; primitive/centre and modulus-factor error smallness; sixth filtering, raw/finite/filtered signed gain; entire saved87 numerical source/archive and two separate compiler/density reserve payments; full same-rho composition and fixed-dependency Lean staging/verification. The changed parent itself and source membership cannot be replaced by a synthetic selector.

\`INPUT_BOUNDARY.md\` records external inputs **only**. No new axiom, unproved-analytic assumption, altered c or K.
