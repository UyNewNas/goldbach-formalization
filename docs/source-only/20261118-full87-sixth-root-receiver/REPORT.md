# P1.4 — actual receiver: coprime-quotient full-q invoice (candidate)

Baseline: verified `88ea5d042c4daa7b0267536565fb031ff10ddbdd`, `chatgpt/p1-full87-receiver-harmonic-20261118`.
Independent current branch: `chatgpt/p1-full87-sixth-root-receiver-20261118`. Terminal source: `P4AOriginalFull87CoprimeQuotient.lean`. This is SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

## Genuine new manuscript-side proof obligation removed at SOURCE_ONLY level

The preceding actual-receiver bound used every integer quotient in `1..floor(N/d)`, forgetting source coprimality. For the *same actual prime receiver source* `chenPrimeReceiverSource N`, any `n` with `d | n` satisfies `0<n<=N` and `Coprime n N`. Since `d|n`, the quotient `k=n/d` divides `n`, so `Coprime k N`. The map `n -> n/d` is injective on the original divisibility fibre, with full physical d. Therefore the new local finite candidate theorem is

```
R_N(d) <= #{k : 1<=k<=floor(N/d) and Coprime k N}
       <= floor(N/d).
```

Both inequalities have candidate Lean proof bodies: the first is a genuine quotient-source injection; the second injects eligible k into `Finset.range (N/d)` via `k-1`. The d=0 fibre is handled separately using original zero deletion.

The new bound is sometimes strictly better: N=12,d=5 has actual receiver fibre 1, coprime quotient capacity 1, previous floor 2; N=120,d=11 gives receiver 2, quotient capacity 2, previous floor 10. It is **not** a merely renamed high-q support filter.

The actual original PLUS beta attached at `a*(p::selectedAfter).prod` is bounded by this quotient capacity. The common actual signed sixth kernel, same `sharedRankFour`, same `actualFifthSixthWithoutBoth` occurrences, exact fifth signs and masses, and absolute stopped invoice are bounded by an explicit `actualCoprimeQuotientBudget`; its candidate proof then replaces the old stopped bill in the **same** RAW-LICENSED physical inequality with the existing raw-outside, producer and licensed-outside bills charged once. The packet separately proves the new budget is <= the preceding harmonic budget, event by event and globally. No new `F` or generic tail-smallness field.

## Redundant approach rejected in this run

A preliminary source draft proved `p^6>N` forces every receiver term on that actual sixth suffix to vanish, using the true ordered fifth history. It was not accepted as numerical progress: since already `a*p*b5>=p^6>N` for a>=1, the **previous floor invoice itself is zero there** (a=0 is also zero). Its new source file was deleted from the branch before this packet was registered. No blue progress is attributed to root pruning; this explicit correction prevents repackaging a support filter as savings.

## Checks and limits

- Exact branch/head/source readback and hashes: record in REGISTRY.
- Executed `lean --version`, `lake --version`, `elan --version`: all exit **127**, command not found. No fixed dependency closure and source-only imports not staged. **No Lean elaboration, kernel replay, transitive axiom audit or independent review**; candidate proof terms may fail.
- Independently checked the finite receiver/cop quotient/floor inequalities by Python for N=1..300, d=0..N+12 inclusive: **49,050** actual fibre tests, **0** numerical counterexamples, **14,884** instances where quotient capacity is strictly below floor. This is not Lean or original saved87 replay.
- Original manuscript pin `9731290e8f53cffda44129906cde6a965eaa869b` / blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` reread at its finite two reserves and PP context; pins unchanged.
- Fixed Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`, c=`49044063/25000000`, K=`8452171/1250000` unchanged.
- No main/master change, merge, force push, CI, Codex, user machine or external theorem implementation.

This bound is **not** proved o(H_N), not a new numeric saving, and does not license any fixed theta<1 for full q. It only uses the actual receiver n coprime to N, not squarefree high-q cancellation. Neither of the two distinct reserves is spent.

## Next substantive step

Use literal retained fifth p/a/occurrence counts and the frozen beta support to estimate the **actual coprime quotient bill** relative to H_N and pay the unchanged three physical invoices. If no o(H_N) follows from the elementary capacity, identify the exact signed cancellation/PP/discrepancy input needed rather than introducing a free smallness premise. Independently address true full-q theta/smooth-singleton admissibility, the unfiltered sixth BOTH issue, raw eighth source, ordinary residual integral, actualParent, saved87 certificate, changed/tagged, rank9 and both separate reserves. First obtain the pinned Lean dependency closure and compile, repairing concrete errors.
