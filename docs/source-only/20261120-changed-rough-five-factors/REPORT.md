# P1.4 — actual changed rough carrier: rank parity and five distinct prime factors

**Status: SOURCE_ONLY / UNEVALUATED / UNCOMPILED. Parent node P1.4: YELLOW.**

## Verified recovery and source

- Verified previous branch `chatgpt/p1-full87-changed-rough-first-divergence-20261120-1310` at HEAD `9e4b4d009ae04c6d02ea0445b285020154faa1d0`, read REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF and its complete source `P1Full87ChangedRoughCausalWitness.lean` (blob `c5928515405cb2eb5bd5c30e8ae511bc69b191fe`).
- Reviewed existing `P1HistoricalBoundaryPolicyDifferenceSupport`, `P1SignedExitPartition`, `FirstExitGenericModuli`, `FirstExitDepthSplice`, and `P1Full87TrueDRoughSymmDiffDensity`. Checked `ChenInitialPrimeSource` supplier without changing it.
- New source `P1Full87ChangedRoughFiveFactors.lean` (167 nonempty/final-line-sensitive lines; fetched line count 168 including terminal newline), Git blob `1b008789a439855ceb7c89707ca8a44b138dddb1`, source commit `b7b43095c028797003c7c8c17af0d8c5df39265f`, in isolated branch `chatgpt/p1-full87-changed-rough-five-factors-20261120-1410` based directly on `9e4b4d0`.

## New in-paper candidate (exact same actual policies)

Let `R := CompleteSixthDispatch.policy` and `S := LicensedSixthPolicy.policy` at the unchanged frozen parameters. Let `b` be a rough modulus belonging to the symmetric difference of the actual `fixedRoughSupport (R false)` and `fixedRoughSupport (S false)`.

The predecessor produces a genuine common-first-exit state `s` with `4 < s.selectedPrefix.length`, selected history `s.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z`, and every selected prime in `b.primeFactors`.

This round uses the **actual nodup prime universe** to get `s.selectedPrefix.Nodup`, and the actual factor-history inclusion to derive

```text
5 <= s.selectedPrefix.length
   = s.selectedPrefix.toFinset.card
  <= b.primeFactors.card.
```

Thus every changed actual rough modulus has **at least five distinct prime factors**. This does not infer ownership from factor inclusion or quotient away original occurrence multiplicities.

Separately, the existing `p1_mem_exitStates_sign_mass` invariant on the **same** actual common-admission recursion gives `s.positive = evenListLength s.selectedPrefix`; the predecessor's `s.positive = false` proves the selected first disagreement has **odd** rank (5, 7, 9, ...). This assertion concerns the selected history, not the number of all factors of `b`, which may be greater.

Finally the earlier exact true-d physical-density identity on `S \\ R` and `R \\ S` is restricted, without changing either sign or the original beta-plus/minus factor, to those `b` with `5 <= b.primeFactors.card`. It is a finite algebraic support reduction, **not** an asymptotic estimate, an 87-cell action match, or a PP license.

## Actual checks and limits

- GitHub branch and source commit were written; source file was read back by blob SHA `1b008789a439855ceb7c89707ca8a44b138dddb1`.
- Current environment: `git --version` succeeded; `lean --version`, `lake --version`, `elan --version` all exited **127**, command not found. Memory cgroup = **4294967296 bytes**. No fixed compiler or staged source-only import closure is present.
- Static banned-escape scan on the generated source found no `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` words. This is **not** elaboration or kernel evidence; the three new public theorems remain **UNEVALUATED**.
- No CI, Codex, main/master write, force push, new analytic axiom, resource increase, kernel replay, transitive-axiom audit or independent review.
- Manuscript pin `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` was re-read, as were `lean-toolchain`, `lake-manifest.json` and `lakefile.toml`. Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`, c=`49044063/25000000`, K=`8452171/1250000` unchanged.

## Next non-synonymous obligation

First type-check the precise source-only imports in the pinned Lean/Lake environment and repair real elaboration failures. Then use the now-identified odd **first** difference rank with the original rank-5/7/9 `rosserAncestor` mapping and the full 87-cell raw/licensed action tables. Do not count all changed moduli as rank-eight owned. The filtered five-prime-factor density still needs correct ordinary residual-integral identification and quantitative `H_N` payment, with outside net, producer invoice, stopped events, two independent reserves and PP licensing kept separate.
