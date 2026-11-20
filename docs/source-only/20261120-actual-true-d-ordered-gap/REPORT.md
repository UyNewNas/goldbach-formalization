# P1.4 — actual RAW/LICENSED true-d coefficient and ordered stopped gap

**State:** SOURCE_ONLY / UNEVALUATED / UNCOMPILED. Parent P1.4 remains **YELLOW**.

## Recovery and immutable source

- Verified previous task HEAD: `6f043485e36394550102e3926874a1d4844e1702`, packet `20261120-true-d-policy-delta`.
- This independent branch: `chatgpt/p1-full87-actual-true-d-ordered-gap-20261120-0810`, created directly from that verified SHA.
- New candidate source commit: `00cbcb9c75876ad1f7a5252397460c16b5291323`.
- New Lean file: `P1Full87ActualTrueDOrderedGap.lean`, 189 lines, blob `cba8f36679715aba611ebf5499d518eab8cde9f1`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (read at the exact commit).
- Fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Constants `c=49044063/25000000`, `K=8452171/1250000` unchanged.

## What changed mathematically

The previous true-d delta was proved for a generic `policy5` and arbitrary rank-six `fresh`. This packet takes instead the literal **full87 RAW** producer
`R=P4AOriginalFull87CompleteSixthDispatch.policy e q om N` and the independently defined **LICENSED** producer
`S=P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om N`. These two policies are NOT silently identified with the earlier generic fifth-to-sixth splice.

For the original physical supports `D_R,D_S` and attached coefficients, the only new coefficient is
\[
 D=D_R\cup D_S,\qquad
 \delta\rho(d)={\bf1}_{d\in D_S}\rho_S(d)-{\bf1}_{d\in D_R}\rho_R(d).
\]
The first candidate theorem uses the existing fixed physical attachment to show, for **every** arithmetic test `G(d)`,
\[
 \sum_{d\in D}\delta\rho(d)G(d)
 =\operatorname{signedTest}(S,G)-\operatorname{signedTest}(R,G).
\]
The original small Rosser plus/minus coefficients, physical d, and root carrier remain unchanged.

The second theorem uses **the same** coefficient with `G=highQTest X F` and combines the existing full physical stopped/frontier identity with the existing real `sharedRankFour` two-gate event theorem:
\[
 \boxed{
 \sum_d\delta\rho(d)G(d)
 =\left(\mathrm{Frontier}_{8,S}-\mathrm{Frontier}_{8,R}\right)
 -\sum_{s\in\mathrm{sharedRankFour}}\ 
      \sum_{e\in\mathrm{actualFifthSixthEvents}(s)}
               e.\mathrm{signedValue}.}
\]
Crucially the order is **LICENSED minus RAW** at true d, but the stopped event source is **RAW minus LICENSED**. The minus sign is therefore essential. Both depth-eight frontiers remain separate, and each fifth/sixth event is counted once with its original ordered List multiplicity. No inherited branch mask was added.

The third theorem instantiates the previous finite **prime receiver** density/discrepancy/negative modulus-prime invoice at those same two actual policies and that same delta coefficient; it does NOT apply the manuscript PP theorem.

## Validation actually performed

- GitHub source creation and remote fetch confirmed the source blob `cba8f36679715aba611ebf5499d518eab8cde9f1` and three candidate proof bodies.
- Static source scan detected zero forbidden proof escape tokens. This cannot detect type errors or unsound dependencies.
- In this execution environment, `lean --version`, `lake --version`, `elan --version` returned **127 (command not found)**; `/sys/fs/cgroup/memory.max = 4294967296` (4 GiB). No checkout with the fixed Lean toolchain, no isolated import staging and NO Lean elaboration occurred.
- SOURCE_ONLY / UNEVALUATED / UNCOMPILED; NOT KERNEL_REPLAYED; NO transitive axiom audit; NO independent mathematical review. No new Actions/CI, Codex, changed pins, main/master changes, merging, force updates or increased compute.

## Exact remaining gap and next proof

1. The new *actual* RAW/LICENSED policy delta has an ordered finite source; it is still **not** the manuscript's single PP-certified physical `rho_N` for all 87 archived source cells and their changed/tagged descendants. The generic prior `|delta rho| <= 2` does not yield the PP licence `|rho| <= 1`.
2. Align every saved 87 cell's real policy membership and original ordered occurrence on this same actual policy pair; include BOTH, rank9, inheritance, strict boundaries, multiplicities and the full modulus beta attachment. Prove coefficient-class membership or admissible normalization with its actual reserve cost; no new axiom-like hypothesis.
3. Authenticate common smooth labelled `W_N`, exact coprime mean and single same-rho signed PP input, with external source/version and fixed-before-N quantifiers.
4. Pay the actual primitive discrepancy and negative modulus-prime correction, all lower-half exceptions, ordinary continuation integral and both independent reserves against `H_N`; authenticate saved87 numbers.
5. Stage the complete **transitive source-only import closure** under `ImbalancedChen/` only in an isolated fixed-pin environment before minimal `lake env lean`; inspect errors and repair. Compile success, kernel replay, transitive axiom check and independent review are separate milestones.

No P1.4 closure, analytic saving, or physical coefficient licence is asserted.
