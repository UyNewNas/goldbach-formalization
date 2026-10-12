# Part 5 round 2: actual Buchstab input for Part 2

## Acceptance status and fixed source

**All three validation gates passed.** The corrected source passed strict
official frontend elaboration with `trustLevel := 0`, bundled kernel
replay, and the defining-module transitive axiom audit. Part 2 can receive
the independent theorem now, without waiting for the complete Chen mean.

| Identity | Value |
| --- | --- |
| Repository / branch | `UyNewNas/goldbach-formalization` / `chatgpt/chen-p5-lower` |
| Unchanged common proof baseline | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Previous handoff | `3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa` |
| Corrected proof source | `ImbalancedChen/CurrentChenBuchstabRefinement.lean` |
| Corrected source SHA256 | `02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5` |
| Frozen manuscript | `ba6ec11d800eccc54406490631895e174de85766` |
| P2 checkpoint reviewed | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` |
| Receivers | Part 2 immediately; Part 0 for integration |

The only proof-source change since the first round replaces
`field_simp [hxp.ne'] <;> ring` by the same two sequential tactics. This
fixes the actual strict-compiler `unnecessarySeqFocus` diagnostic. It
changes no declaration type, definition, cutoff, quantifier or constant.

## Complete theorem types

All names below are in namespace `ImbalancedChen`. These readable source
signatures agree with the successful compiler-generated inventory in
[compiler-types.txt](../verification/parts/p5/round2/buchstab/compiler-types.txt)
and [compiler-types.json](../verification/parts/p5/round2/buchstab/compiler-types.json).
The latter also includes the private helper and every transitive axiom.

```lean
theorem currentChen_buchstab_lower_first_segment {s : ℝ}
    (hs : (7 : ℝ) / 3 ≤ s) (hs₃ : s ≤ 3) :
    (11 : ℝ) / 20 ≤ LiLiuPrereqBuchstab.buchstab s

theorem currentChen_buchstab_lower_transition {s : ℝ}
    (hs : 3 ≤ s) (hs₁₀ : s ≤ (10 : ℝ) / 3) :
    (11 : ℝ) / 20 ≤ LiLiuPrereqBuchstab.buchstab s

theorem currentChen_buchstab_lower_on_tail {a L : ℝ} (ha : 2 ≤ a)
    (hbase : ∀ u ∈ Set.Icc a (a + 1),
      L ≤ LiLiuPrereqBuchstab.buchstab u) :
    ∀ u : ℝ, a ≤ u → L ≤ LiLiuPrereqBuchstab.buchstab u

theorem currentChen_buchstab_eleven_twentieths {s : ℝ}
    (hs : (7 : ℝ) / 3 ≤ s) :
    (11 : ℝ) / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

The final theorem has no analytic supplier premise. It concerns the
literal `LiLiuPrereqBuchstab.buchstab` in the unchanged pinned dependency
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.

## Why the proof covers the whole unbounded interval

The initial window is the complete unit interval `[7/3,10/3]`.
On `[7/3,3]`, the proof uses the actual formula
`buchstab s = (1 + Real.log (s - 1)) / s`. A proved one-term logarithm
expansion supplies `2*(x-1)/(x+1) ≤ log x`; a quadratic inequality using
both endpoints supplies the required `11/20` bound.

On `[3,10/3]`, the actual weighted delay integral is rebased at `3`.
The pinned global `1/2` bound pays its entire integrand, and the same
logarithm estimate gives `log 2 ≥ 2/3`. This covers the transition up to
and including `10/3`.

The general tail theorem then propagates a constant lower barrier from
any whole unit interval `[a,a+1]`, `a ≥ 2`, by induction on succeeding
unit windows. It uses the weighted delay identity and integral
monotonicity with the correct delayed argument `t-1`. The final
Archimedean step covers every real `s ≥ 7/3`. There is no finite upper
cutoff, sampled-value argument, alternative Buchstab definition, or
monotonicity assertion about the Buchstab function itself.

## Validation method and scope

| Gate actually executed | Result |
| --- | --- |
| Strict target frontend, reused from Part 0 after source/object matching | Exit 0; 218.741 seconds; source SHA256 `02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5` |
| Original bundled `leanchecker --verbose` on the same object | Exit 0; 364.183 seconds; object SHA256 `33663881df095e9bebdc3ea62b466da55da6cb8e33d1d73985c0053792162980` |
| Strict defining-module audit through the official frontend | Exit 0; 504.185 seconds; all 5 theorems inventoried, including the private helper |
| Transitive axioms of each inventoried declaration | Exactly `propext`, `Classical.choice`, `Quot.sound`; no other axioms |

The [machine-readable receipt](../verification/parts/p5/round2/buchstab/receipt.json)
contains the full commands, binary and pin hashes, source/object hashes,
scope and original record locations. The copied raw
[compile](../verification/parts/p5/round2/buchstab/compile.log),
[kernel replay](../verification/parts/p5/round2/buchstab/kernel-replay.log),
[axiom audit](../verification/parts/p5/round2/buchstab/axiom-audit.log), and
[initial strict failure](../verification/parts/p5/round2/buchstab/initial-strict-failure.log)
logs retain the actual diagnostics. The three unchanged Buchstab dependency
builds are recorded in
[dependencies.json](../verification/parts/p5/round2/buchstab/dependencies.json).

Part 0's completed dependency builds and target build are reused only
after matching the exact source and object hashes. The source-identical
target object is copied to the Part 5 isolated output directory for the
remaining checks. The original Lean toolchain binaries are unchanged.

The frontend invocation is the official `Lean.Elab.runFrontend`, driven
by stock Lake with explicit `trustLevel := 0` and `warningAsError := true`
for the target and audit. This is a frontend compilation receipt, not a
claim that the repository's `lake build` command or GitHub CI succeeded.
The driver uses Lean's standard initializer-enabling API; it does not
change the kernel, proof declarations or trust level.

The bundled `leanchecker --verbose ImbalancedChen.CurrentChenBuchstabRefinement`
replays the declarations defined by that module against its imported
environment. This is not a `--fresh` replay of every declaration in every
dependency. The audit inventories declarations by their defining module,
including the private logarithm helper, rejects unsafe or new axiom
declarations, and uses Lean's transitive `collectAxioms` collector with
the allowlist `propext`, `Classical.choice`, `Quot.sound`.

No Codex CLI/task or CI rerun is used for this delivery. The fixed
toolchain, Lake configuration, manifest, manuscript and shared theorem
entry points are unchanged.

## Part 2 consumption boundary and units

The theorem supplies exactly the analytic increment

\[
\omega(s)-\tfrac12\ge\tfrac1{20}\qquad(s\ge7/3).
\]

For P2's paired coordinates,
`(t,u,z,w) = (log_N p4,log_N p3,log_N p2,log_N p1)`, the needed argument
is `(1-t-u-z-w)/z`. The same outer mask is therefore `E_N(p3,p4)`, as in
the actual retained Y11 sum. The supplied theorem can be applied once
the actual selected fibre proves this argument is at least `7/3`.

The reviewed P2 checkpoint already uses

\[
K/80 = K\,(11/20-1/2)/4
\]

inside its iterated integral. The quarter factor is already included.
A certified gain `g` in that integral contributes `4*g` to the unscaled
weight mean `W_N`, whose target remains
`4*currentC = 49044063/6250000 = 7.84705008`.

This independent theorem does not provide the full adopted mask, the
full-mask certificate checks, the saved-floor semantic bridge, or the
actual adopted-parent comparison. Those inputs must still be proved by
their owning Parts before inserting the paired improvement into the
eleven-term mean. P2's first cell does not replace its full mask. The
adopted `7/3` refinement does not receive an additional old `12/5` gain.

The common density theorem for `K`, all remaining oriented row estimates,
the complete Chen mean and final `hLower` are not prerequisites for
receiving this Buchstab result and are not asserted by it.
