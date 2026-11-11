# P1.4 — genuine rank-eight prefix physical-level bound (source-only)

Recovery HEAD checked: `c0ee142fe551ea8d36da6bbe6f65a12a0899e490` on `chatgpt/p1-full87-original-fifth-global-ceiling-20261112`. Isolated successor branch: `chatgpt/p1-full87-real-rank8-prefix-bound-20261112`. New substantive source commit: `58b17a2e40c7d95a58bd5ae4eb0ca1be7ed0df75`.

Source: `docs/source-only/20261112-full87-real-rank8-prefix-bound/P4AOriginalFull87RankEightPrefixLevel.lean`; Git blob `8e845a8446a4949536df4f2cb2881fc3c976d404`. Full source remote-read after the commit, 110 lines, two theorem proof bodies.

## Mathematical change, exactly scoped

Unlike the predecessor's **scalar** cap alone, this packet connects (a) the original licensed-sixth/eighth `policy` rank-eight *true* frontier, (b) its exact rank-eight frontier equality to its own `sixthPolicy`, (c) the existing actual rank-eight **seventh-step Rosser admission** with the same sixth ancestor, and (d) the previous all-history `level6Exponent ≤ 299/500`.

For every actual rank-eight frontier state `s` of this very policy on the literal `roughPrimeUniverse`, if the original buffer `data.e ≥ 0` and `1<N`:

```
(s.selectedPrefix.prod : ℝ) < (N : ℝ) ^ (299/500 : ℝ).
```

The strict product inequality is supplied by `ordinaryRosserPrefixAdmissible` of the ACTUAL frontier, **not** inferred from the scalar level bound. The actual fifth predecessor, third-inactive fallback and new accepted sixth policy are all retained. The equality is only at rank eight, not a claim that the old/new eighth frontiers coincide after different actions.

A second candidate accounts for the original small-factor multiplication at this **rank-eight prefix**: for `a:ℕ`, `a<L`, and the fixed (state-independent) numerical scaling requirement `L * N^(299/500) ≤ N^theta`, we get `a * s.selectedPrefix.prod < N^theta`. The scaling requirement is deliberately NOT invented as a proved property of the manuscript parameters.

This is not a final first-exit leaf theorem. After rank eight, true retained descendants may select additional rough primes. In particular this packet does not prove terminal rough `b < N^(299/500)`, full physical `ab < N^theta` for every live coefficient, or the original smooth-singleton PP licence. All original sign, occurrence and parent data are untouched; no auxiliary mask.

## Actual verification and constraints

- Read previous REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF, complete preceding 207-line source, the retained-terminal recursion candidate, actual licensed sixth/eighth policy, existing sixth-frontier admission proof and fixed manuscript section.
- Frozen manuscript verified `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, source `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; anchors `eq:current-PP`, `lem:current-sharp-prime`, `eq:current-sharp-pi`.
- GitHub source readback: blob `8e845a8446a4949536df4f2cb2881fc3c976d404`; no banned proof escapes in two candidate bodies.
- Local `lean --version`, `lake --version`, `elan --version`: **all exit 127** (command not found). Fixed `.lake/packages` absent. Therefore no matching Lean elaboration, build, kernel replay, transitive axiom audit or independent review; no original87 numerical replay. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED.**
- The source-only `ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy` and `ImbalancedChen.P4AOriginalFull87WholeSixthCeiling` imports require staging the exact dependency packets under corresponding `ImbalancedChen/*.lean` module paths in a disposable matching project before typechecking. These files do not exist under the root module tree, and static checks cannot substitute for staging+Lean.
- No new axiom/sorry/admit/native_decide/unsafe, CI, Codex, main/master write, force push, merge, pin change or extra resources.

## Unmet exact obligations

1. Prove every true retained **terminal** old-sixth / selected-new-eighth / inherited-new-eighth leaf product bound, not merely rank-eight prefix; preserve original skipped branches and multiplicities.
2. Discharge actual fixed-before-N small-factor scale `L * N^(299/500) ≤ N^theta` for one `theta<1`; connect true physical nonzero `d=a*b` to terminal leaves and original owner map.
3. Establish true signed smooth-singleton sharp PP coefficient admissibility, correct X/endpoints and same `H_N`; external statement remains registered, unproved and not invoked.
4. Complete original ordinary residual integral, actualParent weighted loss, saved87 numerical witness, low/high q, raw/finite/filtered, rank9, changed/tagged and independent compiler/density reserves.

Next mathematical action: in `ImbalancedChen/P4AActualSixthFrozenEighthAdmission.lean` pattern of step-validity induction, extend the genuine rank-eight state invariants to **post-eight retained terminal descendants** for both literal `policy` branches, first resolving `selectedCap` versus sixth fallback. Only then transport full physical modulus and PP licence.
