# Strict11 boundary B-floor compatibility repair

- Scope: only `boundary_B_floor` in `ImbalancedChen/P2OriginalCompactBoundaryCapFloor.lean`.
- Actual input pin: `d9ef4403bf8007efafb9264c9c03779abc24c3dd`.
- Evidence: [p2-strict-symbolic-11.log](p2-strict-symbolic-11.log), 5,203 bytes, SHA256 `eba20326993251356a8bb2eb3ab6b25d8d959bd060dfdd8dc37b8d4fa83533f4`.
- Before source SHA256: `41515e7278b5b5469251edf672aef4ad1624bbf3f87d176bc2fc28c4a641247e`.
- Frozen candidate SHA256: `9487b31fafa15242ca620819dd635ca4ef56343029b4e55b036a60ae7964499c` (14,655 bytes).

**This module was blocked in strict11.** Its proof was not executed in that batch; this is a narrowly identified compatibility repair, not a reported Boundary failure or a PASS. The actual diagnostic belongs to `ActualThirdOriginalP4AOrdinaryRawFallbackAllOld.raw_B_floor_le`: the floor estimate contains the cast of integer 256, while the following equality uses real 256.

The Raw author confirmed the identical proof pattern and agreed normalization. Boundary differs only in having `b : BoxPoint` and a direct real grid binding instead of `realBox b`. Immediately after constructing `hh`, `simp only [Int.cast_ofNat] at hh` exposes the same real divisor as `he`. The final transitivity step explicitly states `B (b 2) ≤ B (t 2)` before using `ht 2`, avoiding an unresolved endpoint during arithmetic elaboration.

The entire `he` proof, including `field_simp` and `ring`, is unchanged. The integer floor, positive scale, grid equation and original decreasing function `B t = 153/256 - (3/8)*t` are unchanged. No nonnegative-numerator premise or stronger geometric guard was introduced.

Mechanical comparison against the actual input confirms all 14 theorem headers, four complete definitions, two imports, options and local notations are byte-identical. The complete file differs by exactly the two stated proof replacements; `git diff --check` passed. This is cast/expected-type normalization with no identified mathematical gap. No Lean compilation, remote task or index operation was performed; original-checker acceptance remains pending.
