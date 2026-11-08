# P5.6 → h34 — exact marked-family scaling and normalized-count obstruction

Date: 2026-11-09 (China calendar). Scope: manuscript-internal source-only h34 candidate.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Incoming remote head: `47fce62da081ad995de44ef7f4e4157274df313b`.
Source commits: `0915650bddae55e9b449d868004ba1ef49b31b22`, corrected by `7ecaaac8e38024c91b65723b4e69415d4a1523fe`.
Source blob after correction: `9e5669f761d113f834ff333152b883170be31e5e`.
Candidate module: `Part5OriginalH430MarkedScalingInvariance.lean`, 138 lines, six theorem bodies.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (`paper/source/manuscript-body.tex`).

**PARTIAL_SOURCE_INCREMENT · SOURCE_ONLY · UNCOMPILED · UNEVALUATED · FULL_H34_OPEN.**

## Actual new manuscript-local mathematical scope (candidate, not kernel-verified)

1. `literal_phi_homogeneous`: actual `Phi N Q D (c*sigma) w = c * Phi N Q D sigma w` at unchanged physical `Q`, source sieve cutoff and product marks.
2. `literal_theta_homogeneous`: same exact degree-one homogeneity for the REAL `Theta N Q D sigma`, retaining singular factor, totient and logarithmic denominator.
3. `literal_quotient_homogeneous`: same homogeneity for actual `weightedQuotient` without introducing a second source weight.
4. `normalized_phi_unchanged_by_global_rescaling`: under primitive `Theta_pos` gates, positive uniform scaling leaves `Phi/Theta` unchanged.
5. `normalized_quotient_unchanged_by_global_rescaling`: the local quotient/Theta coefficient also remains unchanged under uniform positive scaling.
6. `normalized_original_q_count_inverse_rescaling`: the original arithmetic `originalReceiver N p` cardinality does NOT change with sigma, while its ratio to the same physical Theta scales by `1/c`.

These relations show why simply magnifying an arbitrary marked sigma cannot improve the normalized H430 finite source coefficient or replace missing arithmetic q-to-marked-product coverage. They do NOT rule out a correct nonuniform or genuinely constructed sigma, and do not equate marked product d with quotient prime q. The fixed manuscript's original sigma/mark choice must still be identified and its admissibility independently proved.

## Dependency and scope audit

Reused exact in-repository definitions: `P2EnhancedTwentyOneSameQWeighted.Phi`, `Theta`, `weightedQuotient`, and `Theta_pos`; exact `originalReceiver N p`. Reused ordinary `Finset` sum and ordered-field algebra only.
No PNT/Mertens/BV proof was implemented, no new external analytic theorem was assumed, and no target-equivalent q-to-marked count licence was introduced. No source beyond this h34 module and its three new docs was changed. P1.4, P3.6, manuscript, c/K, root norm 7/2, row norm 12, alpha, same-Q and original q/tag multiplicities are unchanged.

## Validation (actual limits)

- GitHub connector write permission and exact branch ref checked before source commit. Source blob, six declaration names and additive one-file source diff read back. Source revision added existing originally-opened Wu2008DoubleSieve and Bombieri1965Richert418 namespaces.
- Static source scan found no sorry/admit/custom axioms/unsafe/native escape; paired parentheses counted. Static checks are NOT Lean parsing or proof checking.
- Actual container test: `command -v lean` and `command -v lake` returned no executable. `git ls-remote https://github.com/UyNewNas/goldbach-formalization.git HEAD` failed because DNS could not resolve github.com.
- No executable Lean/Lake compilation, elaboration, kernel replay, transitive axiom audit, or 430 numerical certification occurred. Numerical430 and inherited finite guard statuses remain UNEVALUATED. Formal green credit is zero.
- Existing `.github/workflows/lean.yml` invokes a large full-root 150-minute job on push, not a staged source-only h34 target. These source-only commits use `[skip ci]` to avoid triggering an unrelated costly full-root job; no workflow configuration was changed and no CI success is claimed.

## Still unclosed in manuscript

1. Identify actual U3/U4 selected marked family B/sigma and quantitatively match its finite positive source to each original q/tag arithmetic occurrence; current weight homogeneity neither constructs nor bounds this matching.
2. Pay the positive original q-count minus 5 Phi gap with an actual admissible normalized family; supply full/selected/inherited owner, root weights, deeper history/cross-q/tag multiplicities, six rejection lanes and signed Euler suffix.
3. Complete all-action CLOSED-CELL count induction using actual Buchstab/retention and bank records, correct base/switched/seed/floor payments and feedback-to-integral.
4. Close manuscript-local PP/same-rho instances, native-history residual/equality/inherit mass, outer integrals to Theta/count, and the joint 430+11 nested causal refinement.
5. Stage/install the held source-only dependency chain in an unchanged pinned Lean 4.33.0-rc1 toolchain, compile, replay kernel, audit all transitive axioms and execute finite certificates.

Next action: inspect the pinned original U3/U4 marked product construction and prove an actual source membership/coverage statement, not global rescaling or a target-equivalent bound. On a provisioned pinned Lean environment first elaborate this module and repair any genuine compiler errors.

**完整h34稿内证明仍未闭合。**
