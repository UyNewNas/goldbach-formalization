# Saving19 Higher facade, proper-gate and acceptance-wrapper review

## Scope and conclusion

This is a read-only source and acceptance-boundary review. No material blocker was found for submitting the two selected owners to the existing P1 acceptance engine. This report does **not** record compilation, kernel replay, axiom-audit results, or acceptance of either target. The reviewer ran no Lean compiler, no wrapper, and no cloud job, and modified no production source, dependency, worktree, or verification driver. The only writes for this review are the report, review manifest and recorded driver diff in this directory.

The reviewed targets are `ImbalancedChen.P2OriginalSaving19HigherMoments` and `ImbalancedChen.P2OriginalSaving19GateProper`. All exact file hashes, lengths and paths are recorded in `REVIEW_MANIFEST.json`. The static review is preserved at this point even if later P1 jobs accept these targets.

## Higher facade: public contracts and exact changes

The candidate is 15,058 bytes, SHA-256 `da2281584acf0c11940e4ae38dd5a6871f74f81981d9a3be9e2609f5f7459181`. An independent in-memory reconstruction of the complete candidate from the production facade at commit `0fa84a8bf7c3a794d29279f381c8b5b18a8d3b2d` matched the candidate byte for byte. The reconstruction changed only the imports, the two guard proof bodies, and four explicit factorial syntax repairs.

The imports are exactly `P2OriginalSaving19MomentFloorConsumer` and `P2OriginalSaving19HigherMomentsMomentStructure`. The proof of `integratedPower_newton_guard` delegates to `ProofPieces.integratedPower_newton_guard_structural y i k hk`; the proof of `duplicateH_author_guard` delegates to `ProofPieces.duplicateH_author_guard_structural y i k hk`.

The four repaired headers are `integratedPower_newton_guard`, `binomial_normalization`, `integral_bary_interpolate_power`, and `integral_interpolate_mul_power`. Each changes `9.factorial` to `Nat.factorial 9`. The old notation failed to elaborate under the current Lean version; this is an explicit repair of the intended natural factorial, not a claim that those four old header texts or previously elaborated types were identical.

The 36 original public contracts comprise 30 facade declarations and six retained Core declarations: `duplicateH`, `baryCoefficient`, `bumped`, `integratedPower`, `completeH`, and `completeH_cons_succ`. Across the 36 there are 12 definitions, one structure and 23 theorems. Thirty-two header texts are unchanged; the remaining four differ only by the documented syntax repair. The independent declaration comparison, ignoring comments and irrelevant whitespace, found no additional change to binders, hypotheses, integral domains, normalization, quantifiers, or definition/structure mathematical code.

Relative to the production facade at `0fa84a8b`, 31 complete declarations and 21 theorem proof bodies are byte-identical. Relative to the archived original facade, the counts are 29 and 19. The difference in those counts is explained by two **pre-existing** proof repairs that the new candidate retains unchanged from production: `rationalMoment_cast` uses the explicit `hmap`/`change` proof, and `integerNewtonNumerator_spec` includes `smul_eq_mul`. These are not new changes in this candidate.

The new real integrated-power guard retains arbitrary `y : Fin 9 → ℝ`, arbitrary `i : Fin 9`, `k : ℕ` and only `hk : k ≤ 6`, with denominator `(Nat.factorial 9 : ℝ) * ((9+k).choose k : ℝ)`. The rational author guard retains arbitrary `y : Fin 9 → ℚ`, the same index/degree quantifiers, and the full sum over `j : Fin (k+1)` of `completeH (List.ofFn y) (k-j.val) * y i ^ j.val`. No positivity, distinctness, nonzero-coordinate, numerical-data, or desired-conclusion hypothesis was added.

The source import closure falls from 285 to 224 project modules: 66 former enumerated provider modules are removed and five structural/symmetry modules are added. All 224 candidate source-input length/hash bindings were checked. The old GuardK/AuthorK family is absent from the new closure. Retained LowBoundary and SymmetryPilot are not imported by the new facade. These are source-closure observations, not object-acceptance claims.

## Exact provenance of the two allowed facade preimages

At commit `0fa84a8bf7c3a794d29279f381c8b5b18a8d3b2d`, the production path `ImbalancedChen/P2OriginalSaving19HigherMoments.lean` has SHA-256 `910de365b810a41d17f7781856e384512cb0080d5051c6be7045643f0004b3b1`.

The original SHA-256 `59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e` belongs to the **distinct archived Git path** `docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean` at that commit. Both local provenance snapshots were independently checked against those exact Git objects. The claim that the P1 target slot may currently contain the archived original is parent-reported; this review did not inspect the remote slot and does not claim that 59cc was the production path at 0fa.

The installer allows only those two known facade preimages, the exact new bytes, or an absent target. It records and backs up the actual observed preimage through the unchanged installation engine. The provenance snapshots in the source-review package are not claimed to be actual installation backups. Any unknown preimage must stop before installation.

## Proper gate: exact obligation supplied

The candidate is 834 bytes, SHA-256 `143a038b688b7ea1eb944bcac8a917e22728adc1158e4ed6d254f7db6905fad1`. It imports only `OriginalAscendingThirteenLiteralAffineRows`.

Its private closed theorem requests `∀ p : Fin 103, ∃ j : Fin 8, literalPool p j.succ ≠ 0` using `decide +kernel`. The public theorem specializes it at `literalIndex c g`, for arbitrary `c : Fin 13` and `g : Fin 97`. Since `exportedCoefficients c g` is exactly `literalPool (literalIndex c g)`, the specialization has the desired type without a new index remapping or numerical-data substitute.

This supplies only the normal-nonzero first conjunct of the existing `OwnedSource.original_gate_checks`. It supplies no vertex nonnegativity, source inclusion, Archive parse, floor certificate, pulling overlap, or chosen-plane integral result. The 103-entry private statement is a closed proof obligation, not an additional hypothesis; its successful reduction and resource use remain for actual P1 verification. Full-owned checking must include the private theorem and any generated auxiliary declaration from `decide +kernel`, as provided by the unchanged engine.

The gate closure has 207 project modules including the target. Its source manifest intentionally lists 206 dependency records and describes the target separately. All 206 dependency bindings are an exact subset of the independently checked 224-module facade binding map. No Archive-named dependency occurs. The original literal-row supplier remains 19,326 bytes with SHA-256 `7abe6bff570768ae6b5c3baf61d71265c0799e57608ffc8a89c92aae4cc36780`.

## Two-target driver: retained acceptance boundary

The reviewed driver is `run_higher_facade_and_gate.py`, 20,873 bytes, SHA-256 `1fc656efb863e9b17bf4d88b04de619e7af051a2adf98db843176b6be61e24a8`. The comparison baseline is the existing `run_higher_structural.py`, SHA-256 `e0109bacac3b07b608b4d1253e836a7fef34d7c7db5f0dd4cabfec145b8ab652`. The complete textual diff is recorded in `DRIVER_DIFF.patch`.

The published Batch13 API is still loaded from commit `4cea0407c1258eaddd7d4952cffa4aea67310422`, path `docs/p1/20261125/batch13-repairs/run_repairs.py`. Its actual Git-object hash was rechecked as `95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea` (24,975 bytes). The original helper pins, runtime review pins, lane-0 serializer, and configuration checks are retained.

The `api.normal_one`, `api.audit`, and both `api.context` calls are AST-identical with identical arguments. The functions `check_configs`, `binding`, `install_one`, and `check_installed` are AST-identical to the structural wrapper. The worker changes only its event label. The main execution path adds a separate `review-inputs/<full repository path>` destination for review evidence, preventing the two distinct `SOURCE_MANIFEST.json` files from colliding.

The scope manifest permits exactly two owners and exact target hashes, direct imports, byte lengths and closure counts. The driver freezes ten retained supplier hashes when those suppliers occur in the selected closure. It reads every project dependency from the selected full source commit, requires that commit to descend from the reviewed P1 baseline, and checks all installed dependency source hashes and import lists against that commit before installing the selected target. The remaining dependency bytes are bound dynamically to that exact commit; this is an actual-context binding, not a claim that a target hash alone certifies a future dependency tree.

Only the selected target can be installed. GateProper permits absent or identical bytes only. The facade permits the two explicit historical preimages with the unchanged backup/install engine. Unknown target bytes, incoherent dependency sources, changed protected roots, altered review inputs, or mismatched runtime/configuration evidence stop the operation. The run path is restricted to the established P1 repository/project; local `--check` remains explicitly non-accepting.

The before/after source/object/trace/configuration/runtime contexts must agree. Acceptance still requires the original normal compile and audit engine to accept the selected owner and no accumulated error. Successful suppliers are checked for readiness and are not requested for recompilation. The wrapper keeps full-higher/whole-P1/whole-P2 completion flags false. This review does not execute these gates or certify their runtime outcome.

## Manuscript and proof-credit boundary

The facade reuses the independently reviewed three structural owners. The underlying manuscript simplex-moment formula is in `chen-imbalanced-semiprimes` commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`, `paper/release-20261106/en/numerical-appendix.tex`, label `num:simplex-moment`. The file SHA-256 is `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`. The bounded Newton/duplicate-node identities are finite algebraic consequences of the existing Core definitions connecting the producer expression; this review does not claim that the manuscript states an explicit Newton theorem.

The parent reports formal P1 acceptance of the three structural suppliers under `job_1b0e5c52fcfe440b9bd27179ed7fdf14`. This review cites that as parent-reported evidence and does not manufacture or relabel those receipts. The separate prior structural read-only review retains its own zero-compilation timepoint. Facade/gate acceptance, full numerical Archive acceptance, and downstream chosen-plane integral/endpoint completion all remain distinct obligations.
