# P3.4: actual cusp normalization and signed Fourier sections

This delivery reuses existing manuscript-facing Lean code and gives it a small, independently verifiable import closure. **It does not close P3.4 as a whole.**

**Accepted source commit:** `3b3aa92475d0d6ab12a0652cc6cf2561afb99ac7`. The exact-commit run passed all 52 stages: seven fresh strict compilations, seven bundled kernel replays, parser regression checks, dependency/source checks, and the complete declaration/transitive-axiom audit. The inventory contains **113 declarations** (90 theorem entries and 23 definitions, including private and generated entries). The authoritative record is [verification/report.json](verification/report.json); [EVIDENCE_MANIFEST.json](EVIDENCE_MANIFEST.json) binds the archived files to their hashes. This evidence commit changes documentation only after that accepted source commit.

## Manuscript boundary

The reference is the [1106 English appendix, frozen commit 8ca3f6a7](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703/paper/release-20261106/en/analytic-appendix.tex), Appendix B, lines 951–982 in that revision. It uses trivial character at actual level z, cusps infinity and 1, the displayed old cusp scaling matrix, and the surviving packet phase e(-n/z).

The seven modules formalize the literal cusp geometry and fixed-height Fourier normalization needed there:

| Module | Formal content |
|---|---|
| `Part3CuspPhaseCore` | Existing e(t), its addition law, and signed cuspPhase definition. |
| `Part3Gamma0ActualCusps` | Actual Mathlib Gamma0, infinity and cusp 1, and the c-entry calculation for conjugated translations. |
| `Part3CuspScalingMatrices` | Determinant-one old/new matrices and S_old = S_new T(1/N). |
| `Part3ActualCuspWidthNormalization` | Integral cusp-1 periods are exactly N times integers; old scaling sends unit translation into Gamma0 N. |
| `Part3CuspTranslationFourierPhase` | Translation of the actual normalized-Haar Fourier integral on the unit circle and cancellation by e(-n/N). |
| `Part3ActualCuspFourierSection` | Actual horizontal traces of a Gamma0-invariant function on the upper half plane, descent to period-one sections, and their coefficient conversion. |
| `Part3SignedCuspFourierSection` | Both signed frequency branches and conjugation of the actual function, sections, and coefficients. |

For every positive integer N, positive height y and actual Gamma0(N)-invariant complex function f, the old and new coefficients are the normalized-Haar integrals of f evaluated along the corresponding scaled horizontal line. The main conversion is

    oldCoeff(n) = e(n/N) * newCoeff(n).

For natural n, the existing signed phase cancels at frequency n in the positive branch and at -n in the negative branch. Conjugating f gives the conjugate coefficient at the opposite frequency. No assumption that coefficients or f are real is used. Continuity of the descended sections is proved separately when f is continuous; the integral identities also respect Mathlib's totalized Bochner integral for arbitrary f.

These are fixed-height section coefficients. This delivery does not identify them with height-independent Maass/Eisenstein R(n), prove an oldform identity, establish a Kuznetsov or Plancherel formula, or supply the external spectral estimates cited later in Appendix B. The packet row assembly in `staging/` remains unverified and is excluded from acceptance.

## Reuse and repairs

Base: `fa22a56829ee880404516a36d498ce27dcb32f92` (`codex/yellow-closure-20261110`). `DECLARATION_MOVES.json` records the original blocks and hashes for 25 existing declarations, preserving their public qualified names and statements. The original signed source archive remains byte-for-byte unchanged. Its remaining row assembly is staged with an import of the extracted signed module so it does not redefine those names.

The ten extracted signed/conjugate declarations are reused with two proof/API repairs. The recorded original-block hash describes the donor bytes, not a claim that every repaired proof body is byte-identical to the donor.

The published 20261102 repairs already changed `AddCircle.fourier*` to the root Fourier names; those repairs are reused. Further compiler-driven repairs make ZMod arguments, the infinity notation, real matrix casts, square-root identities, function conjugation, and beta reduction explicit. The periodicity proof rewrites both sides of the old/new trace identity. No mathematical assumption or conclusion was weakened.

The three original larger modules that now import the relocated declarations (`Part3NativePeriod64Reconstruction`, `Part3ActualLiteralPacketIntegral`, and `Part3ActualCuspScalingSourceOnly`) are not included in the seven-module acceptance. Their remaining bodies were not changed and their complete downstream assemblies are not claimed compiled here.

## Verification

Pinned Lean: `leanprover/lean4:v4.33.0-rc1`, compiler commit `62eed1db4d67327ec8120be05f1a1b0847d74561`. Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. The manifest fixes all eleven dependencies, including goldbach `09b97db5764ade1246bfb77206baa1b124760958`.

With that toolchain and its manifest packages available, run from a clean checkout of the exact source commit:

```bash
python3 verification/verify_p34_cusp_normalization.py --expected-head <source-commit>
```

The script checks the frozen configuration and actual package checkouts; parses imports with Lean itself; permits only locked external objects and project dependencies freshly rebuilt earlier in the same run; recompiles all seven modules with `-t0 -j1 -M6000 -DwarningAsError=true`; runs the bundled `leanchecker` on every module; and audits the complete defining-module declaration inventory against the serialized constant inventory. This includes private and automatically generated declarations. It preserves complete compiler types and rejects unsafe declarations, newly declared axioms, or transitive axioms outside `propext`, `Classical.choice`, and `Quot.sound`. It binds evidence to exact source and object hashes and a clean Git commit.

The Lean auditor reuses the previous accepted P3 auditor from `ef1479c272bdd6b24800fa10409d793f0a2fe95c`; `AUDIT_REUSE.json` records the provenance. The import guard has regression checks for indented and same-line import commands, both parsed by Lean. External Mathlib objects are pinned cached dependencies; a new kernel rebuild of the entire external library is not claimed.

## Whole-P3.4 source coverage

`source-resolution-recovery.json` and `source-resolution.py` inspect 24 representative terminal files across the ten board leaves. They read exact committed blobs and named or hash-matched archive members. They retain different-byte source candidates and explicitly distinguish source discovery from compilation. The report concerns the fixed base and comparison commit, not every possible remote branch.

| Board leaf | Located modules | Missing source modules | Modules with different-byte candidates | Located only in attachments/archives |
|---|---:|---:|---:|---:|
| `child-1` | 250 | 23 | 14 | 0 |
| `source-d7c20fd154` | 648 | 50 | 25 | 22 |
| `source-02f097a275` | 318 | 27 | 15 | 0 |
| `source-ac61270cfe` | 736 | 49 | 28 | 28 |
| `source-c11432a253` | 756 | 49 | 29 | 28 |
| `source-5d163eba78` | 323 | 27 | 15 | 0 |
| `source-12218e6031` | 391 | 29 | 15 | 2 |
| `source-be795bf299` | 716 | 48 | 28 | 23 |
| `source-b838bef941` | 136 | 0 | 8 | 0 |
| `source-4f9bf9d0fc` | 1070 | 59 | 41 | 29 |

Counts overlap between leaves and are not sums of independent obligations. Recursion follows one disclosed source selection per module; these are explicit-import discovery counts, not compiler closure certificates. Across the chosen terminals there are 59 unresolved module names, 54 with registered hashes and five with name references only. The comparison commit `ef1479c272bdd6b24800fa10409d793f0a2fe95c` on `codex/p3-continuation-20261124` supplies none of those missing names or registered bytes. No blue leaf or the P3.4 parent is promoted to green by this sub-scope.

The next whole-node step is source recovery/version selection and assembly with the manuscript's declared external inputs. A missing source attachment is not evidence of a mathematical counterexample or a manuscript proof gap. Reconstructing an entire external spectral foundation would exceed the authorized manuscript scope.

A supplementary bounded search of 65,732 ordinary local Lean source paths found no same-name candidates for the 59 unresolved modules. Its exclusions and limits are recorded in `source-resolution-local-supplement.json`; it is not an exhaustive search of every historical repository revision.

The fixed-mark weight-two tail leaf has accessible source, but its fourth-moment/CRT/Euler-product construction is a separate route toward a spectral trace formula. [source-resolution-tail-scope.md](source-resolution-tail-scope.md) records the exact existing-code reuse and why this is outside the requested 1106 manuscript proof scope. Its available source is preserved; it is not newly re-proved or credited here.

[REVIEW.md](REVIEW.md) records the final independent read-only review of the exact accepted source and its evidence. No unresolved issue remains within the seven-module scope.
