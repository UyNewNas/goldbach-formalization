# Independent read-only review of the accepted P3.4 sub-scope

Reviewer: independent agent `/root/p34_review`.

Reviewed source commit: `3b3aa92475d0d6ab12a0652cc6cf2561afb99ac7`.
Base: `fa22a56829ee880404516a36d498ce27dcb32f92`.

**Final assessment: ready to publish the seven-module scoped result. No unresolved Critical, Important, or Minor issue was found. This is not acceptance of whole P3.4.**

This record summarizes the reviewer's final report. The reviewer independently read the source, complete verification records, logs, hashes and Git state. The review did not repeat the full compilation run and is not a separate third-party mathematical certification.

## Evidence checked

- The expected source commit, recorded checked commit and observed Git HEAD all matched the source commit above.
- The formal report was `PASSED`; all 52 stage exit codes were zero. Each retained log's recorded command matched its stage in the report.
- All seven strict compilation commands used `-t0 -j1 -M6000 -DwarningAsError=true` and emitted no diagnostics.
- All seven bundled `leanchecker --verbose` logs explicitly replayed their named module.
- All three actual-parser import-scope regression tests passed.
- The raw audit output, parsed declaration inventory and per-module counts agreed: 113 unique declarations, comprising 90 theorem entries and 23 definitions, including private and generated entries.
- The 14 source/configuration hashes matched both the current files and the checked commit's bytes. The seven object hashes and two tool binary hashes matched the observed files. No extra private/server object part was present.
- All eleven package checkouts matched the fixed manifest and had empty dirty-state logs.
- The formal run's initial and final working-tree checks were empty.
- All 55 exported verification files matched the completed run's original files byte-for-byte.
- The evidence/documentation changes made after the run did not change the fourteen verified source/configuration files.

| Module suffix | Inventoried declarations |
|---|---:|
| `Part3CuspPhaseCore` | 4 |
| `Part3Gamma0ActualCusps` | 11 |
| `Part3CuspScalingMatrices` | 15 |
| `Part3ActualCuspWidthNormalization` | 20 |
| `Part3CuspTranslationFourierPhase` | 12 |
| `Part3ActualCuspFourierSection` | 38 |
| `Part3SignedCuspFourierSection` | 13 |
| **Total** | **113** |

Every inventoried declaration had a complete saved compiler type without the truncation marker. There was no axiom declaration. Transitive axioms were contained in `propext`, `Classical.choice`, and `Quot.sound`.

| Evidence file | SHA-256 independently checked |
|---|---|
| `verification/report.json` | `5f66003025ddd9cd6ea05d1c474ea45ef2a39514ea2b3fcd89cf589a37bb69f6` |
| `verification/declarations.json` | `e34f85994c01ed5a40ce86106c32c1aa0136bd2d0bddd978873bb97aaf5afd88` |
| `verification/theorem-types.txt` | `e16ae71a8a5a4e02b9241a57d7ba9e7167ec52e47bb293ffb29bf54600766027` |

## Mathematical review

The reviewed matrices satisfy S_old = S_new T(1/N). The old section is the right translation x ↦ x + 1/N of the new section. With the actual normalized-Haar coefficient convention using Fourier character -n, this gives the positive factor e(n/N). The existing positive-branch packet phase e(-n/N) cancels it.

The negative branch retains frequency -n and uses e(+n/N). Conjugation changes the actual function and the frequency together, giving coeff(conj F,n) = conj(coeff(F,-n)); it does not add any reality assumption. Actual Gamma0 N invariance and positivity of N and y remain in the relevant theorem statements. Continuity is retained as an explicit premise where used.

The proof/API repairs do not weaken conclusions or replace hypotheses. In particular, the periodicity repair rewrites both sides of the old/new trace identity; the signed repairs use the concrete continuous complex-conjugation map and beta-reduce the integral's pointwise expression before rewriting.

## Provenance checked

All 25 moved public declarations retain their qualified names and original signatures. The former active locations no longer define them. The original signed archive remains byte-identical to the base, with SHA-256 `766d00b552b66d4467d857e9e02553fc9431410d9028276fdd491f45ec747336`.

All four original-block hashes in `DECLARATION_MOVES.json` match the donor blocks. The staged row-assembly remainder is unchanged and imports the promoted signed module. The ten signed/conjugate declarations are described accurately as reused with two proof/API repairs, not as a byte-identical repaired prefix. The Lean audit command body after the module list matches the specified `ef1479c272bdd6b24800fa10409d793f0a2fe95c` donor.

## Findings and resolution

**Important, resolved:** the first verifier version used a line regex that missed valid indented imports and multiple import commands on one line. The reviewer confirmed those syntax forms with the pinned Lean parser. The final verifier uses `lean --deps`, validates actual resolved paths against freshly rebuilt project objects and locked external roots, checks the audit imports as well, and includes the three passing parser regression checks.

**Minor, resolved:** promoted module headers still described them as uncompiled or future source. They now retain historical provenance and point to the scoped verification record. Headers of genuinely unverified assemblies were not promoted.

No unresolved issue remains within this reviewed scope.

## Explicit exclusions

The review does not accept whole P3.4, identify fixed-height section coefficients with height-independent Maass/Eisenstein R(n), or prove oldform identities, Kuznetsov, spectral completeness, Plancherel or the later spectral estimates. The remaining packet assembly and three larger original modules are outside compilation acceptance.

The accepted width statements are the explicit integer cusp-one periods N times integers, the matrix identities, and the resulting period-one traces. No stronger unlisted full-stabilizer theorem is claimed. The whole external Mathlib object closure was not freshly rebuilt/replayed as a separate deliverable. The broad source-resolution atlas was produced by a separate source audit; this review grants it no additional formal-proof or compiler-closure credit.
