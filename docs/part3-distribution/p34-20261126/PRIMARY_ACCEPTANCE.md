# P3.4 literal primary arithmetic acceptance — 2026-11-26

## Fresh-checkout reproduction after the harness repair

The four-module scope also passed at the repaired published source **`e84c5a1c2f70f983de7bafc80472fa2d2eb947d0`**, tree `fca71215e562bfe8ee5a48c0de3d59589a94b2e2`, in P3 task `5e2f28aa60a64f3dbd7b5ea1db7a0e06`. All **43 stages and 63 declarations** passed again, with four strict compilations and four bundled kernel replays. This run started in a separate clean worktree with **zero project `.olean` files** and ended with exactly the four listed project objects. The parser regression fixtures were temporary Init-only modules and required no old cusp objects.

The new receipt is `primary-clean-cloud-report.json`; the full 47-file output archive is `primary-clean-cloud-verification.zip`, SHA-256 `7c2c78414309545eee5e4ec6d13eda97c0c634ee6a7bd967b141d7d2b3d03e40`. The corresponding archive manifest, fresh-project-object inventory and `fresh-cloud-task.json` preserve the exact evidence. The original receipt below is unchanged. `SOURCE_REUSE_AT_FIXED_SOURCE.json` verifies that only the two shared harness files differ between its bound source set and the repaired source; every Lean, audit and configuration byte in that set is unchanged.

## Accepted result

Exact GitHub source **`2b284342fce23962a1b431d8003cb5cdffac8128`**, tree `e9e7bd369f6aeb5c6af5b2f59bd2ebfb0752fc4d`, passed P3 cloud task `4352f14875534bf8a0f67a21c7dd0dc6` with exit 0 in 86 seconds. The local reviewed source `a2332ed58aea9ed41363c4366a96c301ef5d7989` has the same tree.

All **43 stages** passed. The four modules received strict compilation and bundled `leanchecker` replay, actual parsed-import checks, complete serialized/defining-module inventory agreement, and transitive-axiom auditing. The inventory has **63 declarations**, distributed 11 / 24 / 22 / 6 across:

1. `Part3PrimaryPrimeSupport`
2. `Part3LiteralReciprocalSource`
3. `Part3FixedRhoPrimaryFiniteCore`
4. `Part3LiteralPrimaryOldformArithmetic`

The only transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`. Toolchain and package pins are unchanged from the packet acceptance. No fresh replay of the entire external Mathlib closure is claimed.

## The two actual-source endpoints

`ImbalancedChen.Part3.LiteralPrimaryOldformArithmetic.literal_primaryFibre_abl_licenses` takes membership in the **existing** computed primary fibre of `nonzeroSource (carrier A a T H F)`. Let `z` and `y` be the actual output, let `nu` be its computed primary key, and let `n = (y / (nu : Int)).natAbs`. It derives:

- `0 < nu`, `y != 0`, integer divisibility of y by nu, and the signed reconstruction `nu * (y / nu) = y`;
- `0 < n`;
- `Nat.Coprime n (a.natAbs * nu)`;
- `Nat.Coprime (a.natAbs * nu) z`;
- for every natural label `qf` and `v`, `supportedPart (z / gcd (v*qf) z) (a.natAbs*nu) = 1`.

The second theorem, `literal_primaryBeta_abl_licenses`, takes the nonvanishing of the original grouped beta on the same computed fibre. It obtains a genuine source witness with the existing `beta_ne_zero_mem_image`, then applies the membership theorem at that exact output. No desired coprimality conclusion or source identity is added as a premise.

The signed quotient is preserved before taking its natural absolute value. The full prime support of the computed nu supplies the extra coprimality beyond `(n,|a|)=1`. The original two fixed-unit gates supply the level coprimality. The cofactor divides the actual level, so its supported part is 1. Quantification over arbitrary natural-number labels proves this integer formula only; it asserts no existence or spectral identity for illegal oldform labels.

## Reuse and compatibility evidence

Fifty-seven existing source declarations were reused. Their exact donor blocks, original signatures, target definitions and compiler type fingerprints are recorded in `PRIMARY_DECLARATION_MOVES.json`. All donor proof bodies are preserved. The original private `carrier_data` is exposed under the documented public name with unchanged type and body so its retained parent consumer can still use the one proof. The scalar oldform cofactor and two private arithmetic helpers are promoted from the immutable original archive.

The five retained analytic donor remainders were compared against the baseline after the planned extraction and import changes. Those large parent modules are not covered by this four-module compilation claim. Source-only archives remain byte-identical. The only initial error in a new endpoint proof was a missing explicit natural-number binder annotation; the correction adds no mathematical assumption.

The exact relation to the original row is the existing instance `A=1`, `a=D.block.atom.residue`, `T=D.sCarrier`, `H=D.hBound`, and `F=Icc (ceil (-D.fScale)) (floor D.fScale)`. Once the genuine original data definitions are available, original block membership supplies this primary-fibre membership. A geometric `nCarrier` may contain beta-zero points, so its original arithmetic consumers must use the membership endpoint; nonzero beta must not be added to their hypotheses. The sign/dyadic `blockBeta` is not definitionally the unrestricted primary-fibre beta: obtain its original source witness first.

## Manuscript and evidence

This is the finite arithmetic of the 1106 manuscript's primary split and Appendix B ABL substitution, not a formalization of external spectral foundations. The manuscript is `UyNewNas/chen-imbalanced-semiprimes` at `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`, `paper/release-20261106/en/analytic-appendix.tex`, in particular the original coefficient/support and the paragraphs around lines 964–982.

At the accepted clean source:

```sh
python3 verification/verify_p34_primary_arithmetic.py \
  --expected-head 2b284342fce23962a1b431d8003cb5cdffac8128 \
  --output-dir .lake/p34-primary-cloud-acceptance
```

`primary-cloud-report.json` and `primary-cloud-task.json` bind the exact cloud run. `primary-cloud-verification.zip` contains all 46 original output files and has SHA-256 `4948c8c045d48036e6dd1e2b79242a00ab4cc8665c1c0329ea7fb22566abcfa1`. Each archive member is bound by `primary-cloud-archive-manifest.json`. `PRIMARY_IMPLEMENTATION.md` preserves the local commands/results; `PRIMARY_REVIEW.md` records independent spec and quality approval with no findings.

The original `FixedBlock`/`OriginalData` closure, actual-mode specialization and oldform spectral coefficient law remain separate obligations. This arithmetic gate does not make all of P3.4 complete.
