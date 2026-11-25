# Historic Q80 sieve expression repair 01

Date: 2026-11-25. Status: source repair prepared; actual compilation pending.

## Actual evidence and manuscript scope

The failures are from P1 compact-03 job `job_a07d78e98e4e4a999137ad2e7ad046cc`, a completed 128-module diagnostic with stable inputs. The full log is `p1-compact-03.log`, 32,153 bytes, SHA-256 `dea260febb4dcd042829b24c3dd3d2b50ae3405b70e187cd0b5aa5f002b5b494`.

The frozen 1106 sources were read at `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- [numerical-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex), Directed arithmetic, lines 94–102: directed integer endpoints and guarded division. Enclosing delayed functions and integrals, lines 122–143: normalized numerator recurrences, rational mesh and conservative interpolation. Lines 145–164 describe weighted numerator chords, which are not substituted for the historical ordinary trapezoid here. Git blob `428e5fb4cd92b01b72119d795b8eeb01c67e3ccd`; exact retrieved bytes SHA-256 `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
- [certify_extended_prefix.py](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/verification/data/certify_extended_prefix.py), lines 7–16: normalized factor equations and the curvature rationale for errors `h^3/6`, `h^3/12` and `h^2/8`. Lines 59–76 retain the original two-layer integer floors/ceilings and their rounded error constants; lines 87–98 retain the original numerator interpolation. SHA-256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29` matches the Lean files' frozen producer binding.

The existing candidate index contains neither module name; no candidate audit was repeated.

## Classification and minimal changes

| Actual failure | Repair | Classification |
|---|---|---|
| Semantics lines 132, 137, 173: unnecessary sequence focus | Sequential `push_cast` then `ring` | Strict-linter expression compatibility |
| Lines 162, 168: `dsimp` made no progress; remaining denominator-exchange equality | Explicit `calc` using the existing bound, with the commutative field equality isolated under `unfold value; ring` | Formal expression normalization |
| Lines 229–231: integer denominators were not cast through multiplication and powers | Explicit `Int.cast_mul`, `Int.cast_pow`, `Int.cast_natCast`, `Int.cast_ofNat` simplification | Cast API compatibility |
| Lines 282, 284: `dsimp` after `convert` had no relevant definition left | State the shared distributive interpolation identity locally, then compose the already established inequalities | Elementary algebra made explicit |
| Lines 302, 304: `field_simp` made no progress | Use the existing `div_div_eq_mul_div` identity for division by `a/b` | Formal expression normalization |
| TrapezoidError line 20: import after a module-doc command | Move the same import before the module-doc | Module-header layout |

These fixes add no analytic premise, numerical constant or missing curvature argument. The local algebra was already the intended content of the old normalization tactics. No substantive manuscript gap is identified by these reported errors. The existing analytic trapezoid derivations are unchanged; the original parser failure did not establish that those bodies compile.

## Source identity and preserved interfaces

Input checkout HEAD when inspected: `5a91b30fef1b225d232a632ce671fad414a7dba4`.

| File | Before SHA-256 | After SHA-256 |
|---|---|---|
| `ImbalancedChen/P2HistoricSieveTableSemantics.lean` | `27fc0022aca73fd4687cbe01757ee5097142c8113da23cdabfe84fa80267a0aa` | `1c7aedc7101576908fc10097ea2cff00abfcdf2fa030a26f2f09fd55211a3a06` |
| `ImbalancedChen/P2HistoricSieveTrapezoidError.lean` | `c54b7b07e7f1b86edee813498e4a85bafe937843a497343be32c45b132545554` | `0dd1f5c93d4d1cfb6858d773c39b66e7912a27a519c499712178a5912de373fc` |

All 24 + 22 theorem headers and 23 + 3 complete `def` blocks are byte-identical. TrapezoidError differs solely by relocation of its existing import; all remaining bytes are preserved. All linter and elaborator options are unchanged. `git diff --check` passed.

No Lean/Lake command, kernel replay, cloud compilation or CI dispatch was run. These are uncompiled source repairs and receive no proof-acceptance credit.
