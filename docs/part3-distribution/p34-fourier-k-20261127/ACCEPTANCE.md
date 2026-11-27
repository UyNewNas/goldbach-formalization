# P3.4 initial-half-plane Fourier–K checkpoint

This checkpoint verifies the existing normal-convergence, real canonical
Fourier and complex canonical Fourier suppliers. It continues PR #8 from
`6a91582b56814dd0133a7e36094efabb2f6dcecd`; full P3.4 remains incomplete.
The precise accepted source commit and hashes are in `SOURCE_BINDINGS.json`.

## Mathematical result

For positive height and arbitrary integer frequency, the actual primitive
Fourier integral equals its canonical Gamma/zeta/divisor/K expression on
`Re(s)>1`. The primitive index, half normalization, interval `0..1`, negative
phase and nonzero coefficient factor `2` are preserved. The prefactor-free
bilateral K series has uniform summable majorants on closed real-part strips
and is entire in the parameter. This does not assert entire dependence of
the meromorphic Gamma/zeta prefactor.

The three targets have 55 existing explicit declarations (42 theorems,
13 definitions) and 72 compiler records (59 theorems, 13 definitions).
No explicit production mathematical declaration or premise was added.
Thirty-one existing source files received proof/API/elaboration repairs;
the complete source delta and final compiler types disclose those repairs.
See `SOURCE_SCOPE.md` for details and the distinction from compiled equality
to originally ill-typed expressions.

## Final verification

The final `verification-r3` receipt reports **PASSED**:

| Check | Actual result |
| --- | --- |
| Verification stages | 238 / 238, exit code zero |
| Project source/object closure | 105 modules, authenticated successful build receipts |
| Warning policy | 59 Part3/P0Ramanujan modules strict; 46 untouched general dependencies normal |
| Current kernel replays | 105 / 105 |
| Interface checks | Earlier analytic endpoints plus Fourier–K endpoints, including expanded nonzero formula |
| Python regression suite | 31 tests passed |
| Owner-based inventory | 2,537 records: 2,078 theorems, 447 definitions, 4 inductives, 4 constructors, 4 recursors |
| Transitive axiom union | `Classical.choice`, `Quot.sound`, `propext` |
| Bound verifier/config inputs | 9, unchanged after validation |
| Observed direct external object parts | 385, unchanged after replay |
| Toolchain binaries | 5, unchanged after replay |

Lean is exactly `4.33.0-rc1` (commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`). Mathlib is
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, with its eight locked
transitive dependencies; goldbach and LeanArchitect revisions are recorded
in the report. Package working trees were checked clean. No dependency update
was performed. External Lean/Mathlib/package objects use normal imported
environment trust; this is project kernel replay, not full external-library
source replay.

An independent source/math review and the addressed findings are recorded in
`REVIEW.md`. Earlier repair attempts and expected regression/setup failures
remain diagnostic history; they are not passing stages of this receipt.

## Reproduction and evidence

Run `python3 -B verification/verify_p34_fourier_k.py --output <fresh-directory>`
in the recorded native environment. It selects the pinned toolchain, builds
or authenticates matching successful receipts, performs the endpoint/audit
checks and replays all project objects. Absolute dependency paths are recorded
in the builder and report.

`evidence.zip` contains the verified 105 project source files, verification
inputs, full final reports/types, successful object receipts, build history,
diagnostics and source bindings. `ARCHIVE.json` records its byte length,
SHA-256 and payload count. Every payload member is hashed and read back after
ZIP CRC validation. Binary library objects are identified by hash rather than
included as payloads.

## Unfinished boundary

This receipt does not close critical-line continuation, all-level Gamma0
automorphy, R22, Fricke/Whittaker amplitude attachment, DI normalization,
ABL dilation or continuous Plancherel normalization. The next all-level
source closure contains 133 project modules; it is outside this 105-module
acceptance. The PR remains a draft and is not merged by this checkpoint.
