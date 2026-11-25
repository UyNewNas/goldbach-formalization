# Six classical interfaces: accepted fixed-source continuation

## Accepted result

**Exactly six owned modules and 85 complete environment inventory records have
passed the full formal gate, and their evidence has been retrieved and verified.**
The accepted source commit is `d1db3a39797ec5e6427bce3e62c42b67c98b1492`.
The source history and evidence were merged locally at
`4d1459cb2f13999e56fea462a4cc585e66df4779`.

Together with the three earlier, disjoint accepted groups, the current checkpoint
contains **24 owned modules and 388 complete inventory records**. Whole P3.6 is
still open: `whole_p36_closed = false` and `currentVerified = false`.

## Exact owned inventory

Every module below has the prefix `ImbalancedChen.`.

| Module | Explicit source declarations | Complete inventory | Definition-kind | Theorem-kind |
| --- | ---: | ---: | ---: | ---: |
| `P5OriginalU5ScalarSmoothCutoffs` | 12 | 13 | 3 | 10 |
| `P5OriginalU5LogCollarBasic` | 17 | 27 | 5 | 22 |
| `P5OriginalU5NarrowSingletonBasic` | 11 | 13 | 6 | 7 |
| `P5WordKernelSignedRow` | 1 | 1 | 0 | 1 |
| `P1SharpPrimeEndpointDefinitions` | 4 | 6 | 4 | 2 |
| `P2OriginalU5PlateauRectangle` | 13 | 25 | 6 | 19 |
| **Total** | **58** | **85** | **24** | **61** |

The 58 explicit declarations comprise 34 `theorem`, 22 `def`, and two `abbrev`.
The complete inventory additionally contains seven `.eq_1` equation theorems
and 20 `._proof_*` auxiliary proofs. The sharp endpoint source has four
definition-like declarations and no explicit theorem; its two theorem-kind
inventory entries are `cut._proof_1` and `cut._proof_2`.
[The complete name-by-name comparison](DECLARATION_COUNT_REVIEW.json) records
this distinction.

## Mathematical scope

The scalar cutoffs have the original smoothness and range properties. The
log-collar interface supplies the original singleton profile, support, widths
and rank-one licence. The narrow singleton interface supplies an exact
same-coefficient decomposition into smooth error, lower reserve and upper
reserve. That identity does not estimate all three terms.

`wordKernel_eq_signedRow` retains arbitrary finite `Q`, complex `rho`, `N`,
and the complete product `ps.prod`. The sharp endpoint module supplies its
original definitions. The plateau rectangle retains the original prime pair
carrier and proves `rootQ N t = N^(90621/160000)` for the stated rectangle and
`N >= 2`.

The rectangle result does not establish coverage of the whole pair support
or a common physical finite modulus set. The six interfaces do not close
filtered-complement payment, quantitative positive signed harmonic mass,
full higher-rank U5/WT admission, complete three-factor `(S)/(F)` licences,
or the same-rho PP conclusion. `P3OriginalU5SelectedClassicalComplement`, the
actual count consumer, is outside this owned group.
[MATHEMATICAL_SCOPE.md](MATHEMATICAL_SCOPE.md) gives the precise quantifiers
and retained suppliers. The next signed-density interface and epsilon-first
budget order are recorded in [NEXT_DENSITY_BOUNDARY.json](../NEXT_DENSITY_BOUNDARY.json)
as an unformalized composition plan, with no additional formal credit.

## Formal execution and complete evidence

P1 task `job_8ce130db9e6645f7a027d0593ea8afcc` completed successfully in
916.294 seconds. All 37 recorded commands returned zero, including six fresh
strict compilations with `warningAsError=true`, six exact independent
`leanchecker --verbose` replays, and the original complete defining-module,
full-type, serialized-constant and transitive-axiom audit. The actual axiom
set is exactly `Classical.choice`, `Quot.sound`, and `propext`.

The unchanged runner is bound by SHA256
`be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709`.
The classical wrapper remains
`daa613d1e1afba572980467142c50358bda8f9899720227b42cb0b46758c32f1`.
The compiler is Lean 4.33.0-rc1, with the original binary, package pins,
import paths, dependency signatures and snapshots bound by the receipt.

Five successful exports were recovered through 173 byte-offset pages.
The frozen local verifier checked all 438 archive payloads, 377 selected
project sources, 407 fixed/current project inputs, 10,125 recursive graph
signatures, 371 reused-node lineage records and 37,857 snapshot bindings.
There are no external cache mirrors or native aliases in this run.

- [RECEIPT.json](../accepted-classical-six/RECEIPT.json): 161,678 bytes;
  SHA256 `028389ac1dd2c12f791cccdebb554fa881c5af4644c6bc57b5961f7290179fcc`.
- [evidence.tar.xz](../accepted-classical-six/evidence.tar.xz): 4,055,128 bytes;
  SHA256 `07d4dd1f76dc8f05f2e7af4048cffa161f191f072edc62911e02deb166a73b0e`.
- [LOCAL_VERIFICATION.json](../accepted-classical-six/LOCAL_VERIFICATION.json):
  SHA256 `0b1e77e928351efec1eaf3ba3ecb6a4bf283f7e71ffafb963e8de75031a70026`.

Owned object bytes and recorded dependency lineage are archived. Other
dependency bytes are hash-bound by the original runner snapshots. Local
recovery verifies archived evidence and current project bytes; it does not
run Lean again or inspect later remote dependency state.

## Source preservation and integration

The initial fixed-donor restoration supplied 126 absent files within the
377-source closure. Twenty subsequent compilation adaptations are recorded
in [COMPILATION_ADAPTATIONS.json](COMPILATION_ADAPTATIONS.json), with original
failures and actual isolated probes retained under `attempts/`. The status
strings in that manifest describe the repair-stage checkpoint; the final
acceptance is established by the receipt above.

The repairs preserve original signed coefficients, beta factors, full
residual universes, complete products, external pairs and same `Q/rho`.
Recorded lexical repairs apply to previously unelaborated source; no old
accepted type is asserted for those failing headers. No imports, global
options or heartbeat limits were changed by these repairs.

The 211 sources shared with the warm selection retain their exact hashes.
After the merge, all 291 warm-selected files and the three earlier evidence
groups remain unchanged. All 24 owned sources match their original receipts,
and all 407 classical receipt-bound project inputs match the merged tree.
The exact verified source commit remains an ancestor of the integrated branch.
See [FINAL_SOURCE_REVIEW.json](FINAL_SOURCE_REVIEW.json),
[SOURCE_INTEGRATION.json](SOURCE_INTEGRATION.json), and the consolidated
[OWNED_SCOPE_STATUS.json](../OWNED_SCOPE_STATUS.json).
