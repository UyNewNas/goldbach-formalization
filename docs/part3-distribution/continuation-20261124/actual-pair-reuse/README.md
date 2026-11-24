# Actual smooth pair: reuse provenance and compatibility

The fixed donor sources and the new adapter have been integrated into the
continuation branch. The compatibility Core and new adapter await their
`actual-pair` strict/kernel/full-inventory gate. Existing accepted proof
sources and the old Attachment remain unchanged. The copied source manifest
records the original isolated staging checks; it is provenance, not a
compilation receipt for this integration.

## Fixed donor

- Repository: `UyNewNas/goldbach-formalization`.
- Commit: `10b89181754c78c0e77616677295ee2105de0bb6`.
- Root: `ImbalancedChen.P4BSmoothPrimeVariableProfile`.
- Root source SHA256:
  `ca93e79e4022b473e0b2ce90e766b14d84eec76e15ba4b2eb79d32c34d0deca5`.
- Existing acceptance:
  `docs/verification/20261123-blue-compilation/member-repair-batch86/VALIDATION_RESULTS.json`.
- Existing final release:
  `docs/verification/20261123-blue-compilation/member-repair-batch86/FINAL_RELEASE.json`.

The donor acceptance records normal compilation, kernel replay, and complete
owned declaration type/axiom auditing for the exact root source above. It is
evidence for that donor context, not acceptance of this changed import context
or the new adapter. `SOURCE_MANIFEST.json` binds all staged source hashes and
the fixed donor receipt hashes.

## Source reuse and compatibility

The fixed donor root has a 94-module project import closure. The canonical P3
checkout already contains 74 byte-identical modules. This staging area supplies
the missing 19 modules. Eighteen are copied byte for byte from the fixed donor.

The remaining module, `FiniteUpperCarrierCore`, retains every existing finite
identity declaration and proof verbatim. Its two definitions
`actualSmallRoughModuli` and `actualSmallRoughRho` already occur byte for byte in
the canonical P3 `ActualSmallRoughAttachment`. Only those duplicate definitions
and their doc comments are removed from the staged Core; it imports the
unchanged canonical Attachment instead. The three original Core imports remain.

The selected project import graph is acyclic, remains the same 94-module set,
and declares each of these two names exactly once. The canonical Attachment
and every other existing dependency remain unchanged. No P1 working-tree source
is used as a donor.

## New adapter

`ImbalancedChen/Part3ProperPowerActualPair.lean` has two direct imports:

```lean
import ImbalancedChen.Part3ProperPowerChartSum
import ImbalancedChen.P4BSmoothPrimeVariableProfile
```

The weight is the literal
`smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width`.
With fixed `b > 0`, `a > 0`, `width > 0`, and
`2 * width ≤ baseline b κ - a`, the adapter uses the existing continuous
positive-coordinate profile support to prove its effective integer-source
geometry. A nonzero normalized von Mangoldt coefficient supplies coordinate
positivity even when the tuple contains proper prime powers. The existing
global weight bounds give amplitude one.

The ChartSum parameters are `k = 2`, `P = N`, `M = 1`, `m = 0`, `c = 1`,
and `C = Real.exp width`. The eventual threshold precedes `B`, `Q`, `ρ`, and
`χ`. The two resulting logarithmic-accuracy theorems cover the full
proper-power residual and the exact prime-minus-von-Mangoldt discrepancy.

The actual signed `ρ`, exact coprime mean, and full-product diagonal remain
unchanged. The physical modulus cap `q ≤ K * N ^ θ`, `0 ≤ θ < 1`, and fixed
divisor-order bound on `ρ` remain explicit inputs. No `policy8` replacement is
made. The existing original-cutoff plateau and range conditions are retained;
no cutoff construction or analysis is repeated.

## Remaining acceptance and scope

The changed Core and new adapter are selected together by
`verification/verify_part3_continuation.py --group actual-pair` for strict
compilation, kernel replay and the original complete serialized declaration
inventory/transitive-axiom acceptance. The source manifest hashes are checked
for every reused file, and all original package/configuration pins remain. The eighteen byte-identical donor
modules keep their existing proof sources and donor provenance.

This adapter closes the weight geometry and amplitude inputs for this actual
rank-two source. It does not prove the manuscript's spectral estimate, select
an actual modulus policy, construct lower or marked smooth source families,
or complete the whole P3 theorem.

## Retained donor evidence

The original [validation record](donor-VALIDATION_RESULTS.json) and
[final release](donor-FINAL_RELEASE.json) are copied byte-for-byte from the
fixed donor commit. Their mutual hash binding and the profile's
[normal](donor-P4BSmoothPrimeVariableProfile-normal.log) and
[kernel](donor-P4BSmoothPrimeVariableProfile-kernel.log) log hashes were
checked. The full original type/axiom log remains at the fixed donor's
[batch86 evidence](https://github.com/UyNewNas/goldbach-formalization/tree/10b89181754c78c0e77616677295ee2105de0bb6/docs/verification/20261123-blue-compilation/member-repair-batch86).
Only the new adapter and changed compatibility module are being re-audited;
necessary dependency builds do not constitute new mathematics.
