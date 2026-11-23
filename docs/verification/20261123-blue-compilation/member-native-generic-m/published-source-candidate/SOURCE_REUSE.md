# Published generic-M source reuse candidate

This package is **uncompiled**. It contains one new native extension and one
native consumer change consisting only of a prefixed import. No live source,
pin, build output, or frozen inventory was changed while preparing it.

The candidate extension is
`overlay/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.lean`.
It imports the existing cap100 `LiLiuPrereqBuchstabUniform` provider. It does not
replace any existing provider or alter a mathematical definition.

The consumer candidate is
`overlay/MathlibNt/Wu2008DoubleSieve/Omega3XBuchstabUniform.lean`.
Deleting its first import line returns the exact original 4333 bytes. Its
statements, proof text, local parameters, numerical constants, and quantifiers
are unchanged. Other project/native consumers are outside this overlay.

## Source authority and exact extraction

All 18 declarations, including every header and proof body, are contiguous,
byte-exact slices of three existing research source files at public commit
[`9d4c3a4010d42aedd9e7231bf94386019cfffccc`](https://github.com/subfish-zhou/goldbach-lean/tree/9d4c3a4010d42aedd9e7231bf94386019cfffccc).
The full source snapshots are in `upstream/research/wu2008/src/`.
`OVERLAY_MANIFEST.json` records each declaration's public commit, Git blob,
full-file SHA256, inclusive source line range, half-open source byte range,
candidate byte range, and separate declaration/header/proof-body SHA256s.

The 18 declarations comprise 11 public theorems and seven private theorems.
Six of those seven private theorems are existing helpers whose complete
declaration bytes also match the current old providers. The seventh is the
published new `abs_buchstabPrimeKernelSlope_le_coarse` proof. These are not
seven new private proofs plus another six helpers.

The public declarations are:

1. `abs_shift_mul_buchstabSlope_le_two`
2. `abs_buchstabPrimeKernelSlope_le_unrestricted`
3. `integrableOn_buchstabPrimeKernelSlope_unrestricted`
4. `buchstabPrimeKernel_sum_Ioc_error_le_unrestricted`
5. `buchstabPrimeKernel_sum_Ico_error_le_unrestricted`
6. `roughCount_buchstab_band_error_unrestricted`
7. `rpow_cutoff_bounds_fixed`
8. `roughCount_relative_band_error_fixed`
9. `roughCount_uniform_error_bound_fixed`
10. `tendsto_uniform_buchstab_majorant_fixed`
11. `roughCount_uniform_buchstab_fixed`

The old private helpers are `kernel_range`, `kernel_hasDerivAt_on_band`,
`kernel_endpoint_le`, `bands_pos`, `buchstab_main_decomposition`, and
`roughCount_base_band_error`. They are copied privately because their old
module-local aliases are unavailable from a new module.

The separately published `buchstabPrimeKernel_abel_unrestricted` is omitted:
the copied Ioc error proof directly uses the existing public
`prime_abel_log_error_le` and the copied derivative/integrability helpers. No
copied proof references that omitted theorem. The static verifier checks this
against the complete set of additions in the three published snapshots.

## Preserved producer boundary

The original `UniformAbel`, `Bands`, and `Uniform` files remain byte-exact.
Their old public declarations and definitions are imported unchanged; this
extension adds names without shadowing them. The published canonical compressed
copies are not used, because they remove old APIs.

The four existing external suppliers `LiLiuPrereqBuchstabPrimeSums`,
`LiLiuPrereqBuchstabBounds`, `LiLiuPrereqBuchstabIntegral`, and
`LiLiuPrereqBuchstabBaseEstimate` match the corresponding published research
files byte-for-byte. Their snapshots and exact live paths are listed in the
manifest. No overlay of those suppliers is needed.

Native base commit `09b97db5764ade1246bfb77206baa1b124760958`, Lean
`leanprover/lean4:v4.33.0-rc1`, and mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` are retained. The native and Member
toolchain/manifest files are also captured as unchanged boundaries.

## Interface and manuscript scope

The exact published theorem header is embedded in `actual_published_interface`
in the manifest. It chooses `M ≥ 2`, `u0 > 1`, and `epsilon > 0` before the real
threshold `X`; that `X` works for every `x ≥ X` and every `u ∈ [u0,M]`.
It proves positivity of the actual Buchstab main term and relative rough-count
error below epsilon. It keeps the unit, floor endpoint and strict small-prime
cutoff through the existing rough-count definitions.

The consumer chooses its compact domain from `k,delta` before `N` and every
source box/prime label. Its cap need not be at most 100. The extension supplies
the already-published arbitrary-fixed-cap implementation and does not add a
cap100 premise, alter the order of quantifiers, or infer a logarithmic rate.

Nov6 manuscript `sieve-appendix.tex:550–561` retains the actual switched rough
family with fixed positive exponents. Lines 775–792 retain the unit-surface
term separately and invoke the rough-number formula on fixed positive boxes.
This generic compact-domain uniformity supplies that scope. No final Wu
endpoint theorem or numerical conclusion is used in any copied proof.

## Prior acceptance evidence and limits

`evidence/PRIOR_PUBLISHED_SUPPLIER_PROVENANCE.json` and
`evidence/PUBLISHED_FOCUSED_PRODUCTION_BINDINGS.json` bind the full three
published research sources and unchanged original consumer to prior records.
The public source-manifest SHA256 is
`2079027dc274619f04f255a0dcaecc0410ea914a2af56994d1a979f916892455`;
the production-verification SHA256 is
`d13f60c24222fb0882fadd6ca289ca45eff8e62b2635ff53bd259fd02125494a`.
The compact acceptance validation and logs are copied into
`evidence/published-acceptance/` with their original bytes and hashes.

Those records report 4151 verified modules, 3500 promoted actual compilation
receipts, 651 unchanged receipts, and exit 0 for receipt verification,
literal/axiom acceptance, and the final theorem kernel replay. The final
verification itself did zero fresh source compilations. The final theorem's
reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Individual supplier receipt and object hashes are recorded, but their payloads
are not published in the inspected Git tree. This package reuses genuine
published source proofs; it does not claim reusable compiled objects or new
local compiler, per-interface axiom, or kernel acceptance. Moving existing
proofs to an extension changes the compiled module and requires guarded local
validation by the adoption owner.

## Adoption handoff

`OVERLAY_MANIFEST.json` is the complete install proposal, not an installer.
Before installation the owner should recheck every unchanged boundary and the
exact old consumer SHA. The new extension destination must be absent; the
consumer may only be replaced if its entire current source equals the recorded
baseline. Register both exact source overrides in a new provenance receipt;
do not alter frozen selected-source inventories or the original native pin.

Only the two `overlay` entries may be adopted. Keep existing build artifacts,
traces, hash sidecars, controller policy, and unrelated source bytes intact.
The extension is a new source node; the import-prefix consumer is a new source
postimage. Stock readiness, guarded compilation, kernel checks, and all-public
type/axiom audits belong to `build_workflow` in coordination with the Member
sole owner, using the already-authorized P6 12GiB slot in Member cwd. This
package never starts a source slot.

To repeat the permitted static identity/scope check:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 verify_static.py
```

`STATIC_VERIFICATION.json` records only those checks. It is explicitly marked
uncompiled and cannot substitute for the owner's Lean validation.
