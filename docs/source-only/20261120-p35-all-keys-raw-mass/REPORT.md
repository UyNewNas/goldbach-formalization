# P3.5: original two-chart raw mass across all primary keys

## Baseline and source

Branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`59bf7ddb9b4055763730785ead1489393bbcf04a`. The commit containing this
report is the new continuation SHA. The packet contains
`Part3OriginalAllKeysRawMass.lean`, SHA-256
`193eac582a9c0d9c57887123fc9f195652f7d3b572738ccb7eaf1c0632980724`,
and this report. No other files are changed.

## Exact manuscript-side deduction and candidate proof bodies

For the original data D and completion mark r, let S be `originalSource D`,
let S* be `nonzeroSource S`, and let O be the image of S* under the actual
joint output map. Put

    E = sum_{zy in O} |jointBeta D r S* zy|^2.

For each actual primary/sign/dyadic key k, the block is a subset of S*,
so its output carrier is contained in O; its block beta vanishes outside
that carrier. The existing `finite_beta_energy_assembly` partitions by
the output key, which depends only on the joint output. Therefore

    sum_{k in originalKeys D} actualOutputMass D r k = E.

The prior exact two-chart row identity gives the stronger presentation

    sum_k (sum_{z in levels D k false} rowMass D r k z
           + sum_{z in levels D k true} rowMass D r k z) = E.

These are finite identities with empty carriers allowed. They introduce
neither a factor for the two charts nor a key multiplicity. Multiplicity
of sources with the same joint output remains inside beta. The actual
coefficients still depend on r and on the level z; no common n sequence
is manufactured. The two charts retain their strict/non-strict dividing
boundary and original level sets through the imported identity.

The candidate `weighted_key_mass_le` also supplies the finite consequence
for actual key weights w and scalar B: if every actual key has w(k)<=B,
then sum_k w(k) actualOutputMass(k)<=B E. It does not need a nonnegative
w because each mass is nonnegative. The explicit application
`weighted_all_keys_rawN_le` takes nonnegative w and asks only the stated
pointwise scalar bound on

    w(k) * 2*sieveConstant*(1 + |a|*nu*rowLength(k)/fixedZ(false)).

Finally `all_keys_two_chart_raw_cost_le` uses, for each key, the maximum
of the two *actual* squared J-dependent chart weights. For arbitrary
key-indexed B0, omega0, B1, omega1, the sum of the two original raw chart
costs is at most B E if their maximum times the above raw factor is <=B
for each occupied key. The phases remain separately indexed by key and
physical chart, and are not indexed by r or the Poisson sign. This is a
conditional scalar cost assembly: it does not establish that scalar
bound, choose phases, provide a J estimate, or bound the full block.
In particular it does not imply the 7/32 target or identify fixed-level
estimates with a cross-level spectral large sieve.

The imported oldform/post-removal estimate, strict exceptional range,
regular/holomorphic complement, continuous part and gap-dependent
denominators remain exactly as before. No additional spectral statement
is made. Both zero-frequency lanes, actual truncation tails, 14 eta and
28 eta weights, 128 C enlargement and threshold order are untouched;
this packet proves none of their remaining payment obligations.

## Sources and input boundaries

The full immediate predecessor is `docs/source-only/20261120-p35-two-chart-raw-mass/REPORT.md`
and `Part3OriginalTwoChartRawMass.lean`, blobs
`5eb18488664717f545d2633fa93a178f8cd39372` and
`19eac174ff242cc0c1f97e3e96d484ff009c2d98`. The complete actual key
assembly source `ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean`,
blob `3a12da5b72eeddd3558c4714eecd7754cd660a55`, supplies
`block_subset` and the exact beta-energy identity. The complete primary
rows source `Part3OriginalPrimaryPacketRows.lean`, blob
`4281ec328d4c3a0f4cb9ca21c2f0923604e6e47a`, defines the original keys,
block, carrier and beta. The original reciprocal source is blob
`a99ba7e76f13c45beac5bd459334c9a75dc7c5a7`. The original raw cost
source is blob `779f7d38325d249390e8c812c1918a93db063c1d`.

Manuscript body `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
was verified as blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching
the existing chain pin. Distribution source blob
`19f9672bc9b6d455045213c5e23e10433a9569d2` remains the registered
§10(vii) call source. This packet adds no external theorem or revised
normalization. Pascadi v3, ABL v1, the fixed-level sieve, regular sieve
and gap input retain the source versions, exact scope and verification
status recorded in the predecessor reports. In particular initial AvgJ
is not extended to the manuscript's full X range, and raw n costs are
not replaced by an unproved oldform-removal bound.

## Validation and remaining work

`SOURCE_ONLY`: yes; `COMPILED`: no; `KERNEL_REPLAYED`: no;
transitive axiom check: not performed; independent review: not performed;
`UNEVALUATED`: yes, including imported candidates. The exact import
closure has not been staged. `command -v lean` and `command -v lake`
each returned exit 1 and no output. No Lean/Lake compiler ran: no
compiler exit code or compiler log exists. Configured pins from the
handoff are Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot
be verified. Stack 8192 KiB, virtual memory unlimited; neither changed.
`sha256sum Part3OriginalAllKeysRawMass.lean` exited 0 with the hash above.
`rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'` on this file
exited 1 with no matches. That source scan is not compilation or an
axiom audit. No CI was started.

Next stage the exact dependency closure under the pinned environment and
elaborate/replay the candidate; verify the reduction of beta and the
finite sum specialization. Bound the actual J-dependent per-key scalar
prices on the actual level ranges, or replace the raw n price by a
properly sourced and normalized oldform-removal estimate. Supply the
strict exceptional/gap denominators and regular/holomorphic/continuous
estimates, perform the remaining manuscript integral and reserve
payments, and only then combine both zero lanes, true tails, 14 eta/28
eta weights and the 128 C enlargement with the original threshold order.
