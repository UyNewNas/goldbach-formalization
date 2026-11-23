# Exact reuse of the published P1 near-one candidate

Status: **UNCOMPILED LOCALLY BY THIS AGENT**. No Lean, Lake, compiler, kernel,
type or axiom probe was run. No live Member/main/native/P6/frozen source or
build output was changed. Candidate source was copied exactly from published
Git code, rather than reimplemented.

The candidate is `candidate/ImbalancedChen/P1FourthNearOneKernel.lean`, SHA256
`8d172a73d7f93826ff00693dcb423239265e97beebb9a77049e1f2cde8720835`, 11818 bytes.
Its Member preimage is SHA256
`046fbb5257e9a4bbe0d7bd075da054b6dfe2a2e572fa777b13684a29d61a1f83`.
The published candidate manifest explicitly binds exactly that preimage.

Source authority:

* Repository: `UyNewNas/goldbach-formalization`.
* Commit: `c1eb228f281d93e03a6fc231e0086baa9f589036`.
* Path: `verification/parts/p0/p1-near-one-api/candidate.lean`.
* Same exact candidate at prior successful CI head
  `9f080cf1f7691b7cd498f5912fcead17f3f47107`.
* The endpoint-instantiation correction was published in ancestor
  `c0a48ccb9000d54a6e6616b5f8067d2a342403fa`.

`STATIC_RECEIPT.json` records the full source blob/hash authority, original
published manifest, declarations, and source relationships. The canonical
main source is a different earlier version, SHA256
`83fc7aa451aa3a40d9112f511b3d869045117a79eb7d4ba3f6c6626d96c1f19d`.
It has the same 32 declaration headers and definition bodies, but different
proof text. P6 has no canonical file. The candidate is based on the actual
Member v3 source, not a wholesale copy of the older canonical main file.

## Exact existing corrections

1. Replace the nonexistent fully qualified name
   `MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer_one_two_odd_nonneg`
   with the existing
   `MathlibNt.SieveTheory.suzukiLayer_one_two_odd_nonneg`.
   Its actual provider is
   `MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiProposition118SourceSeriesPairing.lean:42`:
   given `1 < s`, every actual odd source layer is nonnegative. The existing
   `s > 2` branch discharges its unchanged hypothesis. Neither the source
   series nor its natural rank/parity is replaced.
2. Replace the ambiguous rewrite by
   `upper_eq_inv (s := (2 : ℝ)) (by norm_num) (by norm_num)`.
   The pinned local API is `upper_eq_inv {s : ℝ} (1 < s) (s ≤ 3)`.
   In `upper s ≤ upper 2`, the uninstantiated rewrite incorrectly matches the
   left side and demands `s ≤ 3`. Explicitly instantiating the existing right
   endpoint rewrites only `upper 2`. No global restriction on `s` is added.

All 26 public theorem headers and six definition chunks are byte-identical
between actual Member preimage and candidate. A balanced parenthesis-depth
scanner finds theorem-level assignments; named argument `:=` in the copied
proof is not treated as a declaration boundary. Imports, all statement and
definition numerals, hypotheses and bounds are unchanged. The proof adds one
explicit occurrence of the already-existing endpoint numeral `2` solely to
resolve rewrite instantiation; it changes no numeric parameter.

This repairs namespace/API selection. No mathematical gap or public-header
exception was found. In particular, actual-source identities still require
strict `s > 1`; the file does not assert equality of the totalized source at
`s = 1`. `closedUpper`, all residual/normalized/density definitions, the legal
domain, the max-one extension, `A`, and the normalized bound `4/a` remain exact.

## Nov6 manuscript scope

`sieve-appendix.tex:220–251` describes literal Rosser densities uniformly on
compact legal parameter ranges, with upper source parameter strictly greater
than one, and gives the initial strip `F(s)=2 exp(gamma)/s` for `1<s≤3`.
`introduction.tex:259–268` fixes that same standard upper sieve normalization.
The candidate retains the right endpoint extension needed for compact-box
integration while making no assertion that the original totalized series at
one equals the right limit. Its geometric/analytic kernel statements do not
add a discrete residual mean or replace the manuscript family.

## Prior CI evidence and closure caveat

A fresh read-only GitHub metadata query reported run
[`43976090750`](https://github.com/UyNewNas/goldbach-formalization/actions/runs/43976090750)
completed successfully at `9f080cf1…`. The already-held artifact metadata lists
`p1-near-one-api-43976090750` (ID `14283627116`, 3105182 bytes). No artifact or
compiled object was downloaded. Workflow success metadata alone is not a
locally examined compiler/kernel/type/axiom receipt and is not claimed as new
local acceptance.

That published workflow also adds the canonical
`Mathlib.MeasureTheory.Integral.Pi` owner import to `FinitePiIntegral`, mapping
source SHA `22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c`
to `2e4fe57169a1a1e71b354008c0ad2639b52e7170a5e0e5129992437cc0931938`.
It addresses the owner of generated `Fin.insertNthEquiv.eq_1`.
Current Member `FinitePiIntegral` still has the original `22c7…` source.
Therefore the old complete 32-module CI closure is not assumed identical to
the current closure. The extra module was not edited by this task; the sole
owner should handle it only if its actual canonical owner/kernel audit needs
that already-published import correction.

The existing candidate source is ready for the sole owner to adopt under the
current pinned Lean4.33rc1/mathlibe4c9/native09b guard and validate. Original
failure excerpts and original published manifest remain separate evidence.
