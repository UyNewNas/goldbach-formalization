# T02 — exact ClassGhost proof-expression source review

**ALLOW_SOURCE_ONLY** for the exact 5,868-byte candidate SHA `6538fc8ba71dbbd7d66e81fcaecb8c3ac438b0d8485ac46f5249f9813b8b81d6`, Git blob `a5e3b7343d17293342da7a012362a61189898b81`. This independently reviewed source is eligible for ROOT's source-only archival/publication process. It is uncompiled: no kernel, runtime generated inventory, object reuse, driver or CI permission is conveyed.

Author input is `t01/weil34-classghost-api/FREEZE.json`, SHA `d4dd7f480bcf0bbf46bfa7e6ae8c25772e7863f024c170c3bf9e33ed2c23da14`. All 19 bound files and the exact 20-file directory census passed independent size/SHA/Git-blob checks. Forty source/byte/input checks passed. No candidate, proof helper, Lean/Lake/LSP, fixture or setup was executed; no artifact or reference was downloaded by this reviewer. Existing approved runtime checks were reused, not rerun.

## Exact change and original failure

Preimage is source commit `26c8c3ab7017ff27aafb60b5e26f3183f2ed8b7a`, path `docs/source-only/20261115-resume/t01/weil34-failure-review/compat-candidate/LeanPool/KloostermanWeil/Carlitz/ClassGhost.lean`, 5,819 bytes, SHA `d4caea55f0ff8c76b1c1c99d7c5db09eb6e605d380c938d07623e70f44f31321`, blob `fb4a6be77d517da09032959fd9f7814a73ee7d8d`. It equals the actual-source bytes frozen by T02 for run `43657752592` at head `2960e200301de4189c1c2793b918fc8aa7666930`.

The sole change replaces the two-line local call to the unavailable `Module.finrank_div_finrank_cancel_left` at original line 97 with:

```lean
    Nat.div_eq_of_eq_mul_right
      (Nat.pos_of_ne_zero hbase0)
      (Module.finrank_mul_finrank (Fp p) M (Ext p n)).symm
```

Exact forward substitution reconstructs the candidate and exact reverse substitution reconstructs the full preimage. The author patch independently regenerates byte-for-byte (SHA `db2b675b1ffb4669f6b9111ecfd7b7c3b23265c411ac37a8af88cbffdcd7d7a4`). All imports, module/public section/namespace, license and attribution, five explicit declaration heads and every other byte are unchanged. The five explicit source declarations are `conjCarrier_card_eq_minpoly_natDegree`, `minpoly_eq_class_minpoly`, `relative_finrank_eq_total_div_classDegree`, `classGhost`, and `Kext_eq_classGhost`. This is not a census of elaborated private/generated declarations.

The actual raw diagnostic was unknown-constant resolution at this occurrence and its resulting unsolved finrank quotient goal. The earlier independent all-34 scan found the missing complete token exactly once. This patch targets that precise cause; it does not infer that all remaining 18 modules will compile.

## Old API, orientation and conditions

Fixed Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, `Mathlib/LinearAlgebra/Dimension/Free.lean:68`, publicly declares:

```lean
theorem Module.finrank_mul_finrank : finrank F K * finrank K A = finrank F A
```

Its full existing context at lines 35–38 is `Semiring F/K`, `AddCommMonoid A`, the three modules `F K`, `K A`, `F A`, `IsScalarTower F K A`, `StrongRankCondition F/K`, and `Module.Free F K` / `Module.Free K A`. With F=`Fp p`, K=`M`, A=`Ext p n`, these are the standard vector-space/scalar-tower structures over the existing base field and its intermediate field. `Fp p` is the original `ZMod p` with `[Fact p.Prime]`; `Ext p n` is the original Galois field, and M is the existing `IntermediateField.adjoin`. The patch does not introduce any new structure, finite-dimensional condition, witness or assumption. The old and upstream convenience-lemma sections have the same complete context bytes.

Fixed Lean `62eed1db4d67327ec8120be05f1a1b0847d74561`, `src/Init/Data/Nat/Div/Basic.lean:450`, in public `namespace Nat`, declares:

```lean
protected theorem div_eq_of_eq_mul_right (H1 : 0 < n) (H2 : m = n * k) : m / n = k
```

Put `d = Module.finrank (Fp p) M`, `r = Module.finrank M (Ext p n)`, and `N = Module.finrank (Fp p) (Ext p n)`. The tower theorem gives `d * r = N`; `.symm` supplies exactly `N = d * r`. The existing `hbase0 : d ≠ 0` gives `0 < d` via `Nat.pos_of_ne_zero`, an API also already used in the same fixed Nat source. The resulting local term has precisely `N / d = r`, so the untouched `hcancel.symm` proves `r = N / d`. The untouched `rw [htotal, hbase]` then gives the original `n / c.minpoly.natDegree` target. No multiplication commutation or extra divisibility hypothesis is needed.

Existing `hyint`, `hbase`, `htotal`, `hdegpos`, `hbase0`, prime assumption, `[NeZero n]`, class membership and final calc are unchanged. In particular, positivity is proved from the original nonzero rank, not newly assumed. No sqrt-p normalization, theorem parameter, classGhost definition or downstream target is weakened.

The newer `56a005855ea17e0b0958f73ec801ae140b0a1679` convenience lemma at Free.lean:85–87 itself uses `Nat.div_eq_of_eq_mul_right h.bot_lt (finrank_mul_finrank ..).symm`. This comparison supports the diagnosis that the missing name packaged an already available proof. No newer dependency is loaded; no generic tower theorem, axiom, `sorry`, `admit`, unsafe declaration, private bypass or backport module is added. Original Apache-2.0 header/attribution is retained, and the full reference files retain their own provenance/license headers.

## Connection to actual project-4.33 scope

R3 raw `WEIL_STANDARD_INPUTS.json` SHA `9f1547de8950971dff270a3296d3671b9c0ab085bba372bb38786d50577a5979` and ClassGhost direct-input SHA `47c37e185e511ae318800c154495887220db9ddefe34b4432193c64fa36d2a9c` independently bind both referenced fixed source files and their complete public/server/private/IR identities. Old Free source SHA is `e2fbc9efb856428648d2f0bc94a66d94ecd4e9a3559ef1686fe61a9fe36f3f4a`, and old Nat Div Basic SHA is `67f894497257111dff81a5b3bab0f849cc53f31a3c62656333366ad62ab63a58`; both equal the actual original input identities, not merely author-labeled downloads.

The public, non-meta path already present in the original header graph is:

`Separable → PowerBasis → Minpoly.Field → Algebraic.Integral → Dimension.Localization → Dimension.DivisionRing → Dimension.Finite → Dimension.Constructions → Dimension.Free`.

Every edge was independently checked against the original standard source-header closure. Nat Div Basic is reachable through the existing prelude/public route `Separable → Init → Init.System → Init.System.Platform → Init.Data.Nat.Div.Basic`. Both modules are present in actual setup importArts; source plus all five modern facets are prebound. Thus no extra import or hidden/private/meta exposure is being used to make this proof expression available. The declaration names are public, and the proof consumes their public theorem signatures.

The author's bounded dedup record found no reliable existing repair in the checked local source/content and remote branch-name scope. This review relies on it only as a bounded work-duplication check; it does not assert global novelty or perform new remote searches.

## Authority and remaining work

This source-only AL connects the single candidate delta to the existing 34-module scope, leaving the other 33 source identities unchanged. It does not approve a new scope manifest, workflow, 15-protected/19-fresh consumer, or objects. Source publication must use the distinct candidate identity and preserve the 26c8 preimage; it must not relabel the new bytes as the old commit.

The prior 1-protected/14-success/1-failed/18-unstarted runtime census is unchanged. All 14 successful producer objects should be preserved before any future reuse design; no source recompile is authorized here. Full fresh 34-module kernel, two complete typed/generated/private inventories, AX and raw safe closure, actual loaded parts/owner checks and all F1–F7 remain mandatory under project 4.33 / original 487B profile/pins. Six bridge targets and whole J remain HOLD. Neither the upstream comparison nor this exact proof composition is a compile/kernel result.

The original R3 runtime report's 11 frozen files were rehashed and remain unchanged. Later terminal or retention metadata belongs in a separate addendum; none is written into that old review or used here to claim physical reuse qualification.
