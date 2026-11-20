# Independent review: WindowGate namespace delta

Decision: **PASS the exact source-level namespace-resolution delta only.** The reviewed postimage is `authorpost/Part3MediumPrimitiveShiuWindowGate.lean` in the N08 author package, 11898 bytes, SHA256 `6d47a7fb9a91a67ba330cd6ca519964b03cb81e2da5d358d14e50b010ebe3892`. It is bound to author freeze `1fd745adde4504bfc2ecd7c441593bd0cd4350acc9dd8c7cee5c80d66ec9ab93` and the unchanged FiniteCover provider `7bdcfdbbff4382da1ee4ba16ba9296b8995ceb11a43f78cf70af21f852549d39`.

This is an independent review of N08's new postimage. It does not re-sign the old mathematical proofs, approve a Lean environment, or modify the original 565b source/selection/HOLD. Compilation, elaboration, kernel, full Native6 closure and green status remain unaccepted.

## Exact change and identity

All six files listed by the author freeze match their recorded bytes/SHA256. Independently reconstructing the postimage from the original 11839 bytes gives exact byte equality: at zero-based byte 619, insert only the 59-byte LF-terminated line

```lean
open ImbalancedChen.Part3.MediumPrimitiveShiuCover20261028
```

Removing those same 59 bytes reconstructs the original raw source exactly. Nothing is deleted or replaced. The insertion is new line 16, after the existing opens and before every declaration. All three imports, all nine declaration heads, all structure fields and all proof bodies retain their original bytes. The corresponding old lines after the insertion shift by exactly one. This is stronger than a whitespace-normalized comparison.

The preimage equals both original draft and frozen 565b aliases. The chosen provider remains the exact 13577-byte 7bd source named by the original phase9 dependency guard; no newer cover version is substituted. Both source commits remain null in this local source review.

## Name resolution and bounded shadowing check

The original caller is in `ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028`; the imported provider defines the intended objects in sibling `ImbalancedChen.Part3.MediumPrimitiveShiuCover20261028`. The new fully qualified open is in scope for all original caller declarations and exposes precisely that existing namespace. It does not add an import, notation, instance, definition, premise or theorem.

The nine provider names actually present as code identifiers in the comment-stripped caller are:

| Name | Provider line | Meaning retained |
| --- | ---: | --- |
| `shellBase` | 17 | Natural dyadic base `2^j`. |
| `windowLength` | 19 | Original natural `min T (shellStep j)`. |
| `windowStart` | 21 | Same short translated/max branch and shell-step branch. |
| `window` | 25 | Same half-open finite interval. |
| `windowLength_pos` | 56 | Original `0<T` premise. |
| `windowLength_le_start` | 61 | Original length/start inequality with `0<T`. |
| `shellBase_le_windowStart` | 72 | Same natural lower bound. |
| `windowStart_le_eight_B` | 224 | Same A/B order, nonzero B, shell and k-range hypotheses. |
| `active_window_length_lower` | 248 | Same R/16, source-point and shell hypotheses. |

Each full provider name and every caller pre/post occurrence line were independently recomputed and match N08's mapping. The exact provider has 28 top-level declarations; the caller has nine. Their declaration-name intersection is empty. The other 19 provider names do not occur as caller code identifiers, so this file has no additional references that the full namespace open would redirect.

A broad parenthesis-based binder locator initially returned `shellBase`, `windowLength` and `windowStart` inside ordinary function applications/casts such as `(windowStart A T j k : Real)`. Direct inspection distinguishes these from parameter declarations. The nine original declaration parameter lists and local let/have/intro names bind none of the provider declaration names. There is no observed local shadowing or altered local variable binding.

These checks are bounded to the exact caller/provider source context. They do not pretend to establish name uniqueness in every possible imported environment or to run elaboration. The original source had not been successfully elaborated here, so this review does not claim equality to some previously accepted elaborated signature. It approves the explicit reference to the **intended original provider objects**, with unchanged textual types and premises.

## Mathematical and historical boundary

The primitive Shiu boundary remains an explicit structure input with its same fixed A/X0 and alpha/kappa conditions, and the same bound uniform over the four changing natural parameters. The actual windows, cutoff arithmetic, translated branches, modulus condition, primitive residue, Euler exponential and all original hypotheses are unchanged. Opening a namespace supplies no analytic existence theorem and pays no medium/Atlas/Native6 estimate.

The new postimage addresses the previously documented static missing-open issue. The old `HOLD_STATIC_UNQUALIFIED_SIBLING_NAMESPACE_REFERENCES` continues to describe the untouched 565b preimage. It is not edited in V16/V17 or silently marked passed. ROOT may record a separate postimage-specific source repair based on this AL; any installation, source-graph overlay, publication, elaboration and kernel acceptance are later actions.

Thirteen fixed historical pins still match their original paths. The fourteenth is a rolling publication index: N08 pinned `04e8cf7e…` (2995590 bytes), while the live path now contains source67 index `73c358f9…` (3007838 bytes). The exact old bytes were independently verified at `output/resume-20261121/source-sync/48af7e3d/BEFORE_PUBLICATION_SOURCE_INDEX.json`. Its SHA and size match the author's historical pin, and the adjacent sync receipt records the exact before→after transition. The live rolling path is **not** described as unchanged. N08's freeze and historical pin record remain untouched.

## Operations

Independent raw-byte, source-text, JSON and hash reads only; the reviewer wrote only this new review directory. No author helper, Lean/Lake/LSP/kernel, object load, fixture, validator, network/download, Git/GH write, CI, quota call or subagent was used. The byte audit, namespace/line map and historical-index binding are separately frozen alongside the exact source allowlist.
