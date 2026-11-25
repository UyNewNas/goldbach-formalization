# Literal U5 fresh-fifth square supplier — source candidate

Base: `edc2e68c360bf66bd33e4a3a5211cafd6d95f218`.

Status: **source only, uncompiled, kernel unverified**. This directory is not
part of the selected compilation manifest. No compilation task was started.
This candidate did not edit the main cap source or `SOURCE_SELECTION.json`.
The frozen Lean source SHA-256 is
`23eaf74c721d1b1d07acdd03eafb8b2fefffd6df565e58766272c0b973dcd48c`.

## What this candidate adds

`ImbalancedChen/P3OriginalU5FreshFifthSquareSupplier.lean` connects the literal
original U5 `selectedPolicy R bank buffer false N t` to existing square
suppliers on its actual fresh fifth branch. It neither replaces the policy
nor resets the pair seed. Its three supply theorems are:

1. `actual_U5_fresh_fifth_rough_supply`: from an original accepted rough word
   `q₀ :: q₁ :: q₂ :: ds` and the actual fifth fresh action, derives the exact
   stored H5 cap, the full and selected-complement squares on the complete
   outer-pair/rough word, and its budget for the literal small Rosser level.
2. `actual_U5_fresh_fifth_signed_supply`: uses the original nonzero rho and
   its same small/rough factor witness. It derives active-pair membership,
   consumes the preceding supply, then applies the existing signed small
   extension. Its outputs include both complete square lists, the original
   SourceForm selected mask, the canonical prime-factor word of
   `fullModulus t k`, and the original signed rho identity.
3. `native_U5_nonzero_fresh_fifth_supply`: starts directly at a nonzero
   native U5 rho, recovers its already existing actual word witness, and
   returns the preceding result whenever that witness's actual fifth
   selection is fresh. No witness existence or acceptance licence is added
   to this final theorem's inputs.

`FreshFifth` is the actual finite branch condition: `select R bank (2*b) 5`
on the exact original code returns the named SourceForm, and the actual
`freshCheck` against `cap4` passes. It is not a square-support, modulus,
factorization or PP condition. The cap and both square lists are outputs.
No theorem assumes `hfull`, `hselected`, a row-to-trace `hcap`, or the desired
small-factor budget.

This is a genuine branch supply, not a claim that this branch covers the
whole U5 family. The final theorem does not assert existence, positive mass,
or eventual frequency of fresh fifth actions for an arbitrary candidate bank.

## Existing proofs reused, not rewritten

All the following sources are already in the current source tree. This
candidate imports only `P2OriginalPairBufferedRootProvenance` and
`P5OriginalU5PhysicalRho`, which the main cap already consumes.

| Existing supplier | Use in this candidate |
| --- | --- |
| `native_U5_nonzero_word` | The same nonzero native coefficient produces the small/rough factor witness and accepted chronological rough word. |
| `P2OriginalPairSourceReceiver.selected_fifth_point_squares` | The actual PairRange SourceForm supplies the first five slots' own full and selected-complement squares. The ordinary CompactStart selector is not substituted. |
| `actual_fifth_source_cap` | The actual frozen H5 cap is the same selected row at double buffer; no independent `hcap` is assumed. |
| `actual_postfive_integer_gates` | Arbitrary length accepted suffixes preserve both square lists and the original selected mask. No suffix induction is rewritten. |
| `integerSquareGates_product_lt` | The contracted full square list gives the complete outer-pair/rough product bound. |
| `fifth_native_small_level_budget` | The original `L=N^(attachmentNu*epsilon)` fits the compiler buffer from the scalar allocation. |
| `original_U5_small_head` | The actual lower beta head condition `w^2 <= L` is paid from the original precision range. |
| `rho_at_pair`, `actual_signed_small_extension` | The original nonzero rho activates the same pair, retaining its sign-selected beta and canonical factor word. |

The new elementary identities only evaluate this PairRange's source row,
fifth state and mask; the new carrier lemma supplies positivity, chronological
order, cutoff separation and grid membership from the original U5 selector.

## The level and precision parameters remain distinct

For the selected row define

\[
c_2=\operatorname{rowCap}(R,\mathrm{code},2b,\mathrm{branch}),
\qquad
\ell=\operatorname{rowCap}(R,\mathrm{code},b,\mathrm{branch})=c_2+b.
\]

The literal run still stores `c₂`. The extended word's square support is
proved at the same source's once-buffered **cover** `ell`. This candidate
does not identify `ell` with the density's physical level and changes no
coefficient or density. It never substitutes the global carrier exponent
0.599 for a local factorization parameter.

The precision hypotheses are `0 < epsilon < 1/8`, `0 <= buffer`,
`attachmentNu*epsilon <= buffer`, and the explicit scalar grid allocation
`R.epsilon <= attachmentNu*epsilon^2`. The latter supplies the lower endpoint
required by the existing PairRange point-to-box theorem. These choices can
be made before N and before any arithmetic coefficient is inspected; for
example `epsilon=buffer=1/1000` and `R.epsilon=1/100000000` satisfy them.
The local fresh-source proof does not need a new root upper bound on buffer:
the actual selected source checks supply its entire fifth-prefix support.
The main global cap's separate `buffer <= 1/1000` restriction remains intact.

The small-word consumer needs `(B*r)*L <= N^ell`, which is stronger than a
bound merely on the actual `(B*r)*s`. This candidate derives the former
from the contracted rough squares and `L <= N^buffer`; it does not replace
that field by the main cap's final modulus conclusion.

## Exact next unsupplied proposition

The direct relevant existing interfaces were checked before choosing this
subfamily. `P2LowerIntegerRetainedSupport` gives acceptance provenance;
`P2OriginalLowerCompactTraceBinding` and `P2OriginalLowerNestedBufferedStages`
give finite cap/code transport; the actual general square suffix interface
is `actual_postfive_integer_gates`. No same-PairRange public interface in
this checked chain simultaneously produces the mask/cap square invariant
for short words and every fresh/inherited transition before full rank five.
The separate `Part3ActualCompactAllRankSupport` is for the different compact
upper policy and cannot be substituted for this lower pair-root policy.

The immediate missing finite proposition is the following provenance
supplier for the other actual branches. Let `H_j` be the literal pair-root
run after the first `min(3, chosen.length)` rough slots. From the original
selector and acceptance, recover either the original root source or the
last actual fresh source at full rank 3, 4 or 5, together with its literal
mask and stored cap; prove the full and selected-complement squares on
`H_j.word` at that cap. The resulting source must be the one selected by
that exact code, not an arbitrary branch with a convenient inequality.
Short words need their terminating rank; an inherited fifth action needs
the earlier source's continued mask and cap, not a fabricated fresh fifth.

The root reserve, genuine even cube and decreasing-order odd bypass already
provide the expected mathematical ingredients. This source review has not
identified a mathematical counterexample; the remaining finite transition
assembly is not proved by the fresh-fifth result and is not assumed in it.
Full bank adoption and all W source licences are separate from this finite
square provenance task.

Even a completed all-branch square supplier would still need the true local
rescaling, selected-subproduct range, strict reserves, fixed whole-atom
partition and signed coefficient reconstruction before it supplies (F).
None of those conclusions follows merely from this branch's square lists.

## Manuscript alignment

Fixed manuscript:
`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.

- [coefficient-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex), `coef:full-squares`, `coef:selected-squares`: append smaller primes without replacing the selected set; an admitted cube supplies the next square.
- The same appendix's physical/auxiliary level distinction, small beta attachment and parameter order: a support cover does not redefine the original coefficient or density; unique small/rough decomposition retains the actual sign choice.
- [argument.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex), `eq:current-PP`: the count and exact coprime mean retain the same signed rho. This candidate adds support information, not a discrepancy estimate.
- [sieve-appendix.tex](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex), `sv:finite-feedback`: no change to the original physical common Q or residual state is made here.

## Validation boundary

Only source inspection, import-file existence, forbidden-proof-token scan,
parameter arithmetic and source hashes have been checked. These are not
Lean elaboration, kernel replay, an axiom audit, or whole P3.6 acceptance.
The main P1 compilation queue was not touched. Acceptance requires elaborating
this exact candidate with the accepted dependency versions and retaining a
separate receipt.

## Subsequent integration for verification

The root integrator has installed the same frozen Lean bytes at
`ImbalancedChen/P3OriginalU5FreshFifthSquareSupplier.lean` and added that
standard module to the selected source manifest. The archive in this
directory remains the original candidate snapshot. This adds one module
to the previous 254-source selection and no new dependency sources.
Compilation and kernel acceptance remain pending; a separate owned run
will distinguish this branch supplier from the main modulus-cap receipt.
