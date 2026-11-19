# P2.5: first original row at the actual compiler fibre

Baseline `e177b5bb8f26f0ca6f58bd84930ec8bb713d848d` on `chatgpt/p2-saving16-cofinal-20261119-1727`; the commit containing this packet is its new SHA. SOURCE_ONLY; UNCOMPILED; KERNEL_REPLAYED=false; transitive axiom check NOT_RUN; independent review NOT_RUN; finite source reductions UNEVALUATED.

## Concrete candidate

`P2Saving16FirstRowCompilerFibre.lean` selects only row index 0 of each of the fourteen actual ascending source members. The source table's fourteen first indices are all 0, and literal pool row 0 is `(25/128,-1,0,0,0,0,0,0,0)`. Thus its affine expression is `mu-t_1` with `mu=25/128`. The Lean candidate `original_first_row` connects that expression to the actual `rowForm` read by the eighth trim program; the 14-case `norm_num` proof has not been elaborated or evaluated.

For an actual rough word x of rank at least eight whose eighth coordinates lie in the original cell's `trim delta`, and a positive fine width `tau < delta`, `first_upper_endpoint_strict` constructs the upper endpoint of the first original fine-label interval and derives `mu-upper>0`. This is a statement about the geometric upper endpoint, including the endpoint itself. It follows from the same trim's first ordered-core margin and the original half-open label lower bound: `upper≤t_1(x)+tau<t_1(x)+delta≤mu`. It does not assume a corner-level compiler equality.

For y in x's actual empty-tag compiler fibre, `first_row_and_signed_compiler_on_fibre` keeps that first original row strict on y and identifies the actual rough compiler coefficient as `mu(y)` times the actual scalar read on x's same fibre. It uses the literal Möbius sign, not a count or a set equality. `first_row_full_modulus` attaches the existing sign-selected actual beta coefficient at each permitted small factor b and retains arbitrary full-q weight `G(b*y)`. It has the same N, cap N, w, z, tau and L as the R17 compiler coefficient. The pointwise hypotheses include the actual rank-eight source trim, fibre membership and small-factor support; they are not proved for every original corner or every compiler atom here.

## Precise boundary

This packet treats only the first of 96 affine rows, all fourteen source indices, on fibres with a witness in the corresponding trim and `0<tau<delta`. It does not identify the ALL/ANY predicate with the manuscript's full lower/upper corner test, prove the remaining 95 rows at any corner, or transport the same actual fourth parent into that fibre. It does not prove that the common schedule selected its aligned tau below delta; any such refinement must retain all earlier choices and the already-paid `u_c`. It does not promote a source witness into a new saving or repeat the ordinary Q96 charge, the w=0 negative complement, or an inherited moment.

The signed distribution error still belongs to the literal compiled `Q,rho`, at `0<b<1`, `T>0`, `ceil z≤T^(b/(1+b))`. The local first-row corner says nothing about whether the original whole-upper-corner medium partition, buffered above-mu fallbacks or strict power savings have been established. In particular this is not a PP estimate.

## Inputs and verification

Read the prior P2.5 ledger and its Lean source, original source binding, full original ascending affine table, `P4AOrderedThirdEighthTrimProgram`, `P4AFull87SamePieceCapVariation`, `P4AOriginalOrderedThirdActualCoefficient`, original `eighth-prefix-family-20261009.tex` blob `6c1f0d2fc5e77b575e8e2260918619ce08406068`, and original compiler audit blob `d99156d7e4fb3914bedfe4cb9e5b329899a20f37`. Rechecked manuscript commit `9731290e8f53cffda44129906cde6a965eaa869b`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Current branch pins remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`.

`lean --version` and `lake --version` each returned exit 127, command not found. A literal text check found all fourteen first row indices zero and the quoted pool row. A separate exact-rational sanity check covered 2,206 eligible half-open cases and checked the upper endpoint; these are not Lean elaboration, archive evaluation or kernel evidence. The proof text scan found no new axiom, sorry, proof-tactic admit, native_decide or unsafe. No CI was run. Next: type-check the exact staged source graph, then handle the next original row with its actual strict/non-strict corner rule and keep tracking the same signed occurrence and fourth parent into the paid compiler.
