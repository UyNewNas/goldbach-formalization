# P3.5 all-chart reduced-pair transport: source-only handoff

## Base and changes

Base branch `chatgpt/p3-5-bounded-chart-20261119-1734`, HEAD
`f54c691c3df7f5514b247f663e567a94b85a6642` verified before this packet.
The commit containing this packet is the new SHA (the containing commit
cannot embed its own hash). This run adds only
`Part3OriginalAllChartLossyPair.lean` and this report under
`docs/source-only/20261119-p35-all-chart-lossy/`.

Candidate file SHA-256:
`1595e6024afe706191827b9628b71afdbe9a4edd52b6fe8180f3f3c79809c584`.

## Mathematical content and exact limits

For every epsilon>0, the proposed `full_J_with_transport` first obtains
the existing `initial_region` constant at the fixed A=1. For the
complete dyadic m row, `Q>0`, `X>0`, and the same phase omega, let
`M=2^j-1/2` and `X0=Q+M`. The existing positive-frequency transport,
applied to precisely the native complete level sum and rewritten by
`full_window` and `zero_frequency`, gives

    J_Q(X) <= max(1,X/(Q+M))^(3/4)
               * C_epsilon * ((1+Q)*(1+M))^epsilon*(Q+M)*M.

The constant precedes j,Q,X and omega. The 3/4 is the cap supplied by
the existing `actualpositive6` source, not a new global spectral-gap
claim. No full-J input, 7/32 hypothesis, or half-support assumption is
introduced. This is a weaker all-weight estimate with an explicit loss.

The proposed `all_chart_pair_with_transport` substitutes this estimate
for each of the two J energies in `original_pair_to_pascadi`, using
`Q=Z/2` and `Q=Z` at `X=W=max(V,Z^2/V)`. The phase is the same witness
from that pair, with the full original endpoint-corrected level union and
both signs of the reduced n row. The prices are left separate; the
level-varying n coefficients are charged through their original row
square masses, not treated as a common m sequence. No bounded `Z/M`
premise remains. The proof does not claim raw pre-removal trace or total
spectral bounds.

For `Z >= 2V`, `M <= V`, so `W=Z^2/V`; both factors
`max(1,W/(Q+M))^(3/4)` for `Q=Z/2,Z` grow on the order of `(Z/V)^(3/4)`.
This extra power is not a constant and is not the original 7/32 fee. In
particular this candidate does **not** prove full-range Pascadi J or (24)
and cannot replace those bounds in the final 7/32 argument without paying
or removing that explicit loss. The original complete n-side oldform
conversion, regular and continuous returns, gap denominator, and actual
zero/tail/Fourier costs remain separate.

## Source and manuscript boundary

* Original pair source: `docs/source-only/20261113-resume/resume-balance-policy/r14_09/avgj-next/Part3OriginalExceptionalPostRemovalPair.lean`, blob `a038900816ae4e167afb9f46ace2e142440d386c`.
* Native initial-region source: `docs/source-only/20261115-resume/s09/actualpositive6/Part3OriginalNativeJInitialRegion.lean`, blob `45ae9c7ea1bb2ec98f6efe9c2205777b0c15ae1c`.
* Positive 3/4 transport source: `docs/source-only/20261115-resume/s09/actualpositive6/Part3OriginalFullPositiveInitialMean.lean`, blob `a3935959c4efcd93b7f34ae4591ead83760bac5f`; see adjacent freeze blob `ff5cb8cf7a7d1106348101affebbd87ce3f644da`. The full supplier chain is source-only, with its selected paid-return-r2 import as recorded there.
* Manuscript is `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; the (24) and §10(v)–(vii) source is `paper/source/modules/distribution-medium-completion-20261010.txt`, blob `19f9672bc9b6d455045213c5e23e10433a9569d2`. Its common m interval/phase and level-varying n row match the separation used here.
* External input boundary is unchanged from the previous report: original Pascadi v3 Theorem J for the sharper required level average; ABL v1 Lemmas 3.1–3.2 for oldclass and continuous removal; the appropriately normalized numerical spectral gap. This packet proves none of those inputs and does not add an axiom or assume the target inequality.

## Validation and next step

* `SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no.
  Transitive-axiom inspection: not performed. Independent review of this
  new source: not performed. `UNEVALUATED`: yes for its proof bodies and
  inherited source-only suppliers.
* This environment has no `lean` or `lake` in PATH and no project checkout
  or qualified import closure. No Lean command ran: no compiler exit code
  or compiler log exists. Configured pins in the base are Lean
  `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
  and native `09b97db5764ade1246bfb77206baa1b124760958`. Configuration
  lookup is not proof of an installed environment. The stack limit is
  8192 KiB; shell virtual-memory limit is unlimited. No limit was raised.
* `sha256sum` returned the candidate hash above. The precise `rg -n
  '\b(sorry|admit|axiom|unsafe|native_decide)\b'` scan returned exit 1,
  i.e. no token matches. This is text inspection, not compilation.
* Next, stage the selected exact source modules and their frozen closure
  in an already available matching environment and elaborate the new and
  preceding bounded-chart candidates. Then seek the genuinely sharp
  unbounded-ratio average or a payable replacement. Preserve separately
  the two zero-frequency lanes, actual cutoff tail, 14eta/28eta weights,
  128C enlargement and original threshold order when connecting to the
  full consumer; none is discharged by this reduced pair.
