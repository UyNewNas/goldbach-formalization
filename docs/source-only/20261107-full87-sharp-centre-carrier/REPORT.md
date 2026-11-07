# P1.4 — actual original sharp source and once-only centre-prime deletion

Baseline `91b1121097aa07651eb82363252094e4dba2b3b2`. Source commit `bda79f8cb8644ea0b85dd6bd221d5e58b02af1d5`. Independent branch `chatgpt/p1-full87-sharp-centre-carrier-20261107`. Added source `P4AOriginalFull87SharpCentreCarrier.lean` (214 lines, Git blob `ac5fed117922c324ba5027f547b34265f915d428`); all changes restricted to this proof packet. Pinned manuscript, toolchain and c,K unchanged, see REGISTRY.json.

## Actual mathematical correction

The predecessor `originalSharpLiteral` counts every prime p<N in the enlarged prefix. The manuscript's `chenAdditivePrimeCarrier N` instead excludes *all* primes p|N. For even N>2 the prime p=2 is excluded from the actual receiver source, although p=N is not prime. Thus excluding only the zero gap p=N is insufficient.

This packet reuses `chenAdditivePrimeCarrier_eq_prefix_filter`, `centrePrimeAPCount_eq_divisor_fibres`, and `sum_chenPrimeReceiverSource` to supply candidate finite identities

  originalSharpLiteral = actualSharpCarrierLiteral + centreSharpSigned,
  actualSharpCarrierLiteral = sum over genuine chenPrimeReceiverSource of same originalGapFibre.

The centre correction is **precisely**
  centreSharpSigned = sum_{d in original full-q support} rho(d) * chenCentrePrimeAPCount(N,N,d)
                    = sum_{p|N prime} originalGapFibre(N-p).

It is not a second smoothing endpoint or a new arithmetic mask. Its signed absolute value is bounded once by the already existing same-rho `centreDivisorInvoice`.

Combining with the predecessor's `original_sharp_true_singleton_PP_invoice` yields the candidate actual-source inequality

  |actualCarrierSharp - sum_d rho(d) X_W^(d)/phi(d)|
    <= |signedPrimitivePP| + lowerEndpointInvoice
       + upperEndpointInvoice + centreDivisorInvoice.

No analytic smallness, PP permission, density transfer or reserve payment is inferred. The original physical rho and occurrence aggregation are unchanged. The exact signed identity's centre correction has a minus sign, although the displayed invoice takes absolute values.

## Checks actually performed

Read actual GitHub predecessor HEAD, predecessor REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF, whole recent Lean source, original prime source, existing centre divisor-fibre and full-beta rho bound, weighted sharp-smooth and fixed manuscript. AGENTS.md checks at repository root, docs, source-only, packet and ImbalancedChen returned not-found at the frozen baseline. Independent exact Python Fraction synthesis with 3000 composite-centre instances, signed coefficients, variable windows and zero modulus: 0 contradictions of centre split, signed singleton PP arithmetic or the centre invoice. These are synthetic cases, NOT real saved87 replay or Lean proof checks.

GitHub readback confirmed source blob `ac5fed117922c324ba5027f547b34265f915d428`, 214 lines, no forbidden proof-escape declarations and balanced ordinary brackets. SOURCE_ONLY / UNEVALUATED / UNCOMPILED. Lean/Lake not run; no kernel replay, transitive axiom audit, independent review, saved87 certificate verification, Codex, CI dispatch or resource upgrade. Kernel acceptance remains zero.

## Still unpaid

Actual Gevrey singleton W support, [0,1] and interior-one properties, Euler derivative budget, exact prime universe, and fixed-parameters-before-N quantifiers; physical q>0, q<=N^(7/32), squarefree/coprime support and signed PP policy admission. Smooth coprime mean -> sharp pi(N)/phi(q) quantitative mean boundary; centre invoice and endpoint/primitive sums relative to H_N. Rank9 historical/cubic expense, ordinary residual integral, sixth raw/finite/filtered signed losses, saved87 geometry/numerics, changed/tagged and two separate compiler/density reserves. P1.4 remains YELLOW.

Next concrete source action: bind the physical q-support PP permissions and actual Gevrey W to this centre-corrected original carrier, then quantify the actual smooth-coprime-to-sharp-pi mean difference without counting the same centre deletion twice.
