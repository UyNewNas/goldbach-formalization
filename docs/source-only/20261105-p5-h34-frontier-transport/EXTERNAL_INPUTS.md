# P5.6 / h34 frontier transport — external inputs recorded, not implemented

Date: 2026-11-05. Parent 42859b2.
Scope: manuscript-internal finite occurrence/source transport only.

## Existing formal utilities reused

- Pinned Mathlib List.map, List.append, List.prod_append,
  List.mem_cons, List.mem_flatMap, List.mem_map,
  List.mem_filter, Finset.sum_congr and arithmetic tactics.
  Their exact bundled pin is inherited from the repository;
  this packet does not upgrade or re-prove them.
- Existing manuscript-local
  \`Part5OriginalH430RequestedHistory.history\`,
  \`history_facts\`, \`levelOccurrence_source\`,
  \`rootHistory_sameQ\`, \`rootHistory_integer_word\`;
  and \`RequestedBranches.edgeValue\`, \`edgeWeight\`,
  \`children\`, \`nextRequest\`. The identity is unfolded
  against these literal upstream definitions, not a new API
  with count-bound assumptions.
- The prior \`RequestedAllChoice.generationValue\` declaration
  is consumed unchanged.

## Genuinely external number-theory inputs

No additional PNT, Mertens, BV, prime-in-progression,
semiprime distribution or analytic seed theorem is required
or re-proved by this finite transport. The previous packets'
external dependencies remain recorded there and have not
been replayed/audited here.

## Still manuscript-internal

Reverse exact next-frontier multiplicity, original U3/U4
prime/PP count-source identity, root weights, filters and
rejected lanes, seed/base/floor/PP count signs, same-rho,
native history mass and common causal430+11 refinement are
NOT external inputs. This packet supplies no substitute
count licence, hypothesis, axiom, or synthetic source.
