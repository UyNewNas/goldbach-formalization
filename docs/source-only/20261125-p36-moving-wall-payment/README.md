# Fixed-width payment for finitely many moving wall centers

**Source-only candidate. Strict Lean compilation, official kernel replay and full owned-declaration audit remain pending.**

The main new entry is `exists_uniform_centers_full_residual_wall_payment`.
For positive fixed rough exponents `0 < omega < v`, a fixed finite list of proper
linear forms, and `eta > 0`, it chooses `delta > 0` and a common `N0 >= 2` before
`N`, every wall center, the enumeration cap, the causal policy and the rounding mesh.
For every later even target it bounds the literal `wallRoundingCharge` by `eta`.

The proof uses the existing linear coefficient representation and its nonzero-coordinate
lemma to apply the fixed-width slab corollary. The union is bounded by the sum over
actual prime slabs. A finite minimum with a dummy width one handles empty families,
and a finite supremum gives the common threshold. Closed endpoint atoms and target
prime deletion are preserved by the original finite carriers. The last step applies
the existing `wallRoundingCharge_le_two_mass` and complete residual mass envelope.
No canonical factorization, totient product or Euler estimate was reproved.

The five declarations are the linear-form fixed-width corollary, radius monotonicity,
the finite union bound, the uniform-center finite-family reserve, and the full residual
payment. The dependency preflight records the prepared existing payer source separately
from canonical sources; it is not evidence of successful compilation.

This result does not itself connect the actual U5 mixed catalogue to canonical prefixes,
choose the final common fine mesh, pay the complete rounding loss, establish density,
or prove a common physical Q, tensor decomposition or P3.6. Those interfaces remain explicit.
