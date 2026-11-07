# P1.4 persistent handoff — physical 3t tuple gates

Baseline: `4016ff95681f9d59c31c84ea0c6e29356c084b5d`; isolated task branch: `chatgpt/p1-full87-odd-gates-physical-tuple-20261107`; latest source packet: `docs/source-only/20261107-full87-four-history-physical-tuple`. Read the full .lean + REPORT.md + REGISTRY.json + INPUT_BOUNDARY.md + this HANDOFF.md, and fetch live branch HEAD BEFORE any next write. Do not reuse an earlier SHA as a rollback point. Source hash is recorded in REGISTRY.json at this packet commit.

This packet adds genuine candidate derivations for `N ^ originalHistory(t) j` as the product of original processing-order prime tuple positions 0 through 2*j times that prime squared, and instantiates four strict cap bounds at every original owned eighth state, using the actual H and same finiteCap. It does not identify tuple products with the literal list suffixes or prove J < cap yet; do not mark J blue. Both density and compiler reserves are untouched.

Immediate next file: a focused suffix/tuple transport proof built on `primeHistoryTuple_reverse_ofFn`, `actual_eight_odd_square_ceiling_lt` and `owned_four_physical_tuple_gates_below_actual_cap`. It must supply the eight-word and strict order from actual `owned87_eighth_state_exact_carrier`, not assume a reindexed word. Then show `J < actualFrozenPost8Level ... false` and eliminate the CAP-side historical-shell invoice, without falsely eliminating its parent-side counterpart. Preserve exact boundary and occurrence multiplicity.

Status remains SOURCE_ONLY, UNEVALUATED, UNCOMPILED. No Lean check, independent review, original saved87 replay or reserve payment. No CI/Codex/upgrade. Never infer complete P1.4 from this packet.
