# h34 input boundary — record external inputs, do not implement them

Scope requested by the user: continue P5.6 -> h34, completing manuscript-internal
proofs only. Record extra-manuscript inputs without implementing them.

This packet adds no axiom, opaque proof placeholder, new external analytic
backend, or assumed h34/row-error licence. Existing imported theorems are reused
at the pinned revision. Reuse is NOT a new compilation or transitive-axiom audit.
The manuscript-internal assembly is not yet complete, even relative to inputs.

## Library inputs used by the elementary deletion proof

| ID | Existing input / contract | Consumer | Work in this packet |
|---|---|---|---|
| LIB-HARM | `harmonic_le_one_add_log N` and `harmonic_eq_sum_Icc`; the real reciprocal-integer sum up to N is at most 1+log N | `primePool_reciprocal_le` | Invoke existing result only; do not reprove the harmonic/integral comparison |
| LIB-LOGPOWER | Existing imported `tendsto_nat_log_pow_div_rpow m ha`, for m=0,1,2 and a>0 | `removalRate_tendsto` | Combine three supplied limits by arithmetic; do not implement a new asymptotic backend |
| LIB-LOG / RPOW | Existing Real.log injectivity, monotonicity and positive-base rpow laws | Endpoint-fibre uniqueness, fixed threshold, support cap | Invoke existing library laws only |

LIB-HARM was read at:
`leanprover-community/mathlib4`, revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
`Mathlib/NumberTheory/Harmonic/Bounds.lean`, blob
`9bf769b83daeb500e353628263c71d5253632220`.

For LIB-LOGPOWER the checked usage site is the existing pinned
`P2OriginalPrefixMaskMass.compact_uniform_prefixMask_difference`.
Its exact declaration-origin file and transitive axiom closure were NOT
independently traced in this session. The new file imports that same existing
closure and uses the same unqualified API with `Wu2008DoubleSieve` open.
No replacement theorem with a guessed implementation is supplied.

## Previously supplied manuscript-local dependencies (NOT reclassified as external)

- `chen_primeFactors_card_le_log`: reuse the old finite prime-divisor count
  bound; the new work is its endpoint-union and two-coordinate application.
- `thetaAtom_single` / `thetaAtom_pair`: retain the original fresh/repeated
  singular factors; do not substitute an artificial 1/(p-1) identity.
- `pairHalf_geometry`, the three singleton geometries, and original row atoms:
  reuse the actual original W2 domains and their residual margin.
- `uniform_selected_bank_carriers`: reuse the held original arithmetic-to-ideal
  supplier at epsilon/2. Its imported prime-profile/distribution closure is
  not implemented or newly verified by this task.
- Frozen U3/U4 Member support, the fixed positive residual floor and same-Q
  root-cell partition: reuse the prior manuscript-local constructions.

## External analytic inputs at the final h34 boundary

Existing PNT/Mertens, BV/distribution and other externally established analytic
results remain inputs to their existing consumers. This packet neither creates
new versions nor claims to have checked their full hypotheses at final h34.
Their detailed final application ledger still depends on the actual original
count-history construction. An untraced input is not marked verified.

In particular, do NOT move the following unfinished manuscript obligations into
an "external input" bucket merely to close h34:

1. The full selected-count source, generation assignments, positive marks,
   owners and full/selected/inherited filter correspondence.
2. The strict W2 tuple -> production prime-child reindexing with actual physical
   ceiling/product/order gates, and the inherited-mask/count interpretation.
3. Literal bank rounded coefficients/point reads/candidate-to-profile and
   ordinary/fixed/switched base accounting; analytic seed application.
4. The manuscript's own positive-product proposition / same-rho instantiation,
   as distinct from genuinely external results used inside that proposition.
5. Native outer integral/Theta/count correspondence and one nested causal
   approximation through 430+11 levels in the prescribed reserve order.

Only genuinely external theorem statements should become input contracts;
internal instances and compatibility proofs still need manuscript-local code.
No new Lean record of final target-equivalent assumptions is introduced here.
