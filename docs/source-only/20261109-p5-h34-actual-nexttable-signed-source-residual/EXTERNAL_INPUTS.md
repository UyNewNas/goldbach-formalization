# P5.6/h34 — external input register for actual next-table source residual

The fixed original register and manuscript version remain unchanged.
This packet implements only manuscript-local finite sums and the
original feedback source interface, not PNT, Mertens, BV or any
replacement external analytic theorem.

## Reused fixed-version interfaces

- Mathlib, at fixed revision
  \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`:
  finite sums/reindexing, real rings, absolute-value triangle bounds
  and order arithmetic. Called in the seven new Lean candidates,
  with no new analytic hypotheses.
- Existing \`all_markedBankRead_le_candidate\` from the original
  selected-bank candidate level. Its exact invocation is
  \`actual_bank_source_gap_le_candidate_gap\`, and the subsequent
  \`actual_new_table_same_q_one_sided_source_budget\`.
  This is an internal existing requested-feedback lemma, NOT a
  newly outsourced assertion about the original arithmetic count.
- Existing \`uniform_actual_retained_selected_same_q_envelope\`,
  consuming the preexisting bank/Buchstab raw coefficient error
  and row mass supplier. Called only in
  \`uniform_actual_new_table_same_q_source_residual_bound\`;
  no new analytic theorem is imported.

## Not external

Both exact actual next-table source gaps, bank/Buchstab source-gap
growth estimates, original U3/U4 count-owner compatibility,
PP/same-rho matching, correct floor/seed/base inequalities,
native-history control and common 430+11 nesting are all
manuscript-internal and remain unclosed. The existing raw external
prime-profile/distribution chain is neither reimplemented nor
declared kernel-verified. No new axiom is introduced.

Status: SOURCE_ONLY / UNCOMPILED / transitive audit NOT RUN.
