# P5.6 / h34 — external input boundary for literal round action step

Source commit: `d2c97e7c1ea6164360836e8a43293823c54e9db4`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Status: SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

## New external analytic inputs

**None.** This packet introduces no PNT, Mertens, BV, new sieve distribution claim, analytic inequality, foundational axiom, or imported h34-equivalent source-count assumption.

## Reused version-pinned interfaces

- Existing Mathlib integer/real ordering, max/Finset/List arithmetic, cast monotonicity, and division by positive `2^80`. Used only inside the new finite-algebra proof bodies. Existing Mathlib revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` is unchanged.
- Existing literal Q80 producer `P2Selected430CausalOccurrenceExporter`, especially `offer_numerator`, `ordinaryDecision_numerator`, `scan`, `roundDecision`, `roundTable`, `iterate`; the actual 106 bank `rows` and `candidate`; the original suffix with its integer quotient. These are *manuscript-local source machinery*, not outsourced external analytic inputs. The new proofs invoke these names directly.
- Existing `Part5OriginalH430PrefixClosedCellWinningBudget` as the pinned import closure entry. This packet does not claim that module or its transitive dependencies are compiled or axiom-audited.
- `floorValue` from the pinned causal dictionary and `queryCell` from the original finite exporter. Real cell arguments remain the original closed cells, including endpoints.

## Still manuscript-internal, explicitly not externalized

All actual same-Q Buchstab and bank candidate upper bounds, uniform analytic F/cell envelopes, true seed base, complete 430 closed-cell induction, positive source and fixed/slack/feedback/floor payment, selected U3/U4 root count and q/tag ownership, PP/same-rho consumer matching, native-history, integral–Theta–count, common 430+11 nesting, and correct c/K/root/row norms remain internal. No assertion in this file provides these missing premises.
