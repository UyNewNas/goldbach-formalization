# P5.6 h34 — genuinely external inputs

Fixed manuscript: `ba6ec11d800eccc54406490631895e174de85766`.
Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

No new external number-theoretic theorem is stated, proved or assumed in this packet. The module reuses the **existing** manuscript-local `Part5OriginalH430RequestedLevelBankSupply.uniform_level_bank_supply` with its original uniformly quantified pre-N threshold, 4<=T, 0<=tau<=1/12, reciprocal n constraint, prime/coprime root and root-band hypotheses, and each selected Fin 430 bank slot. The direct invocation is in `uniform_selected_bank_physical_source_open_excess`.

Mathlib reuses `Finset.sum_le_sum`, `Finset.sum_add_distrib`, `Finset.mul_sum`, real absolute-value/positive-part order facts and linear arithmetic. They are not replaced by native tactics, external axioms or finite experiments.

The source also uses manuscript-local `Part5OriginalH430TrueRootFinWaveBridge.frozen_root_430_le_actual_fin_payments` for the exact 430-root list-position correspondence. No PNT/Mertens/BV or other external proof is expanded.

**Still manuscript-internal (not reclassified as external):** selected Q80 bank read/base/fixed/feedback/floor and true-read ideal positive surplus, Buchstab physical positive source, correct seed/base/switch, full U3/U4 count owner and 7/2 normalization, full/selected/inherited filters and rejection multiplicities, PP/same-rho consumer compatibility, signed Euler/native-history, outer integral–Theta–count, and the common nested 430+11 geometry.
