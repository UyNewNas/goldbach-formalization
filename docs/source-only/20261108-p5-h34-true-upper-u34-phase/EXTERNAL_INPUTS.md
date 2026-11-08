# P5.6 → h34 — external inputs boundary (true U3/U4 upper phase)

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (`paper/source/manuscript-body.tex`).
Source commit: `ee2072ab8f37aebaaac3d522d7f2e9be72b95fb2`. **New external analytic inputs: NONE.**

This packet imports the existing manuscript-INTERNAL `ImbalancedChen.Part5OriginalU34H430Integrable` upper U3/U4 coefficient dictionary, its actual `v(t)`, main/tail residuals, U3 switch, U4 domain, literal `rootArgument = max 2 (L/a)`, and the existing immutable H430 table `H430Numerators`. All use the pinned Lean v4.33.0-rc1 and Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 dependency versions. It reuses only ordinary real arithmetic, `linarith`, `norm_num`, `min` monotonicity and set-interval simplification.

No PNT, Mertens, BV, new Buchstab theorem, PP/same-rho theorem, numerical430 verification, or new prime distribution input was implemented or asserted. Original upper receiver count-source identification, physical z0, true owner, full/selected/inherited filters, root weights and all count/payment compatibility remain **manuscript-INTERNAL**, not externalized. Compilation, kernel replay, transitive-axiom audit and numerical certification have **not** been executed. Numerical430 is **UNEVALUATED**.
