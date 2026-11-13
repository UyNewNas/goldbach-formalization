# P4 FinitePi canonical owner import candidate

Status: SOURCE_ONLY_UNCOMPILED; no CI dispatched.

Source candidate: 5ccdc63953a82dca253bea6f74c4301025199a32
Base: 4c2d214d2d40160dc400e4b7816f4189f482b374
Changed file: ImbalancedChen/FinitePiIntegral.lean
New Git blob: c548ea28e787ea24a3fce871f87be799d93682e9
Change: add import Mathlib.MeasureTheory.Integral.Pi; every byte of the existing theorem statements and proof bodies remains unchanged.

Evidence: run43369809371 job131702680478 showed Fin.insertNthEquiv.eq_1 serialized by FinitePiIntegral but canonically owned by Mathlib.MeasureTheory.Integral.Pi, also serialized in TorusIntegral. Its four own integral declarations were present. The pinned Mathlib file at e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 itself unfolds Fin.insertNthEquiv in fin_nat_prod and integral_fin_nat_prod_eq_prod. Explicitly loading that same pinned owner before the project proofs tests reuse instead of local lazy equation generation. This is a hypothesis-driven source candidate, not a verified repair.

P2 comparison: p2-validation-v6 at 81cb87f5cd18ab8dc4e85300340de92d91c551bb still uses original blob3f768c8c12dba787dd716f7b8854813f8eb094d9. Its FINITEPI_PREFLIGHT_PLAN explicitly warns that single-module ownership success does not predict combined-environment ownership. No existing P2 source fix was found in that selected bundle; reuse its strict pilot method, not its success as full-P4 credit.

Next driver preparation: fork the P4 diagnostic driver, bind SOURCE_COMMIT and source checkout to 5ccdc63953a82dca253bea6f74c4301025199a32; update only FinitePiIntegral source hash/blob in p4-profile-manifest.json after computing the actual bytes. Keep 146-project-module closure and pinned external dependencies; the new external import is already present in the combined environment observed in the failing run. Independently verify stage/import closure rather than assume. Keep strict serialized==owned census, full types and transitive axioms, object stability, leanchecker, 12 GiB trust-zero and runtime. Do not suppress Fin.insertNthEquiv.eq_1 in the audit. Existing closure may expose later mismatches once this first failure is resolved.

Queue: Stored042–052 run43376280452 occupies the heavy slot. Do not launch concurrent CI. This branch's commits use skip-ci. Full compact profile acceptance remains unproven; six-target and manuscript mathematical closure remain outside this candidate.
