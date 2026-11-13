# P2 r9 targeted repair (uncompiled)

Base source composite: CI 9e4fa641ef9fad4a8cb073ff7e883a660131eeff / source 484d8ffc8f79e7c213b33ae86a8d960cd4da6de4, baseline eb035a259f2f40853e9899f6d98af25852184fee. Both affected modules were baseline-origin as recorded in P2_VALIDATION_MANIFEST.json.

Observed run 43430153710 failures: P4ASixTentRange32OldWeight:266 dependent match; P2OriginalThirdSecondDecay:140 unknown ordinary_factor_integrable.

Only proof-body changes: split TentSide k in the branch guard conversion; qualify both ordinary_factor_integrable calls with their already-imported OriginalThirdP4AOrdinaryEarlyReturnSourceOnly namespace. No import, statement, premise, definition, data, dependency, or workflow changes. Existing factor integrability supplier verified in exact pinned OrdinaryEarlyReturnLeaf source (686024b292027816b712963167436c445df5e68e).

Static review only. No Lean execution, no CI launch, no kernel/axiom acceptance. Full 102-module original gates must remain mandatory in a separately bound CI driver. P4 retains next fair heavy slot; no existing run cancelled.
