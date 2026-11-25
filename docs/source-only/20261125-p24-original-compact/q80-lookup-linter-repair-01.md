# Q80 lookup strict-linter repair 01

Date: 2026-11-25. Status: source repair prepared; actual retry pending.

Root reported P3 job `4b75d6ee19a24eec83462832c647a2ac`: `P2DirectedLogRounding` and `P2GuardedReciprocalRoundingCore` passed; Q80 lookup had only three strict-linter failures. This task repairs exactly those reported failures and does not compile.

Input HEAD: `9b29332d3078c9d8e824d2ddabc72ef7a9679246`.

| File | Before SHA-256 | After SHA-256 |
|---|---|---|
| `ImbalancedChen/P2HistoricQ80DefectLookup.lean` | `992a456dcb131b00fd07d3520d9a77b0c9d23abd4d7b3130b880800c2af9c1f1` | `82cd65f83b1e7dbe3682b7564e241768103ea834ba72f1ee1846fe200d023414` |

Only original lines 80, 85 and 141 change: remove unused `Enclosure.add` and `Enclosure.neg` from their respective simp lists; remove the unused `<;> ring` after `field_simp [Q_ne_zero]`. The Core import and all 43 theorem headers remain byte-identical; every other source line is unchanged. No linter is disabled and no mathematical premise or conclusion changes.

Root will publish and retry. No Lean/Lake, kernel replay, cloud job or CI was invoked by this repair task. The reported diagnostic passes are not treated as complete input qualification, independent kernel acceptance or P2.4 completion; root separately owns those checks.
