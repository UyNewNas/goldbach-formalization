# P1.4 input boundary — low physical delta

**External analytic input:** none introduced or invoked by this packet.

This candidate uses concrete, already existing code and original policy definitions:
- `P1Full87ChangedRoughLevelObstruction.actual_full87_changed_rough_wpow_five_le`: **prior candidate**, not compiled. Premise: the same original policies R,S, same (N,cap,w,z), and `1 <= w`.
- `fixedRoughCoefficient` and `fixedRoughSupport`: original rough Möbius/zero coefficients; no fresh mask.
- `actualSmallRosserSupport_smallPrimeSupportedAt`: `a != 0` is essential for `b <= d=a*b`.
- `actualSmallRoughRho_eq_on_common_carrier`, `smallRoughRho`, `smallRoughRho_eq_zero_of_not_mem`: reindexing the two unchanged original physical coefficients on the **union** of their original rough supports. Their beta-minus/plus, signs and exact modulus d remain intact.
- `P1Full87TrueDPolicyDelta.trueDDeltaRho`: zero-extension on each original physical support.

Frozen source manuscript commit `9731290e8f53cffda44129906cde6a965eaa869b`, Blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. The known compact family `w=N^(epsilon^2)` is **not** silently installed into full87. The theorem is uniform in given w,z,L under `w>=1`, but is not a quantified large-N estimate or an application of `eq:current-PP`.

**External PP/distribution input registration:** `eq:current-PP` from frozen manuscript § on prime products, **NOT_APPLIED / NOT_AUTHENTICATED**. Its original hypothesis, normalization, smoothness, coefficient family and calling proof obligation are unchanged; the current file provides no new premise nor counterfeit proof. The eventual application must verify the actual same physical `rho_N` and `W_N` and supply quantitative arithmetic error and reserve payments.

**Validation boundary:** SOURCE_ONLY / UNEVALUATED / UNCOMPILED, transitive prior candidate dependency uncompiled; no external result marked VERIFIED; no sorry/admit/axiom/native_decide/unsafe introduced.
