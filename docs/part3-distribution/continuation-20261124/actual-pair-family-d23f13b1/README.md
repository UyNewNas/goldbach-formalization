# Accepted uniform-width actual smooth-pair family

**PASSED: 1 module, 5 complete owned declarations, all theorems.**

- Source commit: `d23f13b1d55423ede87153a147f77bbd227fa916`.
- Module: `ImbalancedChen.Part3ProperPowerActualPairFamily`.
- Source SHA256:
  `d663cf07c61ac7f2844faf7303aea42e502b305f7a47b56b725a9edbcf8c4ca0`.
- Environment: Workspace Compile 27f68009, `/workspace/goldbach-p3`.
- Task: `ff76d4db005f4de79bc6fb7b5d8f30f6`, exit 0, 346.108 seconds.
- Pinned Lean: `4.33.0-rc1`, commit
  `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- Pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

The module passed strict compilation with warnings as errors, literal
bundled `leanchecker` replay, and the original complete serialized /
environment / defining-module inventory and transitive-axiom audit. The
only allowed transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. All 11 actual dependency pins, final source/object hashes
and clean-tree checks passed. The 80 baseline proof files and the ten
previously accepted continuation sources remain byte-identical.

[report.json](report.json) and [declarations.json](declarations.json) are
the exact output bytes. [verification.zip](verification.zip) contains
all 33 stage logs, the generated audit source, full types and inventory.
Archive size: 42,347 bytes. SHA-256:
`58bd16d8783e3c26f885d9768db1ffacc84fbf0489f3a7b4d127e1f3316bab33`.
The [service task receipt](task.json) records a sampled peak RSS of
8,638,513,152 bytes.

## What is proved

The actual smooth physical pair source has the same effective integer-VM
roughness and complete-product carrier for every `0 < width <= widthMax`.
The carrier is always `Icc 1 (ceil (exp(widthMax) * N))`. ChartSum is applied
at fixed `C = exp(widthMax)` before choosing the width, so one analytic
threshold works for every admitted width, carrier, signed rho and cutoff.
The residual estimate and exact prime-minus-VM estimate both preserve the
same rho, exact coprime mean and complete-product-N diagonal.

An N-dependent width sequence is obtained by direct specialization. If
it only eventually enters the admitted interval, the final combined
threshold may also depend on when that sequence enters the interval.
No exchange of separate fixed-width eventual quantifiers is used.

The physical modulus cap and fixed divisor-order rho bound remain
explicit. The leaf concerns proper-power deletion; it does not assert
that every shrinking width meets the separate polylogarithmic Euler
derivative budget required for HB/spectral steps. The manuscript's fixed
epsilon pair argument is still covered by the earlier accepted module.
Spectral (24), actual final-policy assembly and P3 as a whole remain open.
