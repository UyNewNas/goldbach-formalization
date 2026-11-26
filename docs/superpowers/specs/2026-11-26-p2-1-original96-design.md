# P2.1 original 96-term logarithm producer

The current continuation closes the concrete `log_interval` obligation in
the frozen 1106 numerical appendix. It does not change the already accepted
five-root query closure or declare the entire P2.1 board node complete.

## Source and required behavior

The manuscript is `UyNewNas/chen-imbalanced-semiprimes` at
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. Its source
`verification/data/corpus-renewal-paired-certificate-v2-20261010.py`, blob
`ad918b5084fb83ff58d7cbb8cb23fa3e4e47ddce`, lines 50–61 defines the
producer on rational inputs `1 ≤ q ≤ 2`. Preserve its 96 steps, working
scale `W = 2^224`, output scale `P = 2^160`, final shift `2^64`, and
`TAIL = ceil(9*W/(4*193*3^193))`. In particular `q = 1` returns `(0, 1)`.
Each step adds the current odd-power bounds divided by `2*j+1` before
advancing the powers. Every integer division remains the literal source
operation, including `(n+d-1)//d` at upper endpoints.

## Approach and reuse

Model the literal integer state with structural recursion, prove its
power and partial-sum invariant over the rationals, and derive a
`RationalLogCertificate.Valid` certificate for the actual two outputs.
Reuse the accepted `RationalLogCertificate.check_sound` for `Real.log`.
The existing, broader remainder is already smaller than `1/W` throughout
this input interval, while the original `TAIL` is exactly one. This avoids
a new analytic remainder theorem. A fold over the original range gives a
separate source-shaped execution model and a general loop equivalence.

Direct adoption of the historical Q80 loop is inapplicable because its
scale, term count, and tail differ. Importing the sharp real remainder
theorem is possible but unnecessary for enclosure and enlarges the
dependency closure. These are implementation decisions by the assistant.

## Constraints and evidence

Author all code in the primary workspace; compile in the designated P2
service or the user-provided backup with the exact same pinned toolchain.
Do not interrupt others' jobs. No `axiom`, `sorry`, `admit`, `native_decide`,
or `unsafe`. Do not rerun the completed 140-module archive acceptance.
Run strict compilation, public type checks, all-owned axiom audit and
independent kernel replay for newly accepted sources. Record actual
commands, source hashes, toolchain and results. Source-shaped Lean
equivalence plus finite Python comparison is not a formalization of the
Python runtime. Preserve that boundary in reporting.

The broader paired-cell integration and all historical serialized tables
are outside this increment. Their existing node ownership is unchanged.
