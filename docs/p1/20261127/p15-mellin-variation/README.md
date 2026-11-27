# P1.5: the original Mellin-profile variation leaf

## Scope

This packet selects the existing `Part3PrimeMellinProfileVariation` argument
from original source SHA256
`2146552e2b0e5fcbe8a3ef40626e3dc957ce4721b02e026ba699470550276d75`.
It isolates the Mathlib-only calculus leaf and repairs the actual Lean
elaboration errors recorded in the two retained probes. It does not add
an analytic estimate as a hypothesis or replace the original profile.

For a real C1 function `Phi`, define

```text
F(y) = Phi(y/U) * exp(i*t*log(y/U)).
```

If `0 < U <= u <= v <= 2*U`, `M,D >= 0`, and `|Phi| <= M` and
`|deriv Phi| <= D` on `[1,2]`, the original theorem gives

```text
norm(F(v)) + integral_(u,v] norm(deriv F(y)) <= (M+D)*(1+abs(t)).
```

The complete text from `physicalProfile_variation_le` through the end of
the file is unchanged, with SHA256
`f4b4e02a818daed6c02a2da4cc5fe60f51507d5ee078786b7e62264f49fbe6d7`.
The frequency cost remains linear in `abs(t)`. This is the variation input
for partial summation, not a Siegel--Walfisz estimate uniform over unbounded
frequency. No FixedM, weighted-prime SW, proper-power receiver, historical
medium, or full `hSmoothSignedPP` acceptance follows from this leaf.

## Reviewed source changes

The selected source is 6869 bytes, SHA256
`f57c040a86ad3bda56b21e5fe993a98157de89328862fd741523c3b00191263e`.
It preserves all twelve declaration names, order and visibility. The only
statement annotation change explicitly takes the real derivative of the
original real function before casting it to `Complex`.

- Replace the unused weighted/scaled-prime project imports with `import Mathlib`.
- Use the pinned Lean `using!` and `convert!` matching semantics for the two
  definitionally equal real module instances on `Complex`.
- Construct the constant `ContDiffAt` factor explicitly before multiplication.
- Separate absolute-value delimiters from multiplication tokens.
- Allow the algebra tactic to handle unchanged conversion goals.
- Use `add_le_add le_rfl` for the shared left summand in the derivative bound.

The direct consumer `Part3MellinPrimeIntervalSW` receives an explicit import
of `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWFamily`, whose
`primeSW_uniform_real` previously arrived transitively. Its proof bodies
are unchanged; its source SHA256 is
`20bd87a034f26d0d655507d2b24bf43a50076de19317c1fa0b618b6377ac4016`.
That consumer is source-only in this packet and is not compiled by the
single-owner adapter.

## Validation status and preserved failures

The v3 no-output probe passed in task `job_2ee744896a4f4858b50bd089af2f2a91`.
The original compiler receipt records exit 0 and 18.92 seconds for the
guarded command. Its 2,280-byte `PROBE_RESULT.json` has SHA256
`c516fde8c95f1dddd233b6dc67eb8469ced1bfffd1d715d63f56381a9d2299b0`.
The 1,155-byte compiler log has SHA256
`5590fde6ccca3609eeb50075d0243d663c1ef5b709cc20ff5c0bf4412c1e1e84`.
The probe requested no output object. Formal normal build, kernel replay
and full-owned acceptance of this variation module are pending.

The archived v1 and v2 runs failed in tasks
`job_a43d3e885508427a8669e24aa4a14fd3` and
`job_a24eb1c578aa420083048ec97e864642`. Their original compiler logs
contain 3,190 and 839 bytes respectively. The archive uses the exact raw
files exported from the receiver, including its original line
endings. Both failed runs receive zero formal credit.
The original source-only annotation in the Lean header is retained to keep
the source identity stable; acceptance is established only by the actual
normal, kernel and full-owned receipts for that exact identity.

## Original validation machinery

`run_variation.py` binds the frozen AG `run_selected.py` and reuses its
guard, serializer, normal-owner build, declaration inventory and kernel
audit. It performs only one new owner operation for this module. A prior
owner, failed/partial operation, unexpected source or artifact causes a
stop for inspection. The old source is retained before any installation.

`--check` reads the original successful operation and its receipts without
executing Lean or Lake. It checks complete ownership, including private and
generated declarations, and restricts axioms to the original standard set.
The original 21-target registry is unchanged at 18/21. The adapter protects
those owners plus the existing geometry and historical dictionary state;
neither this leaf nor its probe is used to claim whole P1.5 closure.

The local Python boundary tests exercise the receipt checks and failed-run
preservation rules. They do not substitute for a real Lean probe, normal
build, kernel audit or full-owned inventory.
