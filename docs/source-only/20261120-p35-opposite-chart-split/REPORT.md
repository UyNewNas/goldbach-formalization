# P3.5: original opposite physical chart split

## Packet and baseline

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`37e6874b60e6f08428cdad32cdcea277af18af00`. The containing commit is the
new SHA. Files are under
`docs/source-only/20261120-p35-opposite-chart-split/`.
`Part3OriginalOppositeChartSplit.lean` SHA-256:
`3564221d038278be28ee911be0eec31e6764a2259113943852829f077f4ac6dc`.

## Exact proposed manuscript adaptation

For a fixed original physical Z chart (`upper` either value), the actual
Fourier mark, positive N, nonzero residue and original composite trace
sign `traceNegative = true`, `opposite_chart_split` states

    actualCoeff * fullChartMode
      = signedExceptionalMode + oppositeComplementMode + oppositeContinuousMode.

The left uses exactly the original `fullChartMode` and its sign-dependent
`actualCoeff`; each term on the right uses the same coefficient and
`M * sqrt (fixedZ D upper)` exactly once. The exceptional mode is the
previous one-phase candidate, on exactly the original `chartLevels` and
strict exceptional multiplicities. The complement is the actual native
cuspidal tsum outside the strict set at each of these levels. The
continuous mode retains each original continuous density and integral.
The proof sums the previous single-level identity over that finite
physical chart, uses the original full-chart trace identity and the
previous exact exceptional reindexing, and distributes the two external
scalars. It introduces no new analytic bound, convergence assumption,
outer weight, or assumption equivalent to the conclusion.

The result is a source candidate for a one-chart, one composite-sign
identity. It does not estimate the cusp complement or continuous mode,
combine both Poisson signs, or instantiate (24). It does not turn the
level-dependent n sequence into a common sequence or apply initial J
outside its range. The claimed result depends on the entire preceding
source-only chain and is not a kernel-verified theorem.

## Sources and input boundary

The preceding `Part3OriginalOppositeExceptionalSplit.lean`, blob
`2037814843ce0e8b8857f9809ad074aff5934a8b`, was reread in full: it
separates one row using the original strict exceptional set and original
continuous integral, subject to its unverified proof body. The parent
`Part3OriginalExceptionalChartIndex.lean`, blob
`a9a767f433c3b48a6cd9e057c3f35512d4ffb2a1`, identifies original chart
level indices and the actual exceptional mode. The complete original
`Part3OriginalPrescribedChartSpectrum.lean`, blob
`fc79ad8d2de109d661b52ba0e9bb83c3c8315e5a`, supplies
`chartSpectrum` and `full_chart_opposite_spectrum`. The complete signed
mode source, blob `628b660ed173c0e1180b3eccb26b992017cdbbd3`, supplies
the exact external coefficient and physical scalar.

The paper pin was checked afresh at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`:
`paper/source/manuscript-body.tex` blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching this chain; the
distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`
and its original (24) passage were reread. No manuscript revision or
parameter was exchanged. The prior external Pascadi v3, ABL v1 and gap
registrations and missing-supplier statuses remain unchanged; no new
external theorem is assumed in this packet.

## Validation and remaining obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including the finite chart proof and all predecessor candidates.
The exact import closure is not staged. `command -v lean` and
`command -v lake` each exited 1 with no output; no compiler was invoked
and therefore no compiler exit code or log exists. Config pins verified:
Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions could not
be verified. Stack 8192 KiB, virtual memory unlimited; no resource
limit was changed. `sha256sum` exited 0 with the source hash above.
Source scan `rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'`
exited 1 with no matches, not a compilation or transitive-axiom audit.
No CI was started. Prior AGENTS checks at root and docs were absent.

Next elaborate and replay the exact chain. Connect the actual
same-sign chart, including holomorphic channels; bound each nonexceptional
and continuous contribution; derive and pay the actual oldform removal
and raw n cost; supply the missing full-range m-side J and spectral gap.
Handle both zero lanes and actual cutoff tail separately, preserving the
distinct 14eta/28eta weights, 128C extension, original N threshold
order, and reserve payments.
