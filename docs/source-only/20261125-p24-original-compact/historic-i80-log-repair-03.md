# P2.4 historic I80 division and logarithm repair 03

Status: proof-script changes prepared; revised compilation and kernel audit pending.
Base: `5a91b30fef1b225d232a632ce671fad414a7dba4`.
Actual failures: P1 compact-03 job `job_a07d78e98e4e4a999137ad2e7ad046cc`,
captured in `p1-compact-03.log` in this directory. This repair task ran no Lean,
cloud compiler, numerical producer, or Git commit.

## Manuscript check and classification

Before editing, read the frozen 1106 manuscript's `Directed arithmetic` section
and equation `num:log-enclosure`, plus the compact/full-tail paragraph, from
`paper/release-20261106/en/numerical-appendix.tex` at manuscript commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. The existing local copy has SHA-256
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.

The manuscript requires directed integer interval arithmetic, a positive
denominator interval before division, and the logarithm remainder
`2*z^(2*n+1)/((2*n+1)*(1-z^2))`. The existing source's historical Q80 backend
retains its 32-term loop and denominator 65; the manuscript's separate paired
96-term calculation is not substituted for that backend.

The reported failures are formal-expression/API and strict-linter issues.
`I80` is a two-field structure with no registered extensionality theorem; the
failed `ext` calls therefore never reached their endpoint proofs. In
`unit_contains`, simplification moved the rational cast into a real quotient,
while the provided nonzero lemma only had rational type and the `unit` alias
was not unfolded. The remaining diagnostics identify proof tactics or simp
arguments that were already redundant. No new mathematical premise or omitted
estimate is needed for these repairs; they do not establish the absence of
other gaps elsewhere in the manuscript or downstream source chain.

## Changes

- `P2HistoricI80DivisionSoundness`: replace the two unavailable `ext` calls with
  `congrArg₂ I80.mk` and explicit lower/upper projection goals. Preserve the
  original signed four-corner argument; in the reciprocal equality each
  projection receives only its applicable minimum or maximum lemma.
- For `unit_contains`, unfold `unit` and derive `(Q : ℝ) ≠ 0` by casting the
  existing `Q_ne_zero`, so the unchanged `I80.raw_contains` theorem simplifies
  to the required real unit bound.
- Remove only the three `ring` tails reported redundant in division soundness.
- `P2HistoricLogPointInterpreter`: remove the reported unused `Pi.sub_apply`
  and `Nat.add_sub_cancel` simp arguments, the redundant `omega` after
  `congr 1`, and the three reported redundant `ring` tails. The sharp remainder
  proof, range reduction, rounding order and all logarithm guards remain intact.

All 47 theorem statements are unchanged. All 27 complete top-level definition
and structure blocks are byte-identical. No linter is disabled, no hypothesis
is added, and the two files' imports are unchanged. The existing complete CI
candidate index was checked narrowly for these two names and lists no matching
candidate; no full audit or broader source search was repeated.

| Module | Before SHA-256 | After SHA-256 |
| --- | --- | --- |
| `P2HistoricI80DivisionSoundness` | `fe0248cc8c7b6fb1fbcf476a924f172c41b0d17c5a51732b547635b7938c140d` | `3a64e682776875212a4ce4993244989a67dea098a297dea5ec02b6361607de41` |
| `P2HistoricLogPointInterpreter` | `26383ab34f68084d46b25e773ba70798827e0b14d7fb9e453fef7c1c6d699681` | `5533067993dd2bfa663f6962ef94904caede9a6c93384d80d120246c6f02726d` |

`git diff --check` passes. These source checks supply no revised compilation,
finite evaluation, kernel replay, or P2.4 completion credit.
