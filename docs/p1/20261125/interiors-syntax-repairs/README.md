# Full87 interiors: scoped-option parser repair

These four source-only candidates move seven unchanged documentation comments
inside their existing two-command `set_option ... in` wrappers, immediately
before the original private theorem. All other source bytes remain in the same
order. No declaration, definition, proof, rational coordinate, coefficient
bound, import or option value changes.

The actual normal task is `job_7026c3296d9a40fd88be8090f6460618`, using source
commit `4f7a975211bdbdccc76adc14734aa2de4a13b6ad`. All four targets failed, with
seven errors in total, each `unexpected token 'set_option'; expected 'lemma'`.
The source locations below and the four complete-log SHA256 values in the
manifest were independently read from the lossless saved task-output pages.
The parent exported complete normal logs in task
`job_9af7b5f0b90146a5a9921dbd6be55eff`; no repaired candidate result is inferred.

| Module suffix after `P4AOriginalFull87` | Original doc-comment end / reported error locations | Candidate SHA256 |
| --- | --- | --- |
| `H3Interiors` | 49:63 and 60:56, actual parser errors | `8f8fcdbb35f7c0ef3942fcf58968cde5bc4f00ba5f403a4c39e643cdc39cd024` |
| `SeedNineFiftyInteriors` | 74:56, actual parser error | `68c4c1d4e97fbcd674dedee1570ccc50d6fee07f959a3ee960ec6274b5247282` |
| `H5H7Interiors` | 63:63 and 75:71, actual parser errors | `5a56878a04f2723ad2020ad389b5b7b0ec3ecc8eeabc8f4076bdcdbdf979f483` |
| `DescAscPairInteriors` | 84:77 and 103:80, actual parser errors | `1bcd2f0292f56779e889aef3ab4ded625b8b4058a0384acfb5227a3d2e5cc4ff` |

The prior form places a declaration doc comment directly before `set_option`.
The candidate preserves that complete comment and instead places the two
unchanged local option commands before it, so the comment attaches to its
original declaration. Each wrapper still applies to the same private literal
proof. The ten existing `decide +kernel` bodies and all earlier expression
repairs remain byte-identical. No resource override is added.

`SOURCE_REPAIRS.json` records the four exact source preimages, candidate hashes
and Git blobs, the seven original comment texts and declaration names, and the
reported diagnostic boundary. The comparison snapshot is
`e421f8cd5aad3d9c53933dec3c77bb530bb52f8c`; the prior expression-candidate
provenance remains in `../full87-other-interiors/` without modification.

Static checks confirmed that removing only those seven unchanged comment
blocks from each before/after pair gives exactly identical bytes. Every file
also retains its original byte count, line count and option list, with no
remaining doc-comment-before-scoped-option pattern. `git diff --check` passed.
These are source checks, not a Lean parser invocation or acceptance result.

The actual error is a command-boundary problem and supplies no evidence of a
mathematical gap. The conclusions remain the original continuous-source
interiors. Normal compilation, kernel checking and full-owned acceptance of
these candidate hashes are pending; no saved87 witness, prime realization,
integral evaluation or P1 completion is claimed.
