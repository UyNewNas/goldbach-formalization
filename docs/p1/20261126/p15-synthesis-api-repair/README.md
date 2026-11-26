# SharpPrimeSynthesis exact updater

`apply_synthesis_repair.py` is frozen at 33049 bytes, SHA256
`be8d6519aa580ae462e6dfba0775b57651bf2b20c15fdd16ba56e457aab92953`.

## Bound identities

- Failed original source AA: `ae373b971d2b88f97532dc883d835751dd10c67b`.
- Published repair AB: `60e6b6e18fbda5f6b0e997d15392b32100e854d9`.
- Execution AC must descend from AB, contain the exact executing script, preserve the six pinned AB inputs, and contain the exact repaired canonical source.
- Mean keeps its original AA run0 acceptance, 22 owned / 22 public, and same-AA run1 reuse. Earlier prior owners keep their existing identities.

The sole source update is `ImbalancedChen/P5OriginalSharpPrimeSynthesis.lean`:
14458 bytes / `9d8b3b273ade3bf3a35aff7469e16f5fac24d9896eb31171c48c0f04328a8cd7`
to 14462 bytes / `990ceec9aae74a67c7e1b25e94d66b33644214e1fc0bb3193275ed1b09c50322`.
One continuous proof splice uses `abs_add_le` and `add_le_add` with `le_rfl` to preserve
the left-associated sum. Three imports, eighteen declaration headers and all premises
remain unchanged.

## Actual probe history

Probe0 (`job_2cfa137d1e284d9da5e3470f88cb0438`) failed after resolving `abs_add`, because
`add_le_add_right` accumulated on the opposite side in this scope. Its source, metadata,
script, raw result and task remain archived locally. The updater additionally preserves
the exact cloud probe0 candidate, log and raw result through its existing retained-file
checks. The failed probe is recorded as a failure in the candidate metadata.

Probe1 (`job_d98b1db30a4d406887de810840109325`) succeeded with the final source under the
original AA serializer and guard, without output objects. Its raw report is 3645 bytes /
`42c93650259a85f6709d46c80286168f59ec60489f9d19b02816ff4c30d06a1b`.
This is whole-module typechecking; no new normal/kernel owner acceptance is claimed.

## Installation gates

The unchanged AA reader and frozen AA collector helpers revalidate Mean at 108 sources /
107 dependencies. The updater preserves all 360 source slots, 160 watched modules and
3360 artifact slots, full AA/Y/W/U/S/Q evidence trees, original retained receipts, runtime
context and dirty Git. Only the Synthesis source and its exact failed setup may change.

The archive basename is `P5OriginalSharpPrimeSynthesis.setup.json`, with original setup
6417017 bytes / `42acce65ed6a2b300809309fd909236cd4de13bfb9b5abe1cf27baac10dca87e`.
Exclusive creation, file/directory fsync, a bound receipt, and a final stat/byte check
precede unlink. Missing setup requires an exact same-AC archive receipt bound to the
script, AA/AB/AC, both source fingerprints and all six publication inputs. Source-after
is held. A complete installation is not silently treated as a resumable preimage.

After archive removal, the original AA remaining5 preflight runs against the old source:
157 sources, 152 dependencies, six current owners, and the same 25 original supplier
bindings. Only then does the original helper install one source with an exact preimage
backup. The updater runs no normal builds, Lean or kernel checks.

## Local verification boundary

The eight focused local checks passed in 0.423 seconds. `UPDATER_TEST.log` contains the
exact output. These checks cover existing archive/recovery/rejection paths, the original
installer, actual graph and publication pins, failure before installation, and probe0
retention bindings. They are local fixtures and static checks, not a cloud installation
or an actual AA remaining5 preflight.

`UPDATER_INPUTS.json` lists the six actual AB pins. `LOCAL_VERIFICATION.json` binds the
frozen script, tests and log. `build_updater_template.py` emits an unbound HOLD template;
it is a construction aid, not the frozen execution entrypoint. Whole P1.5 remains open.
