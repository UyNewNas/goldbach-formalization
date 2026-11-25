# Part A current-root verification

**PASS_CURRENT_ROOT_BUILD_REPLAY_AND_DECLARATION_AUDIT** — see [`RECEIPT.json`](RECEIPT.json).

The actual compilation source is [`c34982b300858968ae78403d3fbd306b88236c10`](https://github.com/UyNewNas/goldbach-formalization/commit/c34982b300858968ae78403d3fbd306b88236c10). Later evidence and documentation commits preserve exactly the 69 production sources, root, toolchain, dependency lock, Lake configuration and audit-source bytes bound by the receipt.

| Stage | Exit code | Runtime |
| --- | ---: | ---: |
| build | 0 | 164.39 s |
| checker | 0 | 488.62 s |
| types | 0 | 22.60 s |

The kernel stage replays exactly 69 selected production modules and the new `ImbalancedChen` root. The complete serialized declaration census contains 1,880 declarations; every record agrees with the retained historical union, including full types and transitive axioms. Source/configuration/input-object snapshots before and after replay and audit agree on all 55,440 entries. The allowed transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Retained files

- [`COMPILER_TASK.json`](COMPILER_TASK.json): observed successful task status, exact driver command and resource accounting.
- [`evidence.zip`](evidence.zip): exact `build.log`, `checker.log`, `types.log`, `OBJECTS_BEFORE.json`, `OBJECTS_AFTER.json`, and `ENVIRONMENT.json`; no reconstruction or summary replaces those bytes.
- [`RECEIPT.json`](RECEIPT.json): individual member hashes, archive hash, source/configuration bindings and final acceptance counts.

From the repository root, validate the retained evidence with:

```bash
python3 verification/part-a/verify.py
python3 verification/part-a/verify_current.py
```

These commands validate the retained records against the current source tree; they do not rerun Lean. The exact executed build, replay and declaration-export commands are in the task record and archived `ENVIRONMENT.json`. Dependency revisions remain locked by `lake-manifest.json`; existing matching caches were reused during the build.

A shallow checkout must also retain the execution commit for the Git source binding; fetch it with `git fetch origin c34982b300858968ae78403d3fbd306b88236c10` if necessary.

This acceptance concerns Part A. It does not discharge the complete main theorem's actual `hLower`/`hUpper` obligations.
