# P0 independent compiler memory

`verification/parts/p0/compiler_policy.py` owns the default/minimum Lean memory
budget: **12288 MiB (12 GiB)**. It is used by queue bootstrap, direct dependency
and target compilation, audit compilation, compiled-object restore, the full CI
runtime guard, and the standalone Round 6 type exporter.

To request a larger budget, set the environment variable before the existing
bootstrap/restore/run sequence, using the same value for every stage:

```bash
export P0_LEAN_MEMORY_MB=16384
```

An unset variable selects 12288 MiB. Empty, malformed, zero, negative, or smaller
values fail explicitly. The setting controls Lean's `-M` option; it does not
allocate RAM or change host/container limits. Native `leanchecker` has no `-M`
option and continues to use `LEAN_NUM_THREADS=2` under the single-heavy-process
lock. Compiler trust stays at `-t0`, compiler threads at `-j2`, and the existing
strict target/audit, kernel replay, axiom, type and dependency-pin gates remain.

Bootstrap embeds the selected budget and the shared argument normalizer in its
wrapper. It invokes a byte-identical copy of pinned Lake from the shadow toolchain
so Lake's executable-directory PATH ordering cannot bypass that wrapper. Caller
`-M`, `--memory`, and clustered resource flags cannot override the selected policy.

Bootstrap, run, and restore receipts record `lean_memory_mb` and the effective
`command_policy`; the relevant policy/normalizer sources are hash-bound. Run and
restore reject a bootstrap policy mismatch, so changing the environment after
bootstrap requires starting a new bootstrap with the selected setting.

Fresh-index signatures and restored producer commands must match the selected
policy. Old 4096 MiB entries are skipped and rebuilt, without modifying historical
receipts or relabeling old objects. A producer command with a later resource
override is rejected. Requested targets always rebuild, replay, and audit.

## Regression checks

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s verification/parts/p0 -p 'test_*.py' -v
```

The queue workflow requires these checks before toolchain installation. They run
the real entrypoint scripts with fake external tools in temporary projects,
covering argument propagation, the copied Lake path, higher budgets, policy
mismatches, and old/new artifact identities. They are entrypoint tests, not Lean
proof compilation or theorem acceptance evidence.
