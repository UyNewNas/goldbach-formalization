# Part 3 — ordinary prime-AP target: compiler fixes and independent acceptance lane

Status at intake: **candidate proof now builds; independent strict three-gate validation pending**. Do not count the thirteen source theorems as compiler-accepted until the new isolated lane produces a matching successful receipt. The comprehensive Part 3 workflow is still red.

## Fixed source, inherited provenance

- Parent actual remote P3 head: `aa4c819b79054493ac789168d9fdcdce97142fea`.
- Exact proof-fix checkpoint: `948b613b25d6492c207f2c4ee234c7be7e0761b8`; branch `chatgpt/chen-p3-distribution`.
- Fixed target Git blob: `ImbalancedChen/Part3PrimeAPDistribution.lean` = `13502fc254e57776f485822a56e529b68e835440`.
- Fixed definition target Git blob: `ImbalancedChen/Part3DistributionTargets.lean` = `178e0fa5acc4f1c5b77b1ff0a3d6b933c9ef3fe6`.
- Common proof baseline `1a80c1bcce67886f699d097fc37fd245cd3620bf`. Manuscript `ba6ec11d800eccc54406490631895e174de85766`. Frozen Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, goldbach `09b97db5764ade1246bfb77206baa1b124760958`.
- No mathematical statement, constant, exponent, modulus range or quantifier was changed in the two production source edits. No new axiom, sorry or unsafe escape was introduced.

## Real compiler transition

Previous exact-head [P3 run 38317730341](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38317730341) built the complete pinned unconditional BV supplier and passed its exact strict/replay/full audit gates (four owned theorems, 6,446 actually resolved import objects). The same run then failed on two real target elaboration errors: a residual definitional-equality goal at `Part3PrimeAPDistribution.lean:40`, and an underdetermined `Finset.le_max'` application at line 55. It also failed to elaborate the grouped record binders in `Part3DistributionTargets`, producing a cascade of projection errors.

The checkpoint `948b613...` added the final definitional `rfl`, made the prefix-max membership proof elaborator-directed, and gave the structure fields their independent explicit types without changing the fields' mathematical types. In [P3 run 38332659386](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38332659386), the standard Lake build **succeeded** for both `Part3PrimeAPDistribution` and `Part3DistributionTargets`, as did the inherited `Part3LongSlotDistribution` and `Part3LongSlotNormalization` builds. The unconditional BV supplier's strict compile, original checker replay and full audit also passed again. These outcomes remove the prior first-import diagnostic as the present GitHub runner's immediate blocker.

The full run nevertheless exited 1 at its aggregate build. Actual remaining diagnostics concern `Part3CurrentLowerDistribution` (lines 148, 265, 374, 385) and `Part3RoughAuxiliarySW` (starting at 76, 139–159 and later lines). `Part3RoughAuxiliarySWNormalization` cannot be accepted before its prerequisite. **No local strict target compile, target replay, target owned-axiom inventory or compiler types were emitted by the failed aggregate verifier**; a successful ordinary Lake build alone must not be labelled three-gate acceptance.

## New independent narrow acceptance lane (added after the preceding CI run)

- `verification/verify_part3_prime_ap_local.py` builds only the same `Part3PrimeAPDistribution` target, strictly recompiles its original source with `-t0 -DwarningAsError=true`, replays the production object with the pinned stock `leanchecker`, strictly compiles/replays the audit, and hashes the actual imported objects reported by `Lean.findOLean`. It preserves original stage logs, exit codes, object copies, compiler declaration types, per-declaration transitive axioms and source hashes.
- `verification/parts/p3/Part3PrimeAPDistributionAudit.lean` derives the full defining-module inventory from the Lean environment and crosschecks all serialized legacy constants, including private/generated names. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
- The existing `part3-distribution.yml` retains its unconditional BV supplier verification, complete Part 3 validation, exact-head outcome gate and CI artifact upload. The new leaf lane is inserted before the complete verifier and is **not a bypass**. Its own acceptance is **PENDING_NEW_RUN** until the matching new-head GitHub Actions job and uploaded evidence have passed.

## Next small action

1. Inspect the new-head CI for the isolated prime-AP strict/replay/audit lane; fix precisely reported Lean or verifier errors, keeping complete original logs and source/tool/object/import identity binding. Promote the leaf only on an actual PASS receipt. Do not re-run all frozen goldbach imports separately when matched CI objects exist.
2. Keep `Part3DistributionTargets` as a separate later strictly audited definition module; its ordinary compilation succeeded but it has no proof credit yet.
3. Once this leaf is accepted, address one real `Part3CurrentLowerDistribution` compiler error batch and the separate rough auxiliary input. None of the ordinary BV results are a `theta_*=599/1000` high-physical-modulus, prime-product or nonzero-additive-phase estimate.

This handoff contains **no invented strict compile or replay success for the prime-AP leaf**. The cited runner URLs retain the raw CI logs and attached original evidence artifacts; artifact retention is finite.
