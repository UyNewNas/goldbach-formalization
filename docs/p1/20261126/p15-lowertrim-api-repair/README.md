# LowerTrim exact source updater

Status: **bound to actual AD; eight focused local checks passed; cloud installation has not been performed by this author.**

## Fixed identities and proof change

Original AC: `9f2013ad9cb9caac9cec03cb213d9949c4443c65`. Repair source publication AD: `e91af3a5c407bdeea243af7dd3c4248949d83e9b`. The future AE execution commit is supplied to `--source-commit`; the updater verifies its ancestry and exact published script and input bytes. No AE commit is assumed here.

The sole Lean splice replaces the failing final `linarith` with:

```lean
      exact (add_le_add (add_le_add hAP hM0) hM1).trans_eq (by ring)
```

It adds the three already-established bounds and normalizes their right-hand side. The two imports, eight declaration headers and all premises remain unchanged. The candidate is 14655 bytes / `f26884610a2d205368b347ed5fd80947c91c5973a6750bc0b333cb57dcb42106`; the AC preimage is 14601 bytes / `82cfc7b75510076d0ded95130504639cde2ee39d38cff4133964a092d5cbcf54`.

Root executed the whole-module no-output probe `job_abfb9ce81e7749c290d6f61c385aa749` successfully. Its exact 2221-byte raw report is pinned in `UPDATER_INPUTS.json`. That probe is not a normal-pass or full-owned kernel receipt.

## Runtime gates

The updater uses the unchanged original AC runner and helpers plus the actual AC collector. It revalidates Synthesis at its original AC run0 identity, with 28 owned/28 public declarations, and preserves the later5 same-AC reuse and actual LowerTrim failure. The accepted prefix is 112 sources/111 dependencies with two suppliers.

The unique failed LowerTrim setup is archived under its exact basename with exclusive creation, file and directory fsync, a receipt bound to AC/AD/AE/script/source and all six document pins, and a final stat/byte recheck before unlink. An absent setup can resume only through that same exact receipt. An already-installed source_after is held.

While the source still equals AC, the original reader must pass the remaining4 preflight: 157 sources, 153 dependencies, five current owners, 26 unchanged original supplier bindings and 160 watched modules. Only then does the original single-source installer write LowerTrim and preserve its exact backup. The wrapper protects 360 source slots, 3360 artifact slots, all seven AC/AA/Y/W/U/S/Q evidence trees, original receipts, runtime and dirty Git state.

## Inherited Synthesis failure evidence

LowerTrim's published candidate has no `prior_failed_whole_module_probes` field. The old Synthesis-specific candidate equality was removed from the adapted wrapper. It would describe the wrong candidate. The original Synthesis probe0 source, log and raw report remain strictly pinned at their original paths, alongside the inherited Mean and Synthesis installation receipts. All five records participate in the existing before/after retained-evidence checks. General identity, receipt and same-source checks are unchanged. `DELTA_REVIEW.json` records this scope-specific change explicitly.

## Local verification and deliverables

`test_lowertrim_updater.py` passed all eight checks, actual exit code 0; `UPDATER_TEST.log` contains the complete result. These checks use temporary fixtures, the original installer/primitives, and actual AC/AD graph and publication data. They cover archive durability and recovery, wrong identity/basename rejection, source_after/symlink holds, a failed original preflight blocking installation, exact single-source installation, and all six AD bindings.

The local checks did not execute cloud installation or actual cloud AC remaining4 preflight, invoke Lean, run Git, or create a new acceptance. Normal and full-owned kernel acceptance remain future work. **P1.5 is not closed.**

Production script: `apply_lowertrim_repair.py`, 33309 bytes, SHA256 `dbf67e2bce3b2059c3f1833e110c80005f486e22704ac431addedc99732dbc6f`. Supporting files: `UPDATER_INPUTS.json`, `test_lowertrim_updater.py`, `UPDATER_TEST.log`, `LOCAL_VERIFICATION.json`, and `DELTA_REVIEW.json`. `build_updater_template.py` is an unbound construction helper, not the production entrypoint.
