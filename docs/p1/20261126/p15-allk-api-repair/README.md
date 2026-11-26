# Exact AllK source repair and failed-setup preservation

`apply_allk_repair.py` is a separate source installer. Its execution identity is the full publication commit Q supplied via `--source-commit`; its source repair and public evidence are pinned to P `b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f`. Its actual failed normal evidence and original PerGroup acceptance remain at O `dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d`. It does not compile Lean, run the kernel, or grant owner acceptance.

The updater binds its exact published bytes; all 360 original sources; original O RESULT, WORKER, context and Git records; the complete original PerGroup normal/kernel/full-owned acceptance (68 owned / 58 public); the successful full-module probe; 160 watched modules and all 21 artifact slots. Only the known 6,329,098-byte AllK failed setup may be retired. Its SHA-256 is `14330c5ee87da605a861559cdd3adb035302ef8e4aa90d3f20cf467b751e0b87`.

The setup is first copied with O_EXCL, verified and fsynced together with its directories. A Q/script/P/O-bound receipt is saved and fsynced before rechecking the active inode, mtime and bytes and unlinking precisely that active setup. Missing setup requires the same updater publication's complete durable archive; an already-installed repaired source holds for inspection.

With the original source still installed, the unchanged O driver performs its actual remaining-13 preflight. Only after this succeeds does the unchanged original installer make the two exact proof splices. Every other source, all other artifact slots, the old evidence tree, original acceptances, runtime configuration and dirty Git state must remain unchanged.

Invocation after publishing and retrieving the exact Q script:

```sh
python3 -B apply_allk_repair.py --source-commit <PUBLISHED_Q_COMMIT> --apply
```

The separate current-corrections runner can be used only after inspecting the successful actual `SOURCE_REPAIR_RESULT.json`. Its first selection is AllK only. This packet records 15 passing local isolated checks; it does not substitute fixtures for actual runtime preflight or new normal/kernel/full-owned acceptance.
