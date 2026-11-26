# Endpoint exact updater: local verification and execution boundary

`apply_endpoint_repair.py` is bound to repair publication X `09bf8a02b4c96798930abe2826cfb27529c01ad3`. Its six exact publications include the two-splice source record, actual successful whole-module probe, original W failure metadata, original W acceptance read, unchanged collector helpers and Smooth public acceptance. The source changes from 13,623 bytes / SHA256 `73c45c9e3418847e4a2e2a685429ff3a44053fff055f99bc91460da59d23364a` to 13,668 bytes / SHA256 `1a9baa44f798fba58671d473f3be4def2eaefd6c758413e0f7d60b3238edef3c`. All nine declaration headers and imports remain unchanged.

The updater loads the original W reader and frozen collector helpers. It revalidates Smooth at its original W run0 acceptance, including the later same-W reuse, using the 130-source / 129-dependency prefix and the existing full acceptance API. Smooth remains W; the ten earlier priors retain their own identities.

Only the exact failed Endpoint setup is archived and removed. Exclusive archive creation, file and directory fsync, an identity-bound receipt, and a fresh stat/byte comparison precede unlink. Missing active setup requires the exact same-execution archive receipt. An already installed source-after, invalid identity, wrong basename, symlink, or context change holds the operation.

Before changing source, the updater calls the unchanged W preflight on the seven remaining targets: 157 sources, 150 dependencies, eight current owners (one complete and seven fresh), and the same 23 supplier evidence entries as the original later8 result. Only the original installer writes the single Endpoint source and exact preimage backup. The other 359 source slots, other artifacts across 160 watched modules, complete W/U/S/Q evidence trees, runtime and dirty Git state must remain unchanged.

## Local verification

`LOCAL_VERIFICATION.json` binds this script, its eight focused tests, test log and input configuration. `python -B test_endpoint_updater.py` passed all eight tests in 0.369 seconds. The checks cover publication pins and actual graph counts, archive durability and recovery, rejection paths, preflight-before-install ordering and the original single-source installer. The parent independently reviewed the wrapper changes and found no new blocker.

These are local static and isolated fixture checks. They did not run the real W preflight in P1, install source, execute Lean, run a kernel audit or produce owner acceptance. The actual probe is separately recorded in X and likewise does not establish normal/kernel owner acceptance. P1.5 remains open.

Publish the exact frozen updater as execution Y, then use `--source-commit <full-Y-commit> --apply`. The script requires its bytes to match that Y publication and Y to descend from X. Its apply path includes all preconditions and the real original W remaining7 preflight; a separate check execution is optional. Formal acceptance belongs to the subsequent published runner.
