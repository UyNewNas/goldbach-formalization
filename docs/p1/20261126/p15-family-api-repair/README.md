# Exact Family source updater; separate from formal acceptance

This updater is published for execution as S, with R `0935516b9bd978a61248c81b59776d1eb47f6044` supplying the unchanged 22 declarations and six proof-only splices. Q `445201674271f9d9d6b846ecc634a10c4a0c6043` retains the AllK and Admissible acceptances and the original failed Family attempt. Pass the full publication commit of this script as `--source-commit`.

The updater first validates six exact R publications, the two original Q acceptance records, the joint 74-source / 72-dependency accepted prefix, and the unchanged Q evidence tree. It preserves the original 6,329,450-byte failed Family setup with exclusive creation, file and directory fsync, and an identity-bound archive receipt before removing only that failed active setup. It then invokes the unchanged Q remaining-eleven preflight on the original Family source: 157 sources, 146 dependencies, thirteen current owners (two complete and eleven fresh), and the same eighteen supplier evidence entries as the original Q later13 attempt.

Only the original pinned installer is used to replace Family with the 19,563-byte R source, SHA256 `4f58683304250030edbca5d1ed4f27eaa06c6de18fb0bbdcad4b2101df0ab109`. The exact source preimage is backed up. The remaining 359 source slots, all other artifacts across 160 watched modules, the entire Q evidence tree, the original accepted owners, runtime and dirty Git state are checked for preservation. The updater performs no Lean compilation or kernel audit and creates no owner acceptance.

Missing active setup is resumable only with the complete same-Q/R/S/script/source archive receipt. An already installed Family source, symlinks, identity changes, races, or other context changes produce HOLD. The source-after state is deliberately not silently accepted as a new installation.

## Local verification

`verify_updater.py` contains thirteen isolated tests. `UPDATER_TEST_LOG.txt` records all thirteen passing in 0.411 seconds. The tests cover durability before unlink, exact resume identity, missing or tampered receipts, incorrect setup basename, setup races and interruption recovery, source-after and symlink HOLD, original preflight failure preventing installation, the original single-source installer, the actual Q graph and supplier evidence counts, the R pins and six-splice reconstruction, collector tree encoding, and unrelated source/artifact/evidence/Git drift.

The entrypoint packet separately records 89 static and isolated checks. Its mathematical source anchor is R; the new Q priors remain Q. After successful installation, use the published current-corrections runner first for Family only, then for its `subsequent_11_targets`. Formal acceptance requires actual normal compilation, the existing named kernel / full-owned audit, and final stock readiness. These local tests and this publication do not establish that acceptance or complete P1.5.
