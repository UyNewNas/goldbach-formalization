# MeanCorrection exact updater

`apply_mean_repair.py` is frozen at 30777 bytes, SHA256
`51443890bd2e14c00f0a01627afd6fcc76ba260e31533e29fbbd9f7dee74e983`.

## Bound identities

- Failed original source Y: `f6e63d1b9785be30a607fb0ff55151ca95d1a6aa`.
- Published repair Z: `bde4a91307cb5e5872b6fc3c1e4a1520908b10c2`.
- The execution commit AA is provided at runtime. It must descend from Z, contain the exact executing script, preserve all six pinned Z inputs, and contain the exact repaired canonical source.
- The original Y reader and collector helpers revalidate Endpoint's first acceptance and later same-Y reuse. Endpoint remains 24 owned / 24 public, with original run and receipts.

The sole source update is `ImbalancedChen/P5PrimeDivisorMeanCorrection.lean`:
17065 bytes / `1da7fe8cde7360ba7748bf1c3f85e00ad1da470a15638eb8cf4b6a32ffdfc3ee`
to 17171 bytes / `efb2138a0a1837c60ab5484afee7d884364dbf118f2753a3690881baebb4c02d`.
The three proof splices preserve all four imports and sixteen declaration headers.
The whole-module no-output probe succeeded under the original Y serializer and guard in
`job_83d359ffbf754a88ad53a15aefbb4a13`. That probe is not a normal/kernel owner acceptance.

## Installation gates

The updater revalidates the original Y accepted prefix at 110 sources / 109 dependencies.
It preserves all 360 source slots, all 160 watched modules and their 3360 artifact slots,
full Y/W/U/S/Q evidence trees, old receipts, runtime context and dirty Git state.
Only the Mean source and its exact failed setup may differ after installation.

The setup archive has the exact basename `P5PrimeDivisorMeanCorrection.setup.json`.
Its original fingerprint is 6416378 bytes /
`e51ad84eea0a873a4414e09a754beaaf1eb4caca2632d7c56a8bc2a0921d4675`.
Exclusive creation, file and directory fsync, a bound receipt, and a final stat/byte check
precede unlink. Missing setup is permitted only with an exact matching archive receipt
bound to Y/Z/AA, this script, all six inputs and both source fingerprints. Source-after
is held rather than accepted as a new installation.

After archive removal, the unchanged original Y remaining6 preflight must pass on the
old source: 157 sources, 151 dependencies, seven current owners and the same 24 original
supplier bindings. The original source installer then writes exactly one source and
keeps an exact preimage backup. It does not run Lean, normal builds, kernel checks or
an alternate acceptance implementation.

## Local verification boundary

The eight focused checks in `test_mean_updater.py` passed (0.547 seconds); their exact
output is in `UPDATER_TEST.log`. They exercise the existing archive/recovery/rejection
paths, actual original helper installation, original graph and input pins, and failure
before installation. The preservation fixtures are local and do not stand in for a
cloud installation or an actual Y remaining6 preflight. No cloud action was performed
by the updater author. Mean owner acceptance and whole P1.5 closure remain unclaimed.

`UPDATER_INPUTS.json` records the six actual Z pins. `LOCAL_VERIFICATION.json` binds the
frozen script, tests and log. `build_updater_template.py` is a construction aid that
emits an unbound HOLD template; it is not the frozen execution entrypoint.
