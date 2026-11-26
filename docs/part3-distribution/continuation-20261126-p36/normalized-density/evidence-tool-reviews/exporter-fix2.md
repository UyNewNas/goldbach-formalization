# Exporter targeted follow-up

- Moved the raw `lake-manifest.json` digest to the export-time inputs.
  The original report records dependency pins. Package checks and the
  combined snapshot map still cover the same bytes.
- Bound a selection manifest inside the original project to its frozen
  Git blob when that relative path is tracked at the source commit.
  The summary reports the Git binding, generated file binding, external
  file binding, or omission. Generated and external manifests retain
  their report digest and per-entry validation.

Exporter SHA-256 is
`d2a13e3fa2d4e290b49682d222f6d288ac416bc99e25ccdd2f8dd7d37b55d692`.
The targeted patch is `exporter-fix2.diff`, SHA-256
`d2ae84af9783f0f8b0bd8030506b73b102d170f008f85ecfd6946f88ab9896e2`.

From the normalized-density directory, the two regressions ran with

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest -v \
  test_export_verified_increment.HistoricalRun.test_real_historical_graph \
  test_export_verified_increment.HistoricalRun.test_refuses_rehashed_mutation_of_frozen_tracked_selection
```

Both tests failed before the fix. The historical Lake-manifest SHA was
absent from the export-time map, and a whitespace-only modification of
the tracked selection survived when supplied with its recomputed report
SHA. Both tests passed after the fix in 5.001 seconds. The first regression
also verifies exact equality to the historical combined snapshot map and
preservation of the original dependency pins.
