# Review of the frozen R14 context export

This package preserves the input context needed to reuse the existing P2 objects. It adds no theorem acceptance and does not qualify a future P1 search path.

The root review independently decompressed the external snapshot and checked all three original file lengths and SHA-256 digests against `CONTEXT_EXPORT.json`:

| Original artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| Cell1 affine normal projection | 356280 | `5e2f0856b5f2df8c4e455cb5320075b743255a441b3d19262a63ec7a50ce3a4c` |
| External snapshot | 20904189 | `ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27` |
| Native qualification | 215179 | `b03c1da0f619c1ad0acd1d00ff453d17fecd6e9dcc094429c8519e3a51fa1ac9` |

The parsed normal projection contains 288 explicitly qualified records and six explicitly unsuccessful records. An existing file for one of those six modules is not an accepted input. The projection remains tied to R14 source commit `f7620a41c082b6969749bcf38370687aa26ffd29`; later repairs require their own selected source and actual accepted records.

The external snapshot contains 70383 physical-file records, 11516 resolution entries, and 515 native modules. The original qualification records 515 qualified native providers, zero blocked providers, eight ABI checks, and eleven runtime checks. It explicitly claims zero new compilation or kernel credit. Those statements and their original scope have been preserved.

Relocation requires comparing actual destination bytes and resolution order. The source snapshot, an unchanged package revision, or a matching sample alone cannot qualify a relocated environment. Existing successful project proofs are to be reused only with their source, object, dependency signatures, applicable owned receipts, and original environment qualification intact.
