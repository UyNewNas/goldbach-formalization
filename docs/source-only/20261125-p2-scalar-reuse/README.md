# Existing scalar extraction provenance

The accepted `ImbalancedChen/P2SmoothPositiveArgumentCore.lean` is preserved byte for byte. Its five source declarations retain the original fully qualified names and their exact definition/proof bodies:

| Original namespace | Moved declarations |
|---|---|
| `ImbalancedChen.Part5OriginalH430ClassicalSmoothOuterWeight` | `floorGate` |
| `ImbalancedChen.Part5OriginalH430ClassicalSmoothRealProfile` | `positiveArg`, `positiveArg_eq`, `positiveArg_pos`, `positiveArg_smooth` |

`SCALAR_EXTRACTION.json` contains the unchanged complete core text and hash, complete original import/namespace/open headers, the exact moved segments, declaration spans and hashes, original Git identities, canonical source paths, and the reversible byte operations.

## Canonical original owners

Only these two existing source-only files received the recorded postimages:

- `docs/source-only/20261112-resume/t07/classical-fixed-box/smooth-word/Part5OriginalH430ClassicalSmoothOuterWeight.lean`
- `docs/source-only/20261112-resume/t07/classical-fixed-box/smooth-word/hb-licence/Part5OriginalH430ClassicalSmoothRealProfile.lean`

Each postimage adds `import ImbalancedChen.P2SmoothPositiveArgumentCore` after its existing import lines and removes only its exact moved segment. All other original bytes are retained. The core declaration bodies match the two removed blocks exactly: 65 bytes for `floorGate` and 1,168 bytes for the documented `positiveArg` definition and its three theorems.

The `preimages/` directory preserves complete original files. The `postimages/` directory preserves the complete applied canonical files. Neither directory is a second active source owner. When those original modules are later installed, use these postimages and the existing core, preserving all original declaration names. Loading a historical preimage together with the core would duplicate ownership.

## Reversibility and validation

All offsets in the manifest are zero-based UTF-8 byte offsets and use half-open ranges. The forward transformation inserts the recorded import bytes at the recorded import boundary and deletes the recorded source block at its original byte span. To reverse it, first remove the inserted import bytes, then insert the preserved moved segment at its original offset. Both reversals were checked against the complete original byte streams.

The original source-only preimages also match their recorded immutable Git commit and blobs. The five moved declarations occur once in the core and no longer occur as declarations in either canonical postimage. The core's complete SHA-256 was checked before and after the changes.

This records existing source provenance and single ownership. It performs no mathematical reproof, compilation, kernel replay, or owned-declaration audit. The old owners remain source-only and receive no new formal credit. The core's historical source comment remains unchanged; its acceptance is managed separately by the coordinator.
