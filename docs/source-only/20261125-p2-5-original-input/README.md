# Saving16 original-input extraction candidate

**SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.** Production files have not been changed.

This package separates the current canonical raw input from the closed parse and numerical guards in `P2OriginalSaving16FiniteArchive`. It mechanically moves exactly two existing top-level commands into `P2OriginalSaving16OriginalInput`: the `originalSaving16Text%` elaborator and `originalText : Fin 14 → String`.

There is one named String-valued function containing fourteen reader invocations. There are not fourteen separately named String definitions. The original namespace `ImbalancedChen.P2OriginalSaving16OriginalArchive`, the complete command headers and bodies, `open Lean Elab Term`, and the noncomputable context are preserved. The reader's already-recorded `IO.FS.readFile` compatibility repair is retained. No new reader, codec, parser, numeric operation, binding lemma, or closed target is introduced.

## Files and reconstruction

- `preimages/ImbalancedChen/P2OriginalSaving16FiniteArchive.lean` is the exact current 72824a… production source.
- `postimages/ImbalancedChen/P2OriginalSaving16OriginalInput.lean` contains the two original commands with only the imports and namespace/context needed to host them.
- `postimages/ImbalancedChen/P2OriginalSaving16FiniteArchive.lean` differs from the preimage only by one added import and deletion of those two exact command byte ranges. All other bytes remain unchanged, including historical module comments.
- `extraction.diff` records both file changes.
- `DECLARATION_IDENTITY.json` gives exact byte offsets, line ranges, full command/header/body hashes, ownership boundaries, and the fourteen original input hashes from the existing manifest.
- `SOURCE_SELECTION.json` records the bounded reuse search, dependency changes, and the unimplemented conditional binding plan.

## Dependency effect

The new raw-input owner imports only `Lean` and `Mathlib.Data.Fin.VecNotation`; its project-source closure contains only itself. It imports neither the failed finite guards nor SourceJson, Q96FloorCore, the real atlas, or custom native project sources. No new census of Mathlib's external transitive imports is claimed.

The existing finite root grows from three to four project modules because it imports the new owner; its mathematical definitions, decoders and guards stay unchanged. Its existing raw-input name remains available through that import. `originalId` does not need to move.

## Acceptance and remaining work

This is a source-byte-preserving module relocation, not compiled declaration or kernel-term identity evidence. The elaborator's generated owned names may change with its module owner. Future acceptance must inspect every generated/private owned declaration, not just the two source commands.

The unchanged `originalText` body still reads all fourteen original witness files during elaboration, totaling **93,508,187 bytes**. Selecting index zero later does not avoid those fourteen input reads. No runtime or memory feasibility claim is made, and the single-cell diagnostic is not an all-fourteen-input acceptance record.

If the separate String/Char diagnostic succeeds, the next unimplemented equality is `oldString00 = originalText (0 : Fin 14)`. The existing local equality could then compose with it using transitivity. No such lemma is included here, and the diagnostic's success is not assumed. Existing generic SourceJson character-input lemmas can transport that equality once accepted; they do not establish parsing or typed-decoding success. `decodeCell` and `CellRecord` remain coupled to FiniteArchive in this minimal extraction.

No Lean, checker, Git, cloud operation, production install, cache update, or numerical replay was performed for this package.
