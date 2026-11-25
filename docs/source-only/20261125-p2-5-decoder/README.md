# Original saving16 decoder/schema extraction

Status: **source-only, not compiled, not installed**. This package does not grant parse-success, Q96, integral or P2.5 credit.

## What is moved

The fixed production `ImbalancedChen/P2OriginalSaving16FiniteArchive.lean` is 10,909 bytes with SHA256 `72824a189dd65b29f0f340918ff867a1e905959e8e60e683a797226923d7e01d`. Its following nine commands are copied byte for byte into the same `ImbalancedChen.P2OriginalSaving16OriginalArchive` namespace in the new `P2OriginalSaving16Decoder` owner:

- `parseInteger`, `parseRational`, `rationalField`, `rationalArray`, `rationalArrayField`;
- `SimplexRecord`, including `deriving Inhabited, DecidableEq`;
- `decodeSimplex`;
- `CellRecord`, including its original documentation and `deriving Inhabited`;
- `decodeCell`.

The complete contiguous region, including its separators, is 3,945 bytes with SHA256 `96b379646470b269625950eed1829d85e36f198291e832c8741bc8353e4a0b0d`. `DECLARATION_IDENTITY.json` records each command's source/destination byte range and hash. No function, schema field, error string, literal, rational operation or algorithm has been rewritten. The original six imports, four open declarations and noncomputable context are retained conservatively. The new owner contains no theorem or closed guard and imports neither FiniteArchive nor OriginalInput.

A bounded search found no separate saving16 decoder/schema owner. The same nine-command region is already present byte for byte in the older P14/P15 original archive; those owners still include the closed guards. `SOURCE_SELECTION.json` records those exact sources and explains why the different M19 decoder is not substituted.

## Reuse the existing OriginalInput extraction

The unchanged existing source is:

`docs/source-only/20261125-p2-5-original-input/postimages/ImbalancedChen/P2OriginalSaving16OriginalInput.lean`

It is 1,714 bytes, SHA256 `792a5adf50263cfc1a0f67fb3d088c7612910388e4d1fa65db45c3c50065aca5`. Its existing package and independent review are not overwritten or reimplemented here.

The combined FiniteArchive postimage in this package is derived in two independently checked ways:

1. From that package's already reviewed FiniteArchive postimage `c225f1c0f9c7dfcd28a2a94648bf2113152e9430e4234d0f5fc6488a089ed15f`, add only the Decoder import and delete the exact nine-command region.
2. From current production `72824a...`, delete only the previously audited 420-byte reader, 415-byte originalText command and 3,945-byte decoder region, then add only the OriginalInput and Decoder imports.

Both constructions produce exactly the same 6,231-byte combined owner, SHA256 `9db41aa0553a3c5020acceffa3f1bc91529f1382f7dc6c6d57ba96c073e6d627`. The new Decoder is 5,257 bytes, SHA256 `e1b23e3de928a97c411d1c6aa73f2059b204d7b9f297105edcd591916b9aee80`.

## What remains in FiniteArchive

All 26 remaining source commands (25 named declarations plus the anonymous simplex-validity Decidable instance) retain their complete original text. This includes the four original closed guards:

- `original_parse_success_tag`;
- `original_simplex_operations`;
- `original_q96_aggregate`;
- `original_counts`.

Their original `decide +kernel` bodies, 39,741-simplex/39,381-active8 count targets, and separate per-simplex Q96 floor computations are unchanged. The `archive` definition still uses the original `getD default` fallback, and the original parse-success guard and constructor-elimination theorem are still required to rule out failure. **An Inhabited record or default value is not evidence.**

## Independent verification and eventual integration

`SOURCE_CLOSURE.json` supplies three source-only overlay graphs:

- Decoder alone: three project modules, including the existing Q96FloorCore and SourceJson dependencies;
- OriginalInput and Decoder together: four project modules, without importing FiniteArchive;
- the eventual combined FiniteArchive: five project modules.

An isolated verification may install and compile only the two new owners, using the four-module graph, while leaving the old FiniteArchive unimported. That can check the reader/schema/decoder owners without executing the four archive guards. OriginalInput still reads all fourteen original raw files, so the same exact input, source, object and physical-identity binding remains necessary.

For eventual FiniteArchive consumption, its combined postimage must be used with those exact two owners to avoid defining the moved public names twice. Neither installation nor verification is performed by this package.

The new Decoder owner must undergo strict compilation, independent kernel replay and a complete actual owned inventory audit, including structures, deriving instances, projections, constructors, recursors and every private/generated companion. OriginalInput needs its own corresponding audit and original-input binding. The combined FiniteArchive still needs its unchanged closed proofs and final complete owned audit. Public source-name and command-byte identity do not replace those checks, and no fixed generated-declaration count or helper exemption is introduced.

## Files

`before/` stores the original finite owner. `after/` contains the new Decoder and combined FiniteArchive postimages. `SOURCE_PATCH.diff` shows the complete proposed source change; `DECODER_DELTA_FROM_ORIGINAL_INPUT.diff` shows only the additional decoder extraction relative to the previously reviewed input extraction. The identity, selection and closure JSON files record the exact boundaries and source hashes.
