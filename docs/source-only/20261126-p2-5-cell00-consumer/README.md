# Cell00 canonical consumers: source selection candidate

Status: **source only; these consumer modules have not been compiled, replayed,
or audited.** No P2.5 completion credit is claimed.

This package retains the three existing `P2Saving16Cell00Decoded` API names but
sets `decodedCell00` to the named typed payload. Its exact decoder theorem
composes the full AST identity with `rawRoot_decoded`; the success Boolean then
follows by rewriting that equality. The replacement performs no whole-decoder
decision and introduces no fallback record or new success premise.

`P2Saving16Cell00OriginalParse.lean` is a byte-for-byte copy of the existing
consumer. It must be selected together with this replacement `Decoded` module.
Its theorem `cell00_original_archive` connects the original `archive 0` to the
named payload through the canonical original text, the complete original reader
result, and the unchanged typed decoder.

`P2Saving16Cell00OriginalFloors.lean` transports the eight stored-bound floor
identities, three counts, vertex dimensions, finite simplex indexing and array
shape, the combined stored-floor guard, and both sums to `archive 0` by equality
substitution. The sum is 13236428172062120 and contains eight separate floors.
The identity between `jensenQ` of the vertices and each stored Jensen bound
remains a separate obligation. These consumers do not establish `simplexValid`,
any all-cell finite guard, or P2.5.

The earlier failed monolithic `Decoded` source is preserved unchanged under
`preimages/failed-monolithic/`; it must not be selected as an import provider.
The original copy in the decoded package is also unchanged. `MANIFEST.json`
records exact source hashes, the replacement conditions and the required three
verification gates. Use one selected source and one selected object for every
full module name, and rebuild these three consumers after their exact imports
have passed all gates. The manifest does not certify an imported dependency
closure or stand in for a successful compiler receipt.

No Lean command, cloud task, production installation or git operation was run
while preparing this package.
