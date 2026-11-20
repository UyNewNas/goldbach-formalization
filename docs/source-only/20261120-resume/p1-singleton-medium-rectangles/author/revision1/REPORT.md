# Revision 1: exact reserve namespace repair

The installable review candidate is this directory's `P1OriginalSingletonMediumRectangles.lean`, 10010 bytes, SHA256 `80bf1e6fdae063320fcb9f69f9825b14cdc6de9ac256d5f5426fef503660f130`. The original 9966-byte `4c345bb1…` candidate and parent FREEZE remain unchanged as history and are not selected for installation.

Exactly one line is added: `open P5Z.OriginalPrimeAllGroupHBDiscrepancy`. The final full-Atlas statement uses that existing namespace's `properPowerReserve`, `roughPrimeReserve`, and `trimReserve`, at lines 61, 66, and 71 of the pinned source. Opening that namespace inside the imported MiddleTensor module is not a public alias here. The new explicit open makes those owners available without changing any theorem statement, proof body, imports, or mathematical argument. Inverting the insertion reconstructs the preimage exactly.

This is a statically identified expression/name-resolution repair, not a Lean execution result. The original matrix and mathematical review request in `../REPORT.md` still apply, with this exact postimage replacing the old candidate hash. Existing source61, OneLong and actual row dictionaries remain unchanged and are reused. Scope is only the original finite medium-to-occurrence identity and complete Atlas expression rewrite; no signed M, whole-box license, analytic restoration bound, Atlas/PP estimate, P1.4 or kernel acceptance is added.

`EXACT_DELTA.json` pins the new source, inverse comparison, and reserve definition owner. Parent `SOURCE_PINS.json` supplies the unchanged imports/manuscript context. Independent n09 review is pending; ROOT owns any publication and compilation decisions. No proof execution, CI, artifact download, Git/GH write or subdelegation occurred.
