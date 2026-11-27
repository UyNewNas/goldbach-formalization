# Repaired dictionary formal adapter — unbound incremental draft

These two files adapt the independently reviewed formal draft in
`/tmp/p15-r5-medium/formal/` to the 9107-byte repaired source and version-2
whole-source probe. The original draft is retained unchanged. Both new
`INPUTS` assignments remain **None**; no actual success is filled in.

The source pin is now
`eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff`.
The pinned repaired probe is 29728 bytes / SHA256
`4ff5139a3c9eacd16f29e11a99da8cee7c20541a284ad9538458b3caaf4ea8c4`.
The original AK 9079-byte source identity remains separate.

The successful repaired probe publication is read from future actual INPUTS;
it must be a full commit different from failed AM. Loading requires the chain
AM → repaired-probe publication → a distinct new formal publication, exact
repaired probe bytes, exact repaired canonical/source-only bytes, and the frozen
probe reader's exact original-to-repaired proof-delta check. The v2 receipt must
identify both the repaired source and the original failed AM RESULT, whose
88801-byte fingerprint and real failed job remain fixed.

The original AM full evidence tree is checked against the repaired probe's
before/after records and included in every later preservation check and summary.
It cannot be replaced by the new successful probe tree or a relabelled source.

All earlier reviewed acceptance logic is retained: independent D288 full 6048
slots and separate W58; original four supplier audits and 284 fixed normal pins;
unchanged corrections ROOT and original `g.run_owner`/normal/kernel/full-owned
APIs; one new accepting owner/publication; separate exact installation; partial
owner refusal; and full read-only preservation of any already accepted Geometry
source, all 21 artifacts, accepting/install/probe evidence and original identity.
Geometry still is not a dictionary dependency.

Only new delta risks receive additional checks: old AM or old-source activation
inputs are rejected; a v1 or original-source header cannot enter the v2 path;
the old failure cannot be rebound to the repaired source; and an altered AM tree
fails preservation even if all other mocked contexts match. The previous 11-case
suite is not rerun. Mock headers in these local tests are explicitly synthetic,
contain no command/log/receipt evidence, and never populate production INPUTS.

Actual repaired-source whole-probe success, its job/result bindings and the
final Geometry state must still be observed before activation. No cloud/Lean
command or Git write was performed by this draft's author. P1.5 remains OPEN.
