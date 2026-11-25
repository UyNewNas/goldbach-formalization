# Existing parser representation tools for P2.5

Status: CURRENT PARTIAL ACCEPTANCE. The current run independently replayed and
fully audited CharInputBridge (9 owned declarations) and SourceJsonCharInput
(6 owned declarations); the unchanged accepted parser (122 declarations) was
reused. PackedChars compiled and replayed but FAILED the unchanged complete-owned
audit. See `P3_ACTUAL_RESULT.json` and the exact `p3-attempt-001/` artifacts.
No concrete String/Char binding, complete JSON parse, Q96, or final P2.5 acceptance
follows from these generic helpers.

This package installs three existing generic modules byte for byte from commit
`bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3`. The original blobs are preserved
in `original/ImbalancedChen/`. `REUSE_MANIFEST.json` binds their paths, source
hashes, historical evidence and unchanged current parser. `SOURCE_CLOSURE.json`
records the separate four-module closure, with only Lean as an external import.

The actual single-cell original parsing diagnostic reported kernel memory
exhaustion. These existing representation tools address that
implementation obstacle; this is not a new mathematical saving or a substitute
for the original JSON-to-proof relation. The diagnostic still embedded all
fourteen original Strings, although its proposition selected cell00 only.

The current SourceJson and FiniteArchive are unchanged. No M19-specific data,
field certificate, segmentation algorithm, source loader or saving16 arithmetic
is installed. The current 377-module continuation graph and 64 audit targets
are unchanged.

Historical donor normal/kernel results do not establish acceptance here. The
current parser uses a different, total/noncomputable implementation. Any API or
computability incompatibility must be established by actual compilation before
a separate source repair is considered. Full-owned auditing must include all
generated declarations; no historical object or acceptance record is installed.

A separate character representation still needs the stated Lean String/Char
binding equality. A file hash is provenance, not a proof of that equality.
The unchanged PackedChars source includes its original local resource options;
the actual runner receipt records their effective values. The separate
`packed-repair/` probe and single-owner candidate remain source-only until their
respective actual runs. They do not modify the original full-owned audit gate.
