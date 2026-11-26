# Accepted cell00 typed field decoder, attempt006

P3 task `271829aa21dd4513b8e2754b759fb241` checked the source published in
`99ec807044cd865b9713e769c6a967094c4b3e34`. All three required stages passed:
normal Lean checking (9.204 seconds), independent leanchecker replay
(7.931 seconds), and complete owned declaration audit (5.616 seconds).

The owner is `ImbalancedChen.P2Saving16Cell00FieldDecode`. Its seven audited
declarations include the actual private `decodeCell_of_field_successes` theorem.
The theorem composes 19 equality premises: 16 use accepted imported certificates,
and three use unchanged theorems in this same freshly checked owner. All four
public statements are unchanged. The 21 accepted dependency objects were reused;
their accepted compilation, replay and audit gates were not rerun.

`ACTUAL_EVIDENCE.json.xz` contains the exact remote RESULT, all three logs, and
the accepted object. Decompression yields a JSON array of named artifacts with
their byte lengths, SHA256 digests, encoding, and exact content. `SUMMARY.json`
is a compact derived index, not a replacement for the original receipt.

The original RESULT SHA256 is
`82123af5bc4f1e9334da8f578de11147effe73da0a7ab90b55459abbb25bcb0e`.
The accepted object SHA256 is
`be8aa94f8754aa8404da5dc12d8c4544ce3063b75af82ddbb51879e19ccf70eb`.
The compressed capsule SHA256 is
`cb477a3b4ebc8353f1ed1e0e7024b1539916292cb3c424e6b6560a11bf2bda3c`.

This establishes the typed decode of the proved raw cell00 root. The original
archive transport, finite arithmetic consumers and complete fourteen-cell Q96
proof are separate obligations. This receipt does not claim P2.5 completion.
Earlier failed aggregates and attempts004/005 remain failed and unchanged.
