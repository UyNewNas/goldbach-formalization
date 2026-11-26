# Consumer attempt005: one accepted owner, OriginalParse resource failure

P3 task `c1e16ac3e1ae45e4b05ed01664d735dd` executed the reviewed v5 source
from publication `be20f0b050bb787ecb98f9afdd9b6a386706f45a`.

`P2Saving16Cell00Decoded` passed normal checking (3.861 seconds), independent
replay (3.454 seconds), and complete owned audit (4.027 seconds). Its four owned
declarations and exact 16,208-byte object are preserved. The object SHA256 is
`f700e8e866da0192152040a0853e27eab857ee007c0076df61613e3a849e534f`.
This individually accepted owner must be reused in continuation.

`P2Saving16Cell00OriginalParse` then failed normal checking after 172.179 seconds,
without a timeout. The complete 1,046-byte log reports kernel memory failures
while checking the original-decode and parse-success theorems. Its log SHA256 is
`8c4de444dda9af81f3783f916be29440a89b465ac7096de0d7a5a51247f12d16`.
The subsequent failed-declaration axiom printouts confer no proof credit;
the module did not reach replay or owned acceptance. The three later owners
remain pending. The aggregate remains `accepted = false`.

`ACTUAL_EVIDENCE.json.xz` is the complete byte-checked export of the original
RESULT, four stage logs, the accepted Decoded object, and the exception log.
It decompresses to an array of named artifacts with encodings, byte counts,
hashes, and exact content. Its SHA256 is
`cae8680b31d1ca2a03ada9cabdd186a12ede1946132aa308290b05bcd58549cc`.
The original 5,049,315-byte RESULT SHA256 is
`bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88`.
`SUMMARY.json` is a derived index and `TASK_STDOUT.log` is the exact service log.

No completed original-archive transport, fourteen-cell Q96 proof or whole P2.5
acceptance follows from this partial result. The failed aggregate is retained
separately from the accepted Decoded owner.
