# Five-consumer attempt004: disk failure before the first Lean gate

Task `c9cc66562e934713bcf75ab704f8562d` executed the reviewed v4 runner from
publication `8fb0faace8f95a4ad4be26f32350575491445ac4`.
It failed with `OSError: [Errno 28] No space left on device` while creating the
`P2Saving16Cell00Decoded` stage directory. No normal compilation, independent
replay or owned audit started. All five owner records have empty stage maps and
`accepted = false`; their temporary RUNNING/PENDING labels confer no credit.

`RESULT.json.xz` contains the exact original UTF-8 receipt. Its decompressed
size is 5,016,911 bytes and its SHA256 is
`2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a`.
The compressed SHA256 is
`3948a2189a572117388b318c3610f3e251ac73486359cf40497d36b8b2b365b8`.
`SUMMARY.json` is derived metadata; `TASK_STDOUT.log` preserves the full 547-byte
compiler-service output.

The accepted field-decode attempt006 and other prerequisite owners remain
separate, accepted receipts. Copying those objects into this attempt did not
create new acceptance. Neither cell00 consumer completion nor whole P2.5 is
claimed here.
