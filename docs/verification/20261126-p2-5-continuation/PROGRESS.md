# P2.5 continuation — 2026-11-26

Base: 52098e403ac4b28c72ec5958fd738ae93d785ac5, work/p2-5-saving16-20261125.

- Recovered existing P3 task a2885d420bc349adb4f3b63b080bd23c without resubmission.
- Canonical originalText 0/String/Char bridge: strict compilation, independent kernel replay and complete owned audit accepted (two declarations).
- Full cell00 parse+decode: kernel memory failure at 11264 MiB; no accepted parse proof.
- P2 endpoint still reports Session terminated on system_info/compiler_info/get_task. Existing P2 task 2ae30f61b07f46b397eb8db93b65fb72 was not cancelled or resubmitted.
- Backup service returns retained-job limit; no job records deleted or settings changed. P3 is the existing arithmetic execution target.
- Exact local Lean/leanchecker binaries match accepted remote SHA256.

## Execution decisions

Continue in the existing dedicated P2.5 branch and preserve every preexisting edit. Reuse the original parser, decoder, raw input, mathematical endpoints and existing segmentation work. The prior full-reader failure is the failing regression. A low-fuel result may be lifted to the original length+1 fuel only by a kernel-proved stability theorem; it is not a new assumption or replacement parser. The exact input-to-object, original decoder, separate Q96 floors, all96 constraints, occurrence signs and common parameters remain required.

The existing raw-span planner estimates sufficient fuel 371 for the original 53,305-byte cell00, versus actual original fuel 53,306. This host estimate is untrusted candidate data; Lean must prove the concrete parse and the exact fuel transport.

## Pending

1. Prove original-parser successful-result fuel stability, reusing or adapting no existing theorem unless found.
2. Compile the unchanged parser at candidate fuel, retain exact typed decoder and final originalText binding.
3. Continue original finite arithmetic and compatible downstream owners if accepted.
4. Publish only actually checked claims and explicit residual obligations; verify remote SHA.

A bounded low-fuel diagnostic is queued/running in the existing P3 P2.5 worktree. It reuses seven exact accepted dependency objects, checks the unchanged full typed decoder at fuel 371, and keeps normal compile / leanchecker / complete-owned audit separate. Its success would not yet give original-fuel or canonical binding credit.

Checkpoint: FiniteCore accepted29; Fuel accepted76; FuelBridge accepted5; exactcell00 AST accepted2 and original-fuel wrapper accepted2. The original decoder candidate reached local4GiB with import baseline3.56GiB and will continue on existing P3 with11GiB. All scopes remain explicit.
