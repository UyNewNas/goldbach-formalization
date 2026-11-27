# Final review: classical common Poisson support continuation

Accepted source: `6bafadff2427616abaa8159797b87b816af76d63`.
Date: 2026-11-27.

## Verdict

Independent specification and evidence-quality review passed. No critical,
important or other substantive issue remains in the accepted finite scope.
The review examined existing local evidence and calculated file hashes; it did
not rerun Lean, repeat the Python tests or request new cloud jobs.

## Independent evidence checks

- The outer archive has 110,278 bytes and the recorded SHA-256. All 165 manifest
  members, extracted bytes and member hashes agree.
- All 146 stages have unique names, matching log hashes and command lines, and
  exit code zero. Cloud task status is succeeded, exit zero, with no truncated
  output.
- Source commit, tree, launcher hash, final clean checkout and the gate's source
  bindings agree. All 69 accepted inputs match the publication worktree.
- The 56 reused provider source records, import graph and object hashes match
  R2 exactly. Tools, canonical package roots and pins also agree. The final
  external set retains every one of R2's 67 bindings; its only additional object
  is `Lean.Util.CollectAxioms.olean` for the owner audit.
- The selected consumer strict compile, both target kernel replays, strict
  boundary file and strict owner audit all actually succeeded. The report's
  56 reused / one fresh / 57 total compilation accounting is correct.
- The 38 declarations match the raw owner-audit output. Their complete
  transitive axiom union is limited to the three declared standard axioms.

## Independent mathematical and inventory checks

All four explicit consumer declarations retain their definitions or theorem
statements. The actual clipped block and completed weight, unique membership
premise, signed integer frequency, strict interval endpoint and original
`64 * 2^j` phase denominator are present in the compiler's complete types.

The six consumer records split into four explicit declarations (one definition,
three theorems) and two generated theorem constants. The P3.1 provider contributes
32 reused records (six definitions, 26 theorem constants). All 31 theorem names,
full type strings and axiom lists agree between the JSON inventory and full type
text. No unavailable historical P3.1 inventory comparison or cumulative union
count is inferred.

R3's boundary failure was exactly the cast of natural-number one versus literal
real/complex one. The one-line `Nat.cast_one` repair preserves the same theorem
application and unchanged boundary statement; R4 confirms it passes.

## Documentation disposition

The review identified one wording inconsistency: the attempts index still said
two failures after R3 had been added. That count is corrected to three. The
finite scope remains explicit; full P3.4, original amplitude interfaces and
external spectral estimates stay open. PR #8 remains a draft.
