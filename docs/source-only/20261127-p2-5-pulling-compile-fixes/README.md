# Repairs selected from actual pulling compiler diagnostics

These postimages address the first strict local compile of the existing
Cell00 finite-geometry sources on 27 November 2026. They are unaccepted until
their separate normal, stock kernel replay, and complete owned-declaration
audit receipts succeed. The original sources and failure logs are retained.

`FaceDecoderCore` failed at the code-generation check because its unchanged
`decodeFace` body uses the already accepted noncomputable Nat decoder.
Adding `noncomputable` to this definition preserves its kernel reduction and
type. The finite guards continue to use kernel checking.

`PullingFaceInduction` reported one unnecessary `simpa` and four unsolved goals
that were all literally `0 ≤ 0`. The postimage uses `simp` in the first place
and closes those four existing normalized goals with `le_rfl`. The Shape
predicate, induction, affine separators, hypotheses, and conclusions retain
their original text. Strict lint remains enabled.

The manifest pins the actual failed source and logs, records each bounded
replacement, and checks that reversing the replacements recovers every byte
of each donor. This is an elaboration and proof-expression repair. The
diagnostics expose no unresolved mathematical inequality in these branches.
Containment, support, the original-cell transports, and the final integral
remain subject to their separate actual dependencies and receipts.
