# Original cell00 decoder continuation

This package separates the unchanged original reader and typed decoder. A quoted
payload is candidate data until a Lean theorem proves the original decoder
returns it. The P2.5 node and its finite guards are not accepted by this package.

## Recorded acceptance

`P2Saving16Cell00OriginalJson.lean` passed strict compilation, independent
`leanchecker` replay, and a complete owned-declaration audit. It proves
`SourceJson.parse (originalText (0 : Fin 14)) = .ok rootValue` using the accepted
canonical text, full reader payload, and fuel transport. Source SHA-256:
`3543baacddde3ff81b566b1f1c597251dd27d0981ba95161eeb25a8563ea3fda`.
The unchanged accepted source is installed in `ImbalancedChen/`.

## Candidates awaiting acceptance

- `P2OriginalSaving16DecoderChars.lean` gives representation equations using
  `String.toList_ofList`. It retains every original error branch and operation.
  The first proof attempt failed on the generic monadic match identity. Its
  exact source is retained under `attempt-evidence`; a constructor-case proof
  is prepared for the next strict run. No decoder success was inferred.
- `P2OriginalSaving16DecoderCharsProbe.lean` checks exact integer and rational
  results through those equations, including the longest actual cell00 token.
- `P2Saving16Cell00TypedPayload.lean` quotes all typed fields and retained raw
  geometry. It contains data definitions only. The immutable generator and
  manifest preserve the original rational expressions without host reduction.
- `P2OriginalSaving16DecoderCompose.lean`, `P2Saving16Cell00ScalarDecode.lean`,
  and `P2Saving16Cell00FieldDecode.lean` are further source-only composition
  candidates. They are not accepted merely because their scalar pattern or
  raw data has been checked.
- `P2Saving16Cell00OriginalParse.lean` is the downstream rewrite-only consumer.
  It requires a separately accepted exact typed-decoder equality.

The earlier `P2Saving16Cell00Decoded.lean` whole-expression attempt failed to
reduce under `decide +kernel` at 11264 MiB. No generated error/sorry artifact is
accepted. It is retained as the failing diagnostic, not installed in production.

All results remain bound to the original 53,305-byte CRLF input with SHA-256
`360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6`.
The independent full-owned audit template and expected inventory accompany the
typed payload. No parser/decoder replacement, new axiom, or native decision
procedure is used.
