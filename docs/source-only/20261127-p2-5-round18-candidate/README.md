# R18: Cell0 chronology proof expressions

The candidate changes only the actually failed Cell0 chronology owner. Its theorem headers, definition tokens, imports and options are preserved. The exact source bytes and the completed R17 normal/replay/owned receipt are pinned in SOURCE_SELECTION.json. The new candidate has no formal acceptance until this continuation finishes its own three stages.

The unchanged gates cover 377 normal modules and 69 owned targets. The failed closure has 16 modules; 361 normal successes and 53 accepted owned results remain eligible for qualified reuse. All five protected controller functions are AST-identical and both nine-condition postflight lists are unchanged. Blocked successors are not modified.

Run `python3 -B test_round18_delta.py` after installation, or set P25_REPO_ROOT to the existing repository to check this staged package. These three focused tests check source/specification preservation, failure/reuse scope, and exact terminal/controller guard provenance.

## Observed preflights and final source

Two isolated preflights are retained in `preflight001/` and `preflight002/`. The first exposed finite-vector simplification failures; the second reduced the owner to one failure in the `old_W` proof, where the unqualified `B` and `cap` referred to the wrong namespace. The final candidate qualifies these two existing definitions. Expanding them gives exactly the affine row already present in hypothesis `h15`; no theorem statement or assumption changes.

The final source has SHA256 `27223877023e38d88077690d9384b90ff3b0d4b3033a9dc1a599eae49ad398e0`. It has not received a third preflight: the next execution is the complete R18 continuation with normal compilation, stock replay and full owned-declaration audit. `LOCAL_VALIDATION.json` records the three passing source/controller checks without claiming Lean acceptance.
