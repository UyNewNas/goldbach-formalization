# P0 Round 12: required Round6 type export

Starting P0 receiver commit: `d6f98737e199fb09d42a51e9d80002bd7859b4e0` on `chatgpt/chen-p0-integration`.

This changes verification infrastructure, not mathematical theorem statements.
The already present `Round6Audit.lean` and `check_round6_types.py` cover the four fifth-level producer modules (70 defining-module declarations) and the conditional main bridge. The checker now requests explicit trustLevel=0 (`-t0`) along with warnings-as-errors. The core workflow invokes the checker after root build, requires its successful outcome, and retains the raw stage log and local output artifacts. Existing root build, bundled checker, root axiom audit, Round3 and Round4 gates remain mandatory.

**Important**: this commit is SOURCE_ONLY until the exact new-commit CI succeeds and Round6 receipt binds full compiler types, imported objects and recorded axioms. No source proof was changed or re-proved this round. The final bridge still depends on unproved `hLower` and `hUpper`.
