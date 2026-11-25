# Canonical character quotation: future cell01 candidate

This package contains one generic elaborator and one cell01 binding candidate.
It has not been compiled or executed and grants no acceptance credit.

The loader elaborates the already imported canonical `originalText (i : Fin 14)`,
uses pinned official Meta reduction, accepts only `Expr.lit (.strVal s)`, and
returns the existing `toExpr s.toList` quotation. Nonliteral results fail.
The candidate has no `readFile`, JSON parser, typed decoder, host numerical
checker, second String definition, or reduced parser fuel. OriginalInput's
existing source/input/object binding remains necessary.

The only concrete definition is `chars01`; the only target is
`String.ofList chars01 = originalText (1 : Fin 14)`. Its reflexivity construction
reuses the three-line prefix accepted in raw cell00 attempt003. The raw cell00
module is neither imported nor rebuilt, and no other cell is generated.

`PINNED_API_EVIDENCE.json` records the official Lean62eed source blobs and exact
API excerpts used, including weak-head reduction stopping at a literal. The
manifest records the already cached Expr/ToExpr/reflexivity source hashes.

This package must remain inactive until the current b80 unguarded-owner check,
cell00 canonical binding, and full cell00 parse/decode sequence is accepted.
Any later run still requires normal kernel checking, independent replay, and
complete owned inventory auditing of both new modules without helper exclusions.
The cell01 source retains raw003's local maxRecDepth1000000, Elab.async=false,
and stderrAsMessages=false; it does not change the normal heap or proof gates.
Actual generated helper flags, kernel acceptance, resource use, and cell01
performance remain unknown.

No production source, mainline runner, parser, original finite guard, or queued
task is changed by this source-only package.
