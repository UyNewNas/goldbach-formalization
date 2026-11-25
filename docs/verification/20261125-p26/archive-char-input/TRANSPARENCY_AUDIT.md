# Old String / explicit characters: transparency review

This is a source review against the exact Lean 4.33.0-rc1 runtime, commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`. It includes no data experiment.

## No opaque obstacle in the accepted original texts

Accepted ArchiveCore v2 declares `geometryText : Fin 13 → String` and
`momentText : Fin 13 → String` as ordinary `def` declarations. They are finite
vectors of loader-produced String literals. There is no `opaque` declaration
or irreducibility attribute on those definitions. The loader's IO executes
while elaborating the original source; it is not an IO action in the resulting
mathematical String value.

For a proposed equality `String.ofList chars00 = geometryText 0`, the relevant
definition unfolding is the old text selector and any ordinary character-list
definitions needed to expose its head. A new global reducibility attribute or
a change to accepted Core is not required merely to make these values visible.
Local explicit unfolding of the selector can make the intended scope clear.
It does not solve the cost of converting/comparing the large values.

The default Meta configuration uses `.default` transparency
(`Lean/Meta/Basic.lean`, `Config.transparency`). `rfl` is implemented through
the reflexivity machinery (`Init/Tactics.lean`, `apply_rfl` / `eq_refl`);
`Lean.MVarId.applyRfl` compares the two sides with definitional equality and
then assigns an `Eq.refl` term for ordinary equality
(`Lean/Meta/Tactic/Rfl.lean`). Ordinary `def` bodies are available to this
process. An actual `opaque` character cache would prevent the desired
definitional unfolding and would instead require an explicit specification
theorem for that cache. A proof theorem may remain opaque after certification;
that does not prevent later use of its stated equality.

## What the String-literal optimization does and does not establish

`Lean/Meta/ExprDefEq.lean`, `isDefEqStringLit`, specifically handles the shape
String literal versus `String.ofList cs`. It converts the literal using
`Expr.toCtorIfLit` before recursively checking definitional equality.

`Lean/Meta/WHNF.lean`, `Expr.toCtorIfLit`, handles a String literal `s` by:

```lean
Lean.Meta.whnf (mkApp (mkConst ``String.ofList) (toExpr s.toList))
```

This is concrete evidence that the elaborator knows the relationship between
a String literal and a quoted character list. It is not a theorem that the
large check has bounded memory. In particular the helper still requests
weak-head normalization of the constructed expression. `String.ofList` is a
transparent definition in `Init/Prelude.lean`, producing a String from
`List.utf8Encode` and its validity proof; it has `implicit_reducible` and an
extern annotation. The logical body remains subject to kernel conversion.

The pinned CBV String simprocs (`Lean/Meta/Tactic/Cbv/BuiltinCbvSimprocs/String.lean`)
can compute literal `ofList`, `toList`, append, and push values in Meta and
return an `Eq.refl` proof. Such a proof still has to type-check against the
original expression. The source does not justify treating a Meta-computed
result, a cached host value, or its hash as an accepted equality without the
normal and kernel checks.

The sibling's separately authorized 128 KiB direct literal-to-`ofList` `rfl`
experiment exceeded its 2 GiB budget during normal compilation and produced
no object. That result supplies no accepted `htext` at the attempted scale,
and does not isolate whether term construction, elaboration conversion, or
declaration checking consumed the memory. This review adds no data retry.

## How a proved binding is consumed

After a binding theorem `htext : String.ofList cs = oldText` has passed its
own checks, the compiled companion interface

```lean
parse_bind_eq_parseChars_bind_of_ofList_eq decode oldText cs htext
```

rewrites the original parser and the unchanged typed decoder together. The
generic `ofList`/`toList` cancellation is already proved for arbitrary `cs`;
it is not re-established by reducing the original String in that interface.
The success guard must still evaluate the new character input and the original
reader/decoder. Keeping ordinary data definitions transparent is needed for
that closed computation. Keeping the already proved equality theorem opaque
is compatible with using it by rewriting.

This separates two costs without claiming either large-scale computation has
passed: the concrete old-text binding proof, and the character-input parser
success proof. No parser internals, record fields, Q80 inequalities, or target
parse statement are removed by this separation.
