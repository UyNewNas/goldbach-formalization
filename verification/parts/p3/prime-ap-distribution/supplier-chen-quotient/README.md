# Verified direct supplier: `ChenQuotientSieveRemainders`

This checkpoint removes one of the two direct import blockers for
`Part3PrimeAPDistribution`. The production source at parent commit
`f3ad8cbe43c61c903857c7411626ee8c56f4f2f9` is unchanged.

## Completed gates

| Gate | Result | Bound object |
|---|---|---|
| Strict frontend compile | PASS, 9 seconds | production `.olean` SHA256 `182b685d…535` |
| Stock `leanchecker` replay | PASS, 81 seconds | same production object |
| Complete defining-module audit | PASS, 10 seconds | 34 declarations, including private/generated |
| Audit-object stock replay | PASS, 14 seconds | audit `.olean` SHA256 `9099c67f…5a0` |

The audit found 30 theorem declarations and four definitions. It rejected
unsafe declarations, new axioms, truncated types, a mismatch with serialized
constant names, or any transitive axiom outside `propext`,
`Classical.choice`, and `Quot.sound`. The exact complete compiler types and
per-declaration axiom lists are in `compiler-declarations.json`.

The retained `evidence.tar.xz` contains `import-objects.tsv`, which fixes all
4,237 actual objects reported by `Lean.findOLean`, with module, resolved path,
byte size and SHA256. The same archive contains the complete declaration JSON,
the two verified output objects, and all raw compile, replay, audit and
first-failure logs. Its SHA256 is
`3835a394f6cd65f07b2ab195610d90d4c53a1ea4f4c59f1de1fba44d6f44cd08`.

## Recovery history

The first replay correctly failed on a missing dependency object. The bounded
frontier record is preserved rather than rewritten. After the missing object
frontier became available, the stock replay completed successfully. A second
strict compile to a distinct output path produced the exact same production
object hash as the replayed object, binding strict compilation to replay without
overwriting the replay input.

## Boundary

This verifies a direct **project supplier**, not
`Part3PrimeAPDistribution` itself. The other direct supplier,
`Bombieri1965Richert418Unconditional`, and its frozen goldbach BV closure still
need loadable, identity-matched objects. Consequently this checkpoint confirms
no new Part 3 distribution theorem. It also makes no claim beyond ordinary BV's
square-root physical modulus, zero prime-variable phase and bounded external
modulus weights.

Run `python3 verify_evidence.py` in this directory to recheck the retained
evidence and source identities.
