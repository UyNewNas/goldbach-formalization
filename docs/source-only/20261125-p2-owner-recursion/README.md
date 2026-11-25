## Accepted repair

Job `42c2f3a3152e4bf48e1fd877814e23b5` validated the final
`6d2608a6949e6712491db5a1851dba6a4458e94a419972378a42519d5730accb` source:
strict compilation, stock independent replay, and the unchanged full-owned
audit all passed (77 owned declarations, including generated declarations).
The 247-module project closure and joint owner import also passed; 245
unchanged compiled modules were reused. All 12 selected owner/bridge audit
receipts are current, covering 566 owned declarations. The previously reported
partial auxiliary declarations are absent from the accepted owned inventory.
These are implementation/ownership repairs, with the original propositions
and mathematical argument retained. The source-preparation history below
records the earlier, unaccepted states.

# Explicit recursion for the original affine owner

**Source-only candidate. No local compilation, replay, or audit is claimed.**
Only files in this directory were written by the preparing agent; it did not
edit the active owner or audit rules. After candidate handoff, the shared
active owner was observed to match the candidate hash. That integration and
its remote validation are recorded separately by the root agent.

## Observed blocker

The root agent's actual private diagnostic job
`efa45b70ffeb4be5aa0945b96c0b42be` found two generated declarations owned by
`ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows`:

| Declaration suffix | Unsafe | Partial | Axiom |
|---|---|---|---|
| `coefficients._unsafe_rec` | false | true | false |
| `evaluate._unsafe_rec` | false | true | false |

The current owner had passed normal compilation and stock replay, but these
flags prevent the required full-owned audit from accepting it. The candidate
does not exclude these names, weaken the audit, or reinterpret a partial
declaration as accepted.

The active definitions match the saved P1 donor's coefficient/evaluator block
byte for byte. The current P1 worktree donor also matches that saved donor's
complete bytes. Historical donor acceptance therefore supplies no alternative
source implementation for these two functions under the current audit.

## Minimal change

Both public functions keep their original types:

```lean
coefficients : Expr → Fin 9 → ℚ
evaluate : Expr → (Fin 8 → ℝ) → ℝ
```

Their implementations now directly apply `Expr.rec` with the constant motives
`fun _ => Fin 9 → ℚ` and `fun _ => (Fin 8 → ℝ) → ℝ`. Each of the five recursor
branches uses the same constant, coordinate, addition, subtraction, or scalar
multiplication as its original constructor equation. This removes the
self-recursive definition syntax that produced the two partial implementation
auxiliaries. The actual generated inventory must still be checked remotely.

No explicit structural-recursion annotation is guessed. Direct use of the
inductive recursor makes the recursion form explicit and follows the project's
already used recursor patterns. Both original types and all ten constructor
equations are retained; `P2OwnerRecursionEquations.lean` states each equation
with proof `rfl` for the root to compile against the candidate.

All imports, the Expr datatype and notation, all semantic expressions, and
every theorem statement remain byte-identical to the original preimage.
Three proof branches in `evaluate_coefficients` also need an elaboration
repair: `change` first presents the definitionally equal public coefficient
and evaluator expressions, then the same helper lemmas and induction
hypotheses rewrite the goal. The constant and coordinate branches and all
other proofs remain unchanged. The theorem still proves the interpretation
for arbitrary expressions, and the unchanged `literal_coefficients_match`
proof still checks all 15 × 96 × 9 literal coefficients by the existing kernel
mechanism.

## First compilation and proof-folding repair

Job `d994d3d3de5c4b3fa8ea6acefdacbcdf` failed on exactly three rewrite matches
in the first candidate's addition, subtraction, and scaling induction
branches. Unfolding `coefficients` exposed `Expr.rec` expressions that the
following rewrite did not match. No theorem statement or mathematical
premise needed to change.

The first candidate SHA-256
`37330fa3009fac309ead500ba80b2dd8621406af30ef671f44fc5a9041267198`
is retained in `OriginalDescendingFifteenLiteralAffineRows.attempt01.lean.txt`,
with its original patch. The revised candidate SHA-256 is
`6d2608a6949e6712491db5a1851dba6a4458e94a419972378a42519d5730accb`.
Only the three proof branches differ between these candidates. The revised
candidate still requires the actual remote compilation, replay, and complete
owned audit.

## Files and preservation

- `OriginalDescendingFifteenLiteralAffineRows.before.lean.txt` retains the
  exact current active preimage.
- `OriginalDescendingFifteenLiteralAffineRows.lean` is the isolated candidate.
- `explicit-recursor.patch` changes the two evaluator definition bodies and
  the three proof-folding branches.
- `OriginalDescendingFifteenLiteralAffineRows.attempt01.lean.txt` and
  `explicit-recursor-attempt01.patch` preserve the failed first candidate.
- `P2OwnerRecursionEquations.lean` contains the ten reflexive equation checks.
- `PROVENANCE.json` binds the original, donor, candidate, and patch hashes and
  records the actual reported diagnostic flags.

The local reverse comparison reverses only the two definition rewrites and
three proof-folding changes and recovers the complete original preimage
bytes exactly. A repository search found no source reference to generated `coefficients.eq_*` or
`evaluate.eq_*` names; downstream source uses the public definitions and their
existing semantic theorems.

The forward patch was also checked and applied to an isolated copy of the
preserved preimage; its result matched the candidate bytes exactly. An initial
forward check against the shared active path found the patch already applied,
so the preserved preimage was used for this verification. No active path was
changed by that test. Independent read-only source review by
`/root/p2_existing_audit` confirmed the first candidate's recursor branch
order and intended definitional compatibility. The actual compiler then
identified the three rewrite-matching failures above. That source review
does not provide Lean acceptance for either candidate.

## Required verification boundary

The root can stage the candidate in an isolated source/object overlay, using
the existing qualified dependencies. Compile the owner and the ten equation
checks, replay with stock `leanchecker`, and run the unchanged complete
owned-declaration/type/unsafe/partial/axiom audit. Every generated declaration
must remain included. The candidate has no acceptance until those actual
checks pass.

If this owner changes, its real dependent closure must receive the new source
and object signatures. Reuse unaffected valid objects. Do not attach a prior
receipt to a changed dependency merely because the public types and equations
are preserved. The root reported ten other native owners accepted; this
source-only candidate does not promote or alter their recorded status.
