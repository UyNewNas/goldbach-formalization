# P1.4 — post-eight actual odd-trace parity and ordered-source extraction

**SOURCE_ONLY / UNCOMPILED / UNEVALUATED, zero formal credit. P1.4 remains YELLOW.**

## Exact starting point and scope

The latest checkpoint verified before mutation was
`1b6d25c56d4d0b347af171a6c12c539739faf5c0` on
`chatgpt/p1-full87-post8-inherited-squares-20261105`. The source
`P4AOriginalFull87InheritedOddSquares.lean` and its HANDOFF, REPORT,
REGISTRY and INPUT_BOUNDARY were read in full. This new independent
continuation branch is
`chatgpt/p1-full87-post8-trace-order-20261106`.

Manuscript pin and real full87 physical source are unchanged:
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
`paper/source/manuscript-body.tex`, blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, §4 lines 350–485.
No mutation to native/mathlib pins or the constants c, K.

## Source change (a correction, not a renamed interface)

The preceding candidate
`upper_two_min_insert_iff_last_square` had an actual Lean proof
application error in the q-branch. A proof of `Even suffix.card` was
applied as if it were a function to `¬ Even suffix.card`:
`(hqeven hcard).elim`. This is ill typed. The candidate was repaired to
`(hcard hqeven).elim` in the original related packet file. This
correction does NOT confer compilation evidence or alter the theorem
statement.

## New candidate finite mathematics

The ACTUAL `post8OddTrace` source was inspected. For initial
`history.length=8` and `positive=true`, its members have odd LIST
length (even before any setification). Under the source's strict
descending scan and actual reverse-stored-prefix order, every member
is strictly increasing and hence `Nodup`. It follows that its FINSET
cardinality is odd. These are derived from the real recursive trace,
not inserted as assumptions, and preserve all list occurrences.

Four candidate theorem bodies were added in
`P4AOriginalFull87Post8TraceOrder.lean`:

1. `post8OddTrace_odd_length`: invariant of the literal alternating
   true/false trace guard under synchronized history parity.
2. `post8OddTrace_pairwise`: preserves the old prefix's strict order
   through a descending selected sublist and an explicit cross-boundary.
3. `owned87_post8_trace_odd_nodup`: attaches both results to an actual
   retained leaf from `states` of the original 87 domains, for either
   existing `actualFrozenPost8Level`. It uses the SAME valid chosen
   sublist from the literal original tree.
4. `owned87_post8_ordered_reject_last_square`: applies the preceding
   conditional inherited-square source without asking callers for
   `Odd older.toFinset.card` or `older.Nodup` separately.

The remaining incoming assumptions are genuine original-state source
invariants: prefix length eight, increasing stored prefix, descending
remaining carrier, and each remaining prime strictly smaller than each
selected ancestor. They must STILL be extracted from the original
eighth-state producer; currently they are conditional, not assumed to
hold automatically. The prospective p,q order and actual first rejected
branch membership also remain to be established. Rank nine is NOT
silently upgraded to a last-square-only exit.

## Tests and evidence

- Exact finite Python regression: 11,520 synthetic pairs of eight-element
  increasing histories and decreasing chosen sublists, testing trace
  odd length, no duplicates, and strict increasing order. Passed.
- Source readback: new source blob
  `ac0a4b5918570020c1ef9fc457d3fb05d49f23f2` (218 lines);
  corrected previous blob
  `f4e61a586ff6699240591f8cbf488c18f22fa364`.
- Lexical prohibition scan on both source files: no forbidden escape
  tokens. This is NOT a Lean parser or proof checker.
- Lean/Lake, kernel replay, transitive-axiom inspection, archived
  original87 data replay and independent review: NOT RUN.
  No workflow dispatch, Codex, upgrade or remote workstation access.

## Exact remaining internal obligations

1. Derive the four monotone source invariants directly from the actual
   original87 `frontier` producer and `states`, not as a data-field
   equivalent of the target.
2. Attach the genuinely FIRST rejected p,q pair to the literal
   descending traversal; establish the strict order and rank number.
3. Handle rank nine's inherited historical-square failure separately
   (exclude on actual levels, or pay its loss); do not reuse the rank
   eleven last-prime lemma at rank nine.
4. Prove the hprior/hexit/hpair exact normalized logs and same-source
   parity-exit integral asymptotic, with fixed parameters before N.
5. Primitive/modulus-prime/centre errors, sixth filtering, saved87
   archive/gain coverage, two distinct reserves, same-rho assembly.
6. Compile, kernel replay, audit axioms, independent review.

This packet spends no reserve and makes no claim about the entire
Goldbach theorem.
