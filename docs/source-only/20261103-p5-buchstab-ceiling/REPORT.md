# P5.6 / h34 — actual Buchstab ceiling correction

Date: 2026-11-03. Base: `124d09f9fc74e7b78261e2471a573f1657b5633e`.

**PARTIAL_SOURCE_INCREMENT. The whole h34 / full-Member / 441 scope remains OPEN.**
Three new proof-source modules supply the narrow strict-versus-closed ceiling
conversion for both original Buchstab arithmetic rows. No P1.4 or P3.6 source
is edited. No existing production or source-only file is replaced.

`compiled=false`, `kernel_verified=false`, `formal_credit=0`.
All proof bodies and inherited finite computations remain UNEVALUATED.
The execution environment has neither `lean` nor `lake` on PATH. Static
inspection is not elaboration, compilation, a kernel replay or an axiom audit.
No Codex job, connected-computer action, child agent or CI dispatch was used.
This packet has one-session source review, not an independent reviewer.

## Selected yellow and exact difference

The selected yellow is P5.6 -> h34 ->

> 全Member proper/equality层质量、全native域误差、完整外层Theta与immutable430/441共同realization

S18's REPORT explicitly retains the two actual Buchstab arithmetic rows and
their native/outer-Theta linkage as open. R14 supplies the forward implication
from `singleChildren` to `LocalDomain`. Inspection of the literal production
constructors shows why that implication cannot simply be made an equivalence:

- `singleChildren` requires `physicalPrime N q < chi`.
- `LocalDomain` has `OneGate`, which requires `physicalPrime N q <= p.ceiling`.
- The equality fibre is not automatically empty in a finite prime sum.

The new source retains that fibre. It does not call it null, add it to the
strict carrier without correction, or assume that every physical node is an
actual original history. The original upper-parent guard `1 <= p.argument`
is explicit. Lower-parent `s=2` is included, with its original guard unchanged.

The analysis here is of the pinned repository constructors and R/S reports.
The manuscript itself was not independently re-read in this session; the
new statements are tied to those constructors, not claimed as a fresh full
manuscript audit.

## New source chain

### 1. Part5OriginalH430BuchstabCeilingDictionary

`closedChildren` uses the existing `primeCandidates`, the same labelled old
word, and the literal physical `LocalDomain`. `ceilingChildren` is its actual
equality fibre. `local_product_lt_nat` derives the old-product support directly
from the local square gate; `local_prime_le_target` and
`natural_local_iff_closedChildren` show that the `Fin (N+1)` representation
loses no natural local prime.

`mem_singleChildren_iff` supplies the missing converse with the strict ceiling.
`closedChildren_eq_union`, `strict_disjoint_ceiling` and `closedChildren_sum`
provide an exact disjoint decomposition for arbitrary signed tests.
`ceilingChildren_card_le_one` derives at most one prime from strict monotonicity
of the physical logarithmic coordinate. It does not claim zero primes.

The actual query upper endpoint 5 also gives
`primeFloor = N^(physicalLevel N Q old / 6) <= q`.
No selected physical prime floor is assumed in that deduction.

### 2. Part5OriginalH430BuchstabCeilingPayment

The existing exact `thetaAtom_single` is reused at the unchanged Q and prefix.
The multiplier remains `localPrimeFactor d q` (fresh or repeated-prefix law),
not a substitution by `1/(q-1)`. On the actual Buchstab local domain,
`relativePrime <= 1/2`. Therefore, for `4 <= A <= primeFloor`,

```text
childTheta(q) <= (4/A) * parentTheta
ceilingMass   <= (4/A) * parentTheta.
```

The second bound uses the actual at-most-one-prime fibre. A signed test is
paid before cancellation. Neither result divides by parent Theta.

`exists_uniform_primeFloor` constructs a common natural threshold from
`A^(6/Lmin)` for fixed `Lmin > 0`. It precedes Q, the old word and the physical
node, and applies whenever its actual residual is at least Lmin. Supplying
that positive common residual floor for the full original history graph is
still a separate obligation.

### 3. Part5OriginalH430BuchstabArithmeticRows

The two polar rows are actual sums over the production strict children.
Upper-parent reads the old h atoms; lower-parent reads the old H atoms.
The edge scalar is exactly one. `strictRow_value` identifies their full old
array value, including all closed-knot values, without a count licence input.
`closedRow_eq_add` identifies the coefficientwise ceiling difference.

`absoluteCeilingError` is

```text
sum_b |closedRow_b - strictRow_b| * |oldAtomValue_b|.
```

Thus it is not the absolute value of a signed profile sum. Its bound uses the
finite atom L1 size of the original arrays, not a new assertion of norm12.
`immutable430AtomL1` is a finite envelope of the literal seed-only predecessor
arrays `precedingH/precedingh`; no interpreter or saved table is evaluated.

`immutable430_uniform_ceiling_error` chooses
`A = max 4 (4*immutable430AtomL1/epsilon)`, then the preceding natural threshold.
Its conclusion is the actual labelled-family inequality

```text
sum_i sigma_i * absoluteCeilingError_i <= epsilon * parentTheta
```

for both directions and every actual predecessor index g<430. The threshold
is before N, Q, arbitrary finite labelled families, old words, physical nodes,
directions and generation assignments. Equal-product histories are not
collapsed. `labelled_ceiling_error_eq_zero` also supplies the absolute zero
case before normalization.

## What is removed, and what remains

Removed within this narrow source scope:

1. The missing converse between actual strict Buchstab integer children and
   the weak-ceiling local physical carrier.
2. A possible unproved truncation at `Fin (N+1)`.
3. The temptation to delete ceiling equality primes using Lebesgue nullity.
4. An unproved same-Q arithmetic payment for this finite equality fibre.
5. A coefficientwise correction assumption for this fibre at the actual
   immutable430 predecessors and nonnegative labelled outer families.

Still OPEN, not moved into a target-equivalent structure or licence:

1. Interior arithmetic prime sums to the genuine native atom integrals for
   both Buchstab directions. A ceiling correction is not that limit theorem.
2. All incomingAllowed/cellMember/source-owner filters and the actual U3/U4
   root and descendant identifications with one full Member graph.
3. All proper/equality/inherit strata, including the moving lower s=2 guard.
   Keeping the local s=2 case does not establish its global stability.
4. Derivation of one positive residual floor and the original parent-query
   admission conditions for every actual history used by the full assembly.
5. Ordinary/fixed/switched base discrepancies and their analytic count/PP
   licences, and the native/outer parent-Theta integral conversion.
6. The common nested causal smooth refinement through 430+11 levels and
   the final actual h34 supplier.
7. Same-source compilation, kernel replay and transitive axiom checking.

No theorem here assumes h34, hLower, the desired integral bound, or a
coefficientwise-error licence. The geometric identities linking a physical
node to its arithmetic prefix stay visible. Constants c, K, the original
430 interpreter, root norm7/2, row norm12 and the 441-level construction are
unchanged. The new finite L1 envelope is only an asymptotic ceiling-error
threshold device, not a change to the original main-term or reserve ledger.

## Validation and staging

Static checks: no admission/unsafe/native-evaluation tokens in the new Lean
sources; no trailing whitespace; direct-import names and the named source
APIs checked against the pinned reads. Declaration counts and exact raw-byte
hashes are recorded in REGISTRY.json. These checks do not certify parsing or
proof correctness. Existing held dependencies have not been revalidated.

First stage the pinned source-only dependency closure into its intended
`ImbalancedChen.*` module paths; copying these three files alone is insufficient.
Then stage and check in this order:

1. `ImbalancedChen.Part5OriginalH430BuchstabCeilingDictionary`
2. `ImbalancedChen.Part5OriginalH430BuchstabCeilingPayment`
3. `ImbalancedChen.Part5OriginalH430BuchstabArithmeticRows`

Use the S environment's pinned toolchain and dependencies recorded in REGISTRY.
Kernel/axiom targets include `natural_local_iff_closedChildren`,
`mem_singleChildren_iff`, `closedChildren_sum`, `ceilingMass_le`,
`exists_uniform_primeFloor`, `strictRow_value`, `absoluteCeilingError_le`,
`immutable430_uniform_ceiling_error`, and `labelled_ceiling_error_eq_zero`.
Any green credit must refer to the exact checked source hashes and closure.

## Status-tree delta

```text
黄｜全Member proper/equality层质量、全native域误差、完整外层Theta与immutable430/441共同realization
    蓝｜双Buchstab实际strict/closed ceiling字典、同Q逐系数绝对修正与430代统一阈值（source-only，未编译）
```

Only this narrowly stated child has source coverage. Its yellow parent,
h34, P5.6 and the overall theorem retain their previous states.
