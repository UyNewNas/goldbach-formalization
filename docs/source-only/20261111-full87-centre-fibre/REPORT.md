# P1.4 — exact original87 signed centre-prime fibres

## Provenance and precise new scope
Continuation from verified GitHub branch chatgpt/p1-full87-signed-sharp-recenter-20261111 at `1e01d9c7fee860a0cbed598ee2862058d103c163`; the preceding packet's source commit was `e2d88d41c827a1c14166711a9a734a3f1b047478`. This separate task branch is `chatgpt/p1-full87-centre-fibre-20261111`. Do not return to the 9649ab3 navigation point.

Frozen manuscript, unchanged: UyNewNas/chen-imbalanced-semiprimes@`9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Inspected §4 `eq:current-PP`, `lem:current-sharp-prime`, `eq:current-sharp-pi`; fixed parameters and conditions as before. Lean leanprover/lean4:v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958. c=49044063/25000000, K=8452171/1250000.

## Actual mathematical step
The previous packet proved a source-only candidate for the exact sharp receiver identity, with the modulus-prime recentering term cancelled and the centre-prime correction *still present*. This packet works on that remaining correction rather than postulating it negligible. Let

`C_N = {P in chenPrimePrefix N | P divides N}`, and
`U = full87PhysicalSupport = true sixth complete moduli union true finite eighth complete moduli`;
`rho(d)=full87PhysicalRhoChange(d)` retains original old-minus-new signed rho.

New candidate finite identities are:

`chenCentrePrimeAPCount N N d = #{P in C_N | P ≡ N (mod d)}`.

`gain(centrePrimeAP) = sum_(P in C_N) sum_(d in U; P ≡ N (mod d)) rho(d)`.

The second identity is additionally tied to **sum over all original87 ownedSource Cell occurrences** via the pre-existing `gain_eq_owned_sources`; it is not a new independently licensed sieve coefficient or a deduplicated state population. Complete modulus, sign, Rosser beta and source multiplicity survive the pre-existing gain normalization.

A genuine finite absolute bill is

`B_centre = sum_(P in C_N) sum_(d in U; P ≡ N (mod d)) |rho(d)|`

and the proof candidate shows `|gain(centrePrimeAP)| <= B_centre`. Unlike the previous unrestricted old/new absolute expression, this uses only actual prime-divisor congruence incidences and permits subtraction of the *same physical signed rho* before taking absolute values. No numerical comparison between the two budgets has yet been kernel-checked, and no o(H_N) bound is claimed.

For nonprime N, a centre divisor prime satisfies P<N; at each actual congruence incidence the full modulus d divides the strictly positive integer N-P. This explicitly identifies the no-zero-difference condition needed in the manuscript's sharp endpoint; the Lean statement assumes `¬Nat.Prime N`, rather than smuggling in an unproved large-even simplification.

The conditional original sharp PP pair receiver bound now reads
`|gain(receiver)-pi(N)*gain(density)| <= epsilon_6 + epsilon_8 + B_centre`,
on exactly the two prior separate policy-specific signed sharp PP hypotheses. These hypotheses remain **unproved**. The modulus-prime term is *not* recharged in this sharp route; the centre prime error is *not* set to zero.

## Files and checks
- `P4AOriginalFull87CentrePrimeFibres.lean`: source-only proposed bodies for literal fibre identity, finite indicator/Fubini exchange, actual full-modulus signed correction, original87 owner connection, finite absolute budget, and conditional receiver inequality. Git blob `fdb559d272d0c5e0f604516f5865b36dd40e81bb`; source commit `4f4fb3f33aa3c168ecf61a6ac003c23042490c6a`.
- `check_finite.py`: 10,506 finite (N,d) centre-prime equalities including d=0, and 5,000 randomly generated overlapping old/new signed full-modulus synthetic sums and absolute bounds; 0 failures. This checks abstract combinatorics, *not* actual original87 populations or archived saved87 witnesses.
- Local execution: `lean --version`, `lake --version`, `elan --version` unavailable: exit 127 each; no pinned Lean/mathlib/native closure detected. No source elaboration, kernel replay, transitive axiom audit or independent verification. Static comment/parenthesis/forbidden-escape checks are not Lean checks.

Status: `SOURCE_ONLY / UNEVALUATED / UNCOMPILED`. §4 PP and sharp endpoint `REGISTERED_NOT_PROVED / NOT_CALLED`. No CI/Codex/user-machine/main/master/merge/force-push/resource escalation.

## Exact remaining yellow obligations
1. Quantify `B_centre = o(H_N)` (or a correct reserve-scale bound) on the actual same full-modulus old/new rho. Incidence identity by itself pays nothing.
2. Establish **separately** each original sixth/eighth coefficient's fixed-parameter sharp PP eligibility: true support/squarefreeness/(d,N)=1, signed class, smooth singleton and legitimate integer X, endpoint/trim; apply genuine manuscript statement only if conditions match. No absolute per-leaf PP leap.
3. Ordinary continuation to actual residual integral with shared history; weighted actualParent discrepancy, saved87 original numerical witnesses, frozen signed numerical gain.
4. Low/high q and primitive/other correction costs, raw/finite/filtered, rank9, changed/tagged and two independent reserve payments at one rho.
5. Pinned Lean compilation, kernel replay, transitive axiom review, original numerical archive replay, independent verification.

P1.4 parent stays YELLOW.
