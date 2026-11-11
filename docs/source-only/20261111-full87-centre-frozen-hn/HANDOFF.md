# Durable P1.4 handoff — genuine frozen H_N centre error

BASE: 995bcb97375d434c023f38d9e61e4698d71b0744
BRANCH: chatgpt/p1-full87-centre-frozen-hn-20261111
PACKET: docs/source-only/20261111-full87-centre-frozen-hn/
SOURCE: P4AOriginalFull87CentreFrozenHN.lean

Actual increment: replace the arbitrary asymptotic narration for the
existing exact centre fibre budget by a candidate Lean proof with
the literal frozen C_N and H_N. Crucial provenance: the native module
MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries defines the CORRECT
infinite odd-prime series; do not confuse it with the finite
sieve-normalized singularSeries proxy (factor two and truncation tail).

New claims inside source: frozenHN source formula and positivity;
uniform C_2 lower bound; integer base-two log to real log conversion;
Nat.sqrt to Real.sqrt; centre budget <=8 sqrt(N) log N/log2 for N>=4;
centreBudget/frozenHN <=8 log^3(N)/(C2 log2 sqrt N);
tendsto ratio to zero via pinned mathlib log^3=o(sqrt N).
None is compiled here and no budget is numerically paid.

NEXT: with fixed exact pins and valid source-only import placement,
compile this packet and PRIOR dependent packets, repair any actual
elaboration errors, and audit transitive axioms. Independently license
each actual old/new signed sharp-PP coefficient and the ordinary
residual integral / saved87 witnesses. Keep P1.4 yellow.

Do not alter main/master, run Actions, Codex, user machine or add cloud
resource. Never use this historical base SHA to reset a newer task HEAD.
