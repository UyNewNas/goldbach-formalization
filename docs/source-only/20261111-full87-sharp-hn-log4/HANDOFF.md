# Durable P1.4 handoff — original sharp log-4 PP error on genuine H_N

Task continuation baseline HEAD: ce1c84a0151aa4910eb464171f645b1b9dd92880.
New independent branch: chatgpt/p1-full87-sharp-hn-log4-20261111
New packet: docs/source-only/20261111-full87-sharp-hn-log4/
Candidate: P4AOriginalFull87SharpFrozenLog4.lean

Additional candidate: P4AOriginalFull87LiveSharpFactors.lean,
which proves ORIGINAL live nonzero delta-rho factorization into a*b
for the actual active sixth/eighth policy, preserving the real a<L and
nonzero rough weight. The displayed carrier is not automatically the
sharp PP support. This does not supply q<=N^theta.

Actual result: conditional but nontrivial pointwise H_N normalization of
the original sixth-minus-eighth receiver sharp-prime invoice with two
independent permitted fixed-A=4 PP numerical errors. Uses the actual
centreCoprimeDivisorBudget/H_N rate from ce1c84a and exact prior sharp
recentring; keeps all original full-q signed coefficients. Does NOT give
PP admissibility, PP itself, reserve settlement or the full ordinary gain.

No compile: Lean/Lake/Elan all command-not-found exit 127 in this run;
the candidate is UNEVALUATED and must not be reported as kernel checked.
One exact symbolic algebra check via SymPy passed. Source forbidden-tactic
scan passed. No AGENTS.md was present in the actual repository tree
(15760 tree entries, checked).

NEXT: On current HEAD, first read this source, REPORT, INPUT_BOUNDARY and
REGISTRY. Verify candidate elaboration with pinned Lean and all source-only
imports if the fixed environment becomes available. Independently inspect
existing actualSmallRoughRho_ne_zero_factors in
ImbalancedChen/ActualSmallRoughAttachment.lean and policy-specific full-q
cap theorem to supply support q<=N^theta; then prove actual smooth singleton
PP admissibility without inventing an unrestricted coefficient class.
Keep P1.4 yellow; other yellow obligations remain in REPORT.

Pins: manuscript 9731290e8f53cffda44129906cde6a965eaa869b and blob
d529bea2ecfcc74d64fc1664ac770a3becaa7c79; lean4 v4.33.0-rc1;
mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1;
native 09b97db5764ade1246bfb77206baa1b124760958;
c=49044063/25000000; K=8452171/1250000.
Never reset to old navigation SHA. No main/master edit, CI, Codex,
independent task write or dependency upgrade.
