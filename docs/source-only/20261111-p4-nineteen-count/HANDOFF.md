# P4 latest entry — nineteen slots and actual count, 2026-11-11 10:40 round

SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED / NO STATUS PROMOTION.

Repository: UyNewNas/goldbach-formalization
Branch: chatgpt/p4-uniform-correction-20261111
Exact candidate source commit: 5deef6b95d586cd5d9bc743c24d377f0e8201cfa
Parent: d9b924277736f577f23a5e17dd0483988880f730

New modules:
- ImbalancedChen.P4AOriginalFiniteAll22Nineteen
  source docs/source-only/20261111-p4-nineteen-count/P4AOriginalFiniteAll22Nineteen.lean
  install ImbalancedChen/P4AOriginalFiniteAll22Nineteen.lean
  Git blob abadf4d9fbbec16085deb732f4e3388e35500218
- ImbalancedChen.P4AOriginalFiniteAll22EarlyDefectCounting
  source docs/source-only/20261111-p4-nineteen-count/P4AOriginalFiniteAll22EarlyDefectCounting.lean
  install ImbalancedChen/P4AOriginalFiniteAll22EarlyDefectCounting.lean
  Git blob fb3aa5371d57b599fac9726603aaf3d179dd38db

Exact pins, direct imports, R17 semantic replacements and source-manifest
selection: docs/source-only/20261111-p4-nineteen-count/DEPENDENCIES.json.
Independent static reviews: docs/source-only/20261111-p4-nineteen-count/REVIEW.md.
Full scope and remaining mathematical obligations: docs/source-only/20261111-p4-nineteen-count/REPORT.md.
Existing compilation-flow request: automation/parts/p4/requests/20261111T104000Z-nineteen-count.json

## Mathematical checkpoint

All original zero-based slots 3..21 are now consumed on the actual final
finite fallback dispatcher, in one common cofinal m/r/n/e/q/a/omega/N
schedule. The three early slots 0/1/2 remain the original unsigned
lowerEarlyDefect. No new residual is defined to assume their payment.

A single beta/compiler choice gives the actual final Q/rho density bound
(K-densityReserve-exactSlack+lowerEarlyDefect+eta)*C_N/log N
minus that final policy's actual presieve correction.
compilerReserve is paid exactly once. The same Q/rho gives the real
finite RealB count, preserving signed distribution error, ceil z, T+1,
strict modulus support and all b/T sieve-gate hypotheses.

Neither lowerEarlyDefect nor the signed distribution term is assumed
negligible. Full hUpper is not claimed and no original whole node is promoted.

## Exact compilation handoff

Source commit 5deef6b95d586cd5d9bc743c24d377f0e8201cfa includes both new modules and the predecessor
PaidSixth graph. Use the existing serial compilation-repair flow only.
The previous 09:40 source request is included in this dependency closure.
If that closure is already running, let the existing run finish and reuse
matching accepted objects; do not start a duplicate proof/build round.

Keep Lean leanprover/lean4:v4.33.0-rc1,
mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1,
goldbach 09b97db5764ade1246bfb77206baa1b124760958.
Stage all four selected R17 semantic replacements as a group and the
review-repairs G7 payment, not their older source variants. Direct source
fingerprints are not full transitive acceptance.

No CI, workflow change, local compiler or user-machine access occurred here.
Full elaboration, actual imported objects, expanded theorem types,
transitive axioms and kernel checks remain the existing flow's responsibility.

## Next proof entry

The remaining direct raw obligation is the complete fresh→orderedFifth
signed frontier with protect/rounded cap5 error, including outside the
historical owner. Existing historical G1/G2/G3 floors cannot replace it.
The early135 registry blob d7909c82f6073277f62eee33c2a92ee69a418006
remains unavailable remotely (404); recover/inspect its exact authored
source if later accessible before doing overlapping work. Do not access
the user's machine or treat the source as nonexistent.

After the true early defect is paid, preserve this exact final Q/rho when
consuming the complete P3 signed PP supplier. Existing complete analytic
third-tail/integrability/L1 proofs must be reused. Wait for the next
existing hourly dispatch; do not create another schedule or duplicate round.
