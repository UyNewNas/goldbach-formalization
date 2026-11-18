# P1.4 — true stopped q0 Rosser quotient and sixth-divisor occurrence bound

## Recovery (actual readback)
Predecessor remote HEAD `d830038e9d94aec2ca5c0ab88bcd53c5bfb6825b`, branch `chatgpt/p1-full87-stopped-centre-exception-fibre-20261118-1015`; exact compare status identical, ahead=behind=0. Read its complete 282-line Lean source and REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF. Root/docs/docs-source-only AGENTS.md returned 404. Frozen manuscript at `9731290e8f53cffda44129906cde6a965eaa869b` read; blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, including the original signed PP and sharp-prime endpoint. No rewind.

New branch: `chatgpt/p1-full87-stopped-q0-quotient-divisor-20261118-1110`.
New candidate source commit: `fc010469bea988279bbda7db19f10f9863e3ca9b`.
New file: `P4AOriginalFull87StoppedQ0QuotientDivisor.lean`, 229 lines, confirmed remote Git blob `fa0d9fe34af146a2457b121d7d9400fc75933e31`.

## Concrete manuscript-side advance
Predecessor proved that for nonprime N>=8 with N%4=0, the upper-third centre correction in the ORIGINAL stopped fifth/sixth event ledger equals the signed q0=(N-2)/2 fibre. It did **not** bound that fibre, and the fixed physical-rho bound <=1 is NOT applicable to stopped occurrences.

New candidate genuinely constrains the original q0 fibre:

1. Elementary *positive product fibre single quotient* lemma: for fixed b, positive q and unchanged finite Rosser index S, at most ONE a satisfies a*b=q; the only candidate is a=q/b, requiring exact divisibility. The strict X<a*b condition is exactly X<q on this fibre.
2. Actual `exceptionalFifthPlusFibre N cap w L X pre p` is expressed as one `actualSmallRosserPlus` coefficient at the exact integer quotient q0/(p::pre).prod, subject to its ORIGINAL fifth-power filtered membership and strict high-q gate. This eliminates the entire Rosser-a summation for each fixed genuine (fifth history, sixth occurrence), without changing signs.
3. Apply the existing literal upper Rosser bound `actualSmallRosserPlus_abs_le_one`: each fixed sixth occurrence contributes a q0 fibre with abs <=1, NOT a global stopped coefficient <=1.
4. Prove an occurrence is zero unless its actual sixth p divides q0. Filter the original ordered `fifth.remainingAfter` LIST by p|q0, conserving every repetition, original fifth signed mass, actual history and complete modulus.
5. Prove genuine one-event bound
   `|commonLargeSixthKernel(... exceptionalCentreFibre N) fifth| <= |signedTreeCoefficient true fifth.massAfter| * (fifth.remainingAfter.filter (p|q0)).length`.
   This is a local quantitative envelope controlled by the actual occurrence count; no unproved distinct-prime assumption or physical coefficient identification.

No new fifth/sixth event generator; the preceding `actualFixedSignedFifthTail` relation still supplies the original source. This is a substantive improvement over an unstructured q0 Rosser sum but NOT an H_N, asymptotic or reserve payment.

## Verification
- Remote source readback: confirmed source blob `fa0d9fe34af146a2457b121d7d9400fc75933e31`; 229 lines; 9 theorem bodies; no forbidden `sorry/admit/axiom/unsafe/native_decide` token.
- Independent Python exact-rational diagnostics: 4,950 positive q0 / arbitrary b / finite Rosser support / strict X cases comparing literal full sum to quotient singleton; 8,000 synthetic ordered sixth lists verifying nondivisor p terms zero. 0 failures. No real stopped event generator executed.
- Environment check `lean --version`, `lake --version`, `elan --version`: each exit 127, command not found. No pinned v4.33.0-rc1 + mathlib + native closure. No import staging, Lean elaboration, kernel replay, transitive axioms, independent review or saved87 replay.
- State **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Candidate may contain Lean elaboration/tactic errors; diagnostics do NOT validate proof bodies.
- No CI, Codex, main/master edit, merge/force, extra resources or pin changes.

## Remaining exact obligations
- Convert the per-event local bound to a useful global bound on the TRUE stopped q0 occurrence coefficient, using actual fifth-event mass, gate directions, divisor/ordering structure; do NOT assert its abs <=1 or deduplicate the p list.
- Pay 3q<=N centre, complete modulus primitive discrepancy, modulus-prime correction and N^theta<q<=N signed high-q range using only eligible, accurately registered outside inputs. Ordinary residual integral, actualParent full87, saved87 source/certificate, unfiltered sixth BOTH, RAW eighth, rank9 changed/tagged, three original physical outside invoices and two genuinely independent compiler/density reserves remain open.
- Reconcile candidate in a staged exact fixed Lean dependency environment if available, correct errors before promoting status.

Fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000.
