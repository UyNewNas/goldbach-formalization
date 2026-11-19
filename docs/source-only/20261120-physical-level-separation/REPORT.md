# P1.4 — distinguish full reflected receiver Q from bounded physical sieve modulus d

Status: SOURCE_ONLY / UNEVALUATED / UNCOMPILED; P1.4 remains YELLOW.

## Provenance and actual recovery

- Prior verified LIVE HEAD: b25c0cd95edb7934d85c79b9beb4d35984697f4f.
- This independent continuation branch: chatgpt/p1-full87-physical-level-separation-20261120-0505 (created from that exact commit, not master).
- New Lean source commit: f6637ec2054653579763fa853a4dc7a8965ce7af.
- Source: docs/source-only/20261120-physical-level-separation/P4AOriginalFull87PhysicalLevelSeparation.lean, 120 lines, blob cc25cdbc586269761706a9876426a07c0aab0ea1.
- Original upper-room import: docs/source-only/20261120-upper-room-proper-multiple/P4AOriginalFull87UpperRoomNoProperMultiple.lean, candidate source commit 333b8a004c7dd355dc8b6caeadbf026b61638644, blob bafa9f08d8681fd962427a911daebe62e6c9b591.

## Actual mathematical discovery

The LAST candidate already established that for every a in the ORIGINAL actualPrimitiveRosserRoom,
  Q = a * (p::pre).prod satisfies 2Q > N.
The full-Q AP counting identity at this Q is finite and correct as an ORIGINAL reflected one-shell equality. However the manuscript physical upper coefficient rho_N(d) has bounded support d <= N^theta, theta<1; its cited numerical upper level is theta_*=599/1000 BEFORE the small complete-scale adjustment (paper/source/manuscript-body.tex, eq:current-physical-upper and nearby text). In particular a physical bound B with 2B <= N is DISJOINT from every Q in the original upper room.

The new Lean candidate formalizes four finite facts, without inventing rho:
1. For all original a and any B with 2B<=N, B<Q.
2. The entire actual full-Q image misses every supplied physical support S bounded by B.
3. Any (unspecified) coefficient rho supported <=B vanishes at each such original Q.
4. The signed PLUS-beta times rho(Q) times original full-Q AP-minus-mean sum is exactly 0.

The last statement is ONLY a diagnostic for the hypothetical substitution d=Q. It does NOT imply the actual original unweighted full-Q AP room, physical stopped value or lower correction is zero. It instead proves this proposed SAME-Q identification cannot be the bridge to the manuscript's physical rho when its actual support is below N/2.

For theta=599/1000, the inequality theta<2/3 and N>=8 implies N^theta<=N^(2/3)<=N/2. This is a plain real inequality explained here, NOT a Lean proof in this packet. The new Lean source uses exactly the finite premise 2B<=N, without silently adding a physical-level theorem.

This is a correction to the ADAPTER, not a counterexample to the paper's physical divisor-sum identity R_N(n)=sum_{d|n}rho_N(d). The correct bridge must keep n=N-P (or receiver n=ab) distinct from divisor modulus d|n, and derive the genuine rho_N(d) from the original actual policy. Never replace the physical d with n itself.

## Checked evidence and boundary

- Read live prior REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and all 246 lines of previous source; examined earlier fullUpperQuotientRoom, original receiver-tail and one-shell AP modules.
- Read frozen manuscript at commit 9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. The manuscript explicitly states physical bounded squarefree support and theta_* = 599/1000 and uses SAME rho_N in eq:current-PP.
- Read lean-toolchain: leanprover/lean4:v4.33.0-rc1; lake-manifest pins mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 and native goldbach 09b97db5764ade1246bfb77206baa1b124760958.
- Constants c=49044063/25000000 and K=8452171/1250000 unchanged.
- No applicable AGENTS.md found at repo root, docs/, docs/source-only/, or this packet's parent directory in the last checked branch; new packet is restricted to its own files.
- Actual current environment checks: git available; lean --version, lake --version and elan --version return 127 (command not found). cgroup memory.max=4294967296. No fixed-pin Lean import staging, elaboration, compilation, kernel replay, axiom audit or independent review.
- Source is a 120-line SOURCE_ONLY candidate. Static forbidden escape scan found no axiom/sorry/admit/native_decide/unsafe. This is NOT kernel acceptance.
- No Codex, user computer, new GitHub Actions/CI, workflow rerun, forced push, master edit, extra cloud resource or toolchain upgrade.

## Remaining proof obligations, not discharged

1. REAL original finite policy coefficient rho_N(d), d dividing n=N-P: show its exact small/rough factorization, support and class, without substituting receiver n for modulus d.
2. Prove/compile the internal physical support bound B with 2B<=N at the original fixed parameters, including the small complete-scale adjustment, for all sufficiently large even N. If using theta_*=599/1000, formalize real power/integer-floor bridge.
3. Aggregate the EXACT rho_N(d) from original dynamic parent, occurrence signs, Rosser weights, squarefree condition and fifth/sixth original lists; link physical R_N(n)=sum_{d|n}rho_N(d) to the true labelled-prime PP discrepancy.
4. Match fixed smooth W_N, SAME rho_N(d), exact X_W^(d)/phi(d), fixed-before-N parameters, licensed input class and H_N error. Do not extrapolate to sharp q-dependent shell filters.
5. Lower-half primitive/modulus/centre errors, ordinary integral, saved87 geometry/numerics, BOTH, rank9, changed/tagged and the two independent reserves remain open.
6. Fixed-pin Lean elaboration, kernel replay, transitive axiom audit and independent peer review all remain pending.

New result is intentionally a scope correction, not P1.4 completion.