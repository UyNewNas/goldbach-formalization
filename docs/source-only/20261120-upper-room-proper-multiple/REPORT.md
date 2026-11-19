# P1.4 — original upper room: eliminate the proper-receiver AP tail

Status: SOURCE_ONLY / UNEVALUATED / UNCOMPILED. P1.4 remains YELLOW.

## Provenance
Verified previous independent task HEAD: 913928e25afa5c4db680d60598ba71bbb9243cd7 (the actual receiver proper-divisor continuation).
New branch: chatgpt/p1-full87-upper-room-proper-multiple-20261120-0410, created directly from that HEAD.
Source: docs/source-only/20261120-upper-room-proper-multiple/P4AOriginalFull87UpperRoomNoProperMultiple.lean (246 lines).
Source blob after namespace fix: bafa9f08d8681fd962427a911daebe62e6c9b591; candidate source commit: 333b8a004c7dd355dc8b6caeadbf026b61638644.
Prior intermediate source commit 8f2595909af20497192e63e60c4c0008a91404f3 has an invalid open-declaration namespace; it was corrected in 333b8a004c7dd355dc8b6caeadbf026b61638644. Use the latter, NOT the initial source commit.

## Substantive arithmetic correction to the prior outstanding obligation
The preceding full-Q AP split was correct for unrestricted Q but overcounted an apparent unresolved correction when interpreted on the ACTUAL original upper quotient room.

The existing source defines
  b=(p::pre).prod,
  fullUpperQuotientRoom = Ico(max(floor(N/(2b))+1, floor(X/b)+1),
                             min(ceil L, floor(N/b)+1)).
The actualPrimitiveRosserRoom is a subset of this literal original interval. Thus every a in that room satisfies b>0 and N < 2*a*b. This uses the strict upper-half gate 2P<N, NOT any sieve estimate.

The previous candidate exact receiver reformulation showed that omitted full-q AP shells lie in
  {r in chenPrimeReceiverSource N : q | r AND q < r},
where r<=N and q=a*b. A strict proper positive multiple r of q necessarily obeys 2q<=r. Combining 2q>N and r<=N gives a contradiction. Therefore on the actual upper room:
  outside_shell_card(N,a*b) = 0,
  originalProperReceiverDivisorKernel(N,...,r) = 0 for every actual r,
  originalProperReceiverDivisorConvolution(N,...)=0,
  frozenProperReceiverConvolution(...)=0.

All PLUS-Rosser signed beta coefficients, fifth RAW/LICENSED tags, ordered sixth occurrence multiplicities, sharedRankFour parent, frozen survivor filter and the lower one-time deduction remain unchanged. The candidate stopped identity reduces to
  Physical_stopped - lower_once = frozen_mean(mean) + frozen_true_full_Q_AP(mean).
The mean remains an ARBITRARY function b -> R; this identity does NOT authenticate the manuscript's smooth same-rho PP mean or prove H_N payment.

## Actually executed checks
- Read complete preceding Lean source, prior REPORT/HANDOFF/REGISTRY/INPUT_BOUNDARY, and original FullUpperQuotientRoom and ActualPrimitiveRosserRoom definitions. No AGENTS.md found at repo root, docs/, docs/source-only/, or prior packet directory.
- Compared previous live branch with 913928e: identical (ahead 0, behind 0); created this separate branch; no main/master mutation.
- Frozen manuscript paper/source/manuscript-body.tex at 9731290e8f53cffda44129906cde6a965eaa869b: blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79 confirmed. The original eq:current-PP was read in the previous packet, NOT applied here.
- Read lean-toolchain and lake-manifest pin: Lean leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native goldbach 09b97db5764ade1246bfb77206baa1b124760958. Constants c=49044063/25000000, K=8452171/1250000 unchanged.
- Explicit local commands lean --version, lake --version, elan --version: exits 127, command not found. Memory cgroup 4294967296 bytes; cpu.max 400000 100000. No matching compiler, no Lean elaboration, no kernel replay, no transitive axiom audit, no independent review.
- Separate finite Python arithmetic diagnosis: 206,354 (N,b,a) original strict upper quotient pairs for even N in 2..500, b in 1..N+2. All satisfy 2ab>N and all unrestricted primitive carrier congruence classes have zero non-shell AP fibres. This is not an evaluation of the Lean candidate.
- Static forbidden escape scan on new source: no new axiom/sorry/admit/native_decide/unsafe. Static checks are not Lean acceptance.
- No Codex, user computer, CI dispatch, workflow rerun, forced push, upgraded toolchain or increased resources.

## Exact outstanding work
1. Stage source-only dependency imports under their original ImbalancedChen module names in a matching pre-existing fixed-pin environment; typecheck the 246-line candidate, repair all elaboration errors, then separately kernel-replay/audit axioms.
2. Prove true physical rho_N(q) aggregation and same-q coefficient class; local q=a*b alone is not yet the manuscript's rho_N(q).
3. Authenticate the fixed, smooth labelled-prime W_N, actual coprime X_W^(q)/phi(q) mean, pre-N-fixed parameters, admitted external theorem and exact signed H_N payment.
4. Pay lower-half primitive/modulus/centre corrections separately; this upper-half identity does not annihilate those.
5. Finish ordinary residual integral, saved87 original certificate, BOTH, rank9, RAW, changed/tagged arithmetic, two independent compiler/density reserves and final same-rho physical account.

The earlier 'proper divisor tail must be analytically paid' is no longer an outstanding upper-room obligation if and only if the new finite source passes Lean verification. Do not globally claim the tail is zero for all q: e.g. N=70,q=3 outside the actual upper room does have non-shell members.
