# P1.4 — exact one-shell versus full-q primitive AP obstruction (source-only)

Continuation baseline: verified P1.4 HEAD \`a4d60eafae8a83a675e1962a0773f43eff1785d5\`, source commit \`1fdd2512cfb7b8943217aec0c73b7255a4bf66d9\`. New file: \`P4AOriginalFull87OneShellAPGap.lean\`; Git blob \`4f36b722ac7843d4c726ac44902b53729216ce08\`, 347 lines. Independent P1.4 task branch \`chatgpt/p1-full87-one-shell-ap-gap-20261120-0210\`.

## Exact new finite arithmetic distinction

The previous source-only equation uses a SINGLE reflected shell \`P=N-a*b\` with original full rough modulus \`b=(p::pre).prod\`. A manuscript PP AP query at full q has **all** original additive primes satisfying \`P ≡ N (mod q)\`, and cannot be identified with one selected reflected shell. The present source sets \`Q=a*b\`, \`AP_N(Q)={P∈chenAdditivePrimeCarrier N | P ≡ N (mod Q)}\`, \`T_N(Q)=AP_N(Q)\{N-Q}\` and gives the exact finite identity, including zero modulus/out-of-range cases:

    #AP_N(Q) = 1_{N-Q∈chenAdditivePrimeCarrier N} + #T_N(Q).

For the REAL original PLUS-Rosser room \`R_b\`, with unchanged signed \`beta+(a)\` and arbitrary previous reference \`mean(b)\`, the candidate theorem identifies

    sum_{a∈R_b} beta+(a) [1_{N-ab∈carrier} - mean(b)]
      = sum_{a∈R_b} beta+(a) [#AP_N(ab) - mean(b)]
          - sum_{a∈R_b} beta+(a) #T_N(ab).

The non-shell tail is signed. It cannot be dropped merely because each tail cardinality is nonnegative. The equivalence is a finite identity, not an AP distribution estimate.

The candidate proof then preserves the ORIGINAL fifth RAW-only/LICENSED-only sign (negative LICENSED), ordered sixth \`remainingAfter\` multiplicity, \`.both\` and \`.sixthFromBoth\` zero semantics, actual \`sharedRankFour\` states and \`actualFifthSixthWithoutBoth\` filtered by the old \`keepFrozenUpperSurvivor\`. Consequently, after the SAME single lower-half subtraction, the exact candidate physical identity becomes

    (rawStopped - licensedStopped) - lowerHalfOnce
      = frozenSurvivorCarrierMeanRoom(mean)
        + frozenFullQPrimitiveAPRoom(mean)
        - frozenFullQOutsideShellRoom.

This is a strict new explicit analytic interface gap. It is NOT yet the manuscript PP \`rho_N(q)\` class or its smooth coprime mean.

## Verification

- GitHub source commit was created; source path and blob were read back; no \`axiom\`, \`sorry\`, \`admit\`, \`native_decide\` or \`unsafe\` in new source.
- \`lean --version\`, \`lake --version\`, \`elan --version\`: each exit 127 (command unavailable). NO fixed-pin typecheck, no kernel replay, no transitive axiom check, no independent referee. Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**.
- cgroup \`memory.max=4294967296\` bytes, \`cpu.max=400000 100000\` (unchanged).
- Deterministic finite independent arithmetic diagnostics: 35,800 exact AP-fibre tests and 3,580 rational signed-weight tests; zero failures. Example \`N=70,Q=3\`: primitive AP \`[13,19,31,37,43,61,67]\`, selected shell \`67\`, tail cardinality \`6\`. These tests do NOT certify Lean code.
- Frozen paper \`9731290e8f53cffda44129906cde6a965eaa869b\`, file blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`; fixed \`lean-toolchain\` and \`lake-manifest.json\` were read and their Lean/mathlib/native pins match the task. Constants \`c\`, \`K\` unchanged.
- \`AGENTS.md\` checked at repository root, \`docs/\`, \`docs/source-only/\`, previous packet and this task packet: not found. No CI, Codex, main/master edit, toolchain upgrade, local user's machine or resource increase.

## Remaining obligations

1. Stage all source-only imports under correct \`ImbalancedChen/\` module names at fixed versions and run Lean/Lake. Fix actual elaboration errors before calling any theorem COMPILED.
2. Prove/adapt the actual full-q physical coefficient **rho_N(q)** from original small/rough decomposition and all ordered occurrences; the presently used \`Q=a*b\` is a concrete AP modulus for ONE shell, not a proven identification of the manuscript's physical coefficient.
3. Resolve the signed outside-shell tail with a genuine same-rho cancellation or admissible chart/query, without imposing a new sharp q-dependent filter on a smooth \`W_N\`. In particular, signed PP does not give control of this tail separately.
4. Authenticate the common labelled-prime smooth chart \`W_N\`, its \`X_W^(q)/phi(q)\` coprime mean and admitted coefficient class. \`mean(b)\` remains arbitrary and cannot be replaced without an exact finite bridge.
5. Pay the signed discrepancy, chart costs, multiplicities, lower-half three corrections, ordinary residual integral, saved87 certification and both compiler/density reserves against \`H_N\`; BOTH, rank9, changed/tagged branches remain incomplete. No analytically estimated \`o(H_N)\` is claimed.
