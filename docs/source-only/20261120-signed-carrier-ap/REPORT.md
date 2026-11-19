# P1.4 — exact signed primitive-carrier AP return (source-only)

Continuation baseline: `8ae36e34cd1864b92e92abc4ef36ca5f3f8b267f`, branch `chatgpt/p1-full87-beta-mass-envelope-20261120-0010`. The SOURCE commit after one formula-oriented patch is `9b5df7fbe3b2502765c6460f3ad3194259586e6f`; source blob `b83aec43dd8919728dcbe6acd78c5467be2d51cd` (`P4AOriginalFull87SignedCarrierAP.lean`, 276 lines). Task branch: `chatgpt/p1-full87-signed-carrier-ap-20261120-0110`.

## Actual new mathematical step

The preceding round had an exact upper primitive-carrier *jump* invoice and then a factor-two absolute beta-mass envelope. Neither a bound on EVERY modulus nor a bound on every beta jump follows from the manuscript's signed PP distribution estimate. Instead of multiplying that unverified local absolute bound through all occurrences, this source returns to an exact SIGNED arithmetic discrepancy.

With the original full sixth rough modulus `b=(p::pre).prod`, original primitive quotient room `R_b`, actual PLUS Rosser beta `beta^+(a)`, original reflected primitive prime carrier `P_N^{car}`, and arbitrary reference `mean : Nat -> Real`, prove as a source-only Lean candidate:

    sum_{a in R_b} beta^+(a) *
       (1_{N-a*b in P_N^{car}} - mean(b))
       = originalRoomCarrierJumpCorrection(N,cap,w,L,X,pre,p,mean).

Proof: use actual coprimality of a*b to N to cancel centre-prime contributions *pointwise after beta weighting*, rewrite the carrier-weighted sum as the original prime-prefix filtered sum, then apply the existing exact reflected Abel identity and exact centre cancellation. No absolute values or nonnegative coefficient assumptions are inserted.

A second candidate transports this equality through `fifth.remainingAfter` as a List, the genuine RAW-only/LICENSED-only sign (including negative LICENSED), unchanged BOTH/sixthFromBoth zero behavior, original `sharedRankFour` state List, `actualFifthSixthWithoutBoth` producer, and original `keepFrozenUpperSurvivor` selector. It yields the finite physical equality:

    (rawStopped - licensedStopped) - lowerHalfOnce
      = frozenSurvivorCarrierMeanRoom(mean)
        + frozenSurvivorSignedPrimitiveCarrierAPRoom(mean).

This preserves the actual signed cancellation BEFORE any triangle inequality. It is not yet a PP estimate, integral or H_N gain; the right-hand discrepancy is EXACT but not bounded asymptotically.

## Critical input mismatch made explicit

Manuscript `paper/source/manuscript-body.tex`, label `eq:current-PP`, asserts a **SIGNED** coefficient-class estimate

    sum_q rho_N(q) *
      (sum_{p_1 ... p_k equiv N (mod q)} W_N(...) -
       X_W^(q)/phi(q)) = O_{A,W}(N / (log N)^A).

The SAME original signed rho_N occurs in both terms. This is not a uniform bound on each fixed b, not a max over beta jump endpoints, and not an estimate for arbitrary sharp filters. The present `mean(b)` remains arbitrary and is NOT the authenticated `X_W^(q)/phi(q)` normalization. One must identify the complete physical q (which may include beta's small-prime quotient factor a), transform the exact original frozen signed sum into the actual admitted rho_N class with a common smooth W_N, and pay all chart/multiplicity/parameter costs before applying that manuscript input. No such identification or analytic payment is claimed here.

## Source validation, exact limits

- Source-only GitHub commit and blob read back; static inspection: 4 public theorem bodies and one private local proof, no axiom/sorry/admit/native_decide/unsafe.
- Executed `lean --version`, `lake --version`, `elan --version`; ALL exited 127 because binaries not found. Thus actual fixed-pin elaboration was NOT executed, and source theorem bodies remain UNEVALUATED.
- cgroup `memory.max=4294967296` bytes, `cpu.max=400000 100000`; no resource increase.
- Fixed toolchain manifest: Lean v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native goldbach 09b97db5764ade1246bfb77206baa1b124760958.
- Frozen manuscript commit 9731290e8f53cffda44129906cde6a965eaa869b, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79 read and matched; c=49044063/25000000 and K=8452171/1250000 unchanged.
- `AGENTS.md` at repo root, docs, source-only and this packet were explicitly queried, not found (404). No CI, Codex, local user machine, main/master merge, or dependency edits.

Validation remains **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**; NOT KERNEL_REPLAYED, no transitive axiom audit or independent referee. P1.4 parent stays YELLOW.

## Exact unpaid obligations

1. Stage fixed-pin source-only import closure, run Lean/Lake, fix actual type/elaboration errors. Import path for this file is `ImbalancedChen.P4AOriginalFull87SignedCarrierAP` after correct temporary staging; the docs path is not itself Lake's module path.
2. Identify actual `rho_N(q)` of manuscript PP with the unchanged full q and beta quotient; restore common smooth `W_N`, admissible factorization/marked-branch conditions and the right mean `X_W^(q)/phi(q)`. The present arbitrary `mean(b)` is NOT yet this term. Record all external analytic prerequisites separately, without proving them here.
3. Apply a signed estimate only after (2); do not infer the absolute `E_b` used in prior packets from signed PP. Pay the true globally signed error relative to `H_N` or else prove an independent admissible local absolute estimate.
4. Lower-half three corrections; ordinary continuation integral; saved87 numeric and full geometry; BOTH/rank9/changed/tagged; separate compiler/density reserves and final same-rho physical closure.
