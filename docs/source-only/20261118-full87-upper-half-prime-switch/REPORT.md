# P1.4 — exact original-prime switch for the upper half of the full-q high tail

Baseline actually re-read: \`95f36a9ed3aeb3b293e17efb1e569610c90fc4a8\`, branch \`chatgpt/p1-full87-superN-cancellation-20261118-0415\`, packet \`docs/source-only/20261118-full87-superN-cancellation/\`. This run re-read REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF, the 301-line prior Lean candidate, the original fifth signed primitive and centre budget, \`ImbalancedChen/ChenInitialPrimeSource.lean\`, and the frozen manuscript. No applicable AGENTS.md was found at the ancestor or target packet paths. A separate continuation branch was created from precisely this baseline, without touching main/master or any other task branch.

## New proof candidate and its mathematical contribution

For the **original target-deleted** \`chenPrimeReceiverSource N\`, every n satisfies 0<n<=N and n=N-P for a unique P in the actual \`chenAdditivePrimeCarrier N\`. For every **complete** integer modulus d with N<2d, any receiver n divisible by d must equal d. Consequently

\`\`\`
receiverTest N d = if d in chenPrimeReceiverSource N then 1 else 0,
                 whenever N < 2*d.
\`\`\`

This is a genuine sharpening of the earlier bound \`receiverTest N d <= floor(N/d)\` into an exact indicator with a prime-source interpretation. It is not an asymptotic upper bound and is not derived from any external PP/PNT input.

For **any fixed finite full-modulus support S** and **any signed weight rho(d)**, the candidate Lean proof reindexes the high-half receiver sum without changing its source:

\`\`\`
sum_{d in S, N<2d} rho(d) * receiverTest N d
 = sum_{P in chenAdditivePrimeCarrier N}
     1_{N-P in S, N<2(N-P)} * rho(N-P).
\`\`\`

The precise strict high-q \`X<d\` is then retained, and the identity is applied to the **actual** physical \`rho\`:
\`actualSmallRoughModuli (policy false) N cap w z\` with \`actualSmallRoughRho (policy false) N cap w z L d\`.
The new \`actual_physical_upper_half_highq_prime_switch\` theorem applies to each original policy without injecting a new policy or coefficient. Finally \`actual_raw_licensed_highq_halves\` gives the exact split of the original physical RAW-minus-LICENSED high-q difference into high-half and lower-half pieces, retaining both signs and the original FULL q; equality at 2q=N belongs to the lower half.

This identifies a **real switched prime-correlation liability** for complete moduli N/2<q<=N (with strict X<q). It does NOT prove cancellation/smallness of that signed prime sum, and it is not a replacement for the N^theta<q<=N estimate. The lower half still includes N^theta<q<=N/2 if theta is below that level; neither half can be dropped. The original physical three outside/producer/licensed-outside invoices are unchanged, and the compiler/density reserves are not paid. The old above-N four-source cancellation remains upstream.

## Evidence

- Candidate source: \`P4AOriginalFull87UpperHalfPrimeSwitch.lean\`, first GitHub commit \`e3ee8e1e9acecc143f07e02961f2bfd7101a4168\`.
- GitHub source blob: \`1eed835206643f3785a60cebb42629538d70ecdb\`. Source re-read from the created branch, 252 lines. Forbidden-token static scan for \`sorry|admit|axiom|unsafe|native_decide\` returned no hits.
- Independent integer diagnostic: for N=1..300, 12 pseudo-random finite modulus supports and integer signed weights per N, and a randomly drawn X, count the actual receiver fibres by integer divisibility and compare with the original-prime switched upper-half high-q expression. **3,600 tests; zero failures**. This diagnostic did NOT evaluate Lean or replay a proof.
- Current runtime check: \`lean\`, \`lake\`, \`elan\` not on PATH. The authorized local Lean/Lake type check cannot be performed without installing the frozen dependency closure; none was installed or upgraded. No CI, no Codex, no cloud resource expansion.
- Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Possible Lean elaboration, rewrite, or tactic errors remain untested. No kernel replay, transitive axiom audit, independent review or saved87 archive authentication.

## Frozen boundary and remaining work

Manuscript \`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b\`, \`paper/source/manuscript-body.tex\`, Git blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`; Lean \`leanprover/lean4:v4.33.0-rc1\`; mathlib \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`; native \`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958\`; c=49044063/25000000, K=8452171/1250000.

No external input was proved or called. The signed sharp-prime PP remains REGISTERED_NOT_PROVED_NOT_CALLED; it requires the actual common rho, complete coprime squarefree modulus at a **fixed** q<=N^theta (theta<1), smooth-singleton and the manuscript's original endpoints and normalization. Neither the high-half prime switch nor the upper bound q<=N meets that admission condition.

Next: (1) obtain the exact pinned local Lean closure if available and compile this source with correct source-only imports, correcting errors; (2) quantify the switched original prime-correlation sum on N/2<q<=N rather than call it small; (3) handle N^theta<q<=N/2 at the SAME receiver-generated signed rho; (4) pay the original primitive/modulus-prime/centre, ordinary residual integral, raw/filtered and compiler/density reserve obligations; (5) original unfiltered sixth BOTH, RAW eighth, actualParent/saved87, rank9, changed/tagged still require independent evidence. P1.4 remains YELLOW.
