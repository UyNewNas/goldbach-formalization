# P1.4 — exact sharp-prime recentering on the original full87 physical rho

## Provenance and actual scope
Verified predecessor: 8738450e2c693ef53c9cf26643a441c0006b08df on chatgpt/p1-full87-owned-primitive-ledger-20261111. This independent packet lives on chatgpt/p1-full87-signed-sharp-recenter-20261111. Do not reset to 9649ab3.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. The actual source §4 eq:current-PP and Sharp original-prime endpoint lemma lem:current-sharp-prime / eq:current-sharp-pi were inspected. Fixed tools: Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native 09b97db5764ade1246bfb77206baa1b124760958. c=49044063/25000000, K=8452171/1250000.

## Actual new manuscript-internal identity
Use only the existing full-modulus definitions: primeMass N = π(N), densityTest(d)=1/φ(d), modulusPrimeTerm(N,d)=number of primes p≤N dividing d divided by φ(d), primitiveError=AP-exactCoprimeMean, receiverTest=AP-centrePrimeAP. The new sharpPrimeError is AP-π(N)/φ(d). The Lean candidates establish exactly

    primitiveError(N,d) = sharpPrimeError(N,d) + modulusPrimeTerm(N,d)
    receiverTest(N,d) = π(N)*densityTest(d) + sharpPrimeError(N,d) - centrePrimeAP(N,d).

Substitute the FIRST identity into the PREEXISTING actual same-rho receiver_gain_decomposition, then expand the original physical gain's linearity. The resulting candidate is

    Gain(receiver) - π(N)*Gain(density)
       = Gain(sharpPrimeError) - Gain(centrePrimeAP).

The modulus-prime term cancels EXACTLY only after this change of centering. It is not pointwise zero; it is not omitted in the exact-coprime representation. The old 3-part primitive/modulus/centre absolute budget remains valid as a different route. Never pay modulusPrimeTerm a second time after selecting the sharp-error route.

## Same physical signed full-modulus coefficient
Let A and B be the ORIGINAL full-modulus Finsets of the actual licensed sixth and finite eighth policies. The new definitions are U=A∪B and

    rhoChange(d) = (if d∈A then rhoSixth(d) else 0)
                 - (if d∈B then rhoEighth(d) else 0).

A finite support union proof shows Gain(G)=sum_(d∈U) rhoChange(d)*G(d). The existing exact original87 owner/strict-trim state partition then gives

    sum_(c:original Cell) ownedSource(c,sharpPrimeError)
      = sum_(d∈U) rhoChange(d)*sharpPrimeError(d).

Every coefficient is the existing sign-attached physical rho on its COMPLETE small/rough modulus. Repeated source occurrences were already retained in the earlier list equality; regrouping by physical modulus happens only after the true sum. No new policy, parent, beta, mask, weight, geometric zero-error or PP class was introduced.

Crucial distinction: the frozen PP and sharp-endpoint estimates are SIGNED. They do not imply a bound on the previous packet's absolute per-leaf primitive invoice. E.g. signed discrepancy 1-1=0 has absolute invoice 1+1=2. Nor is rhoChange itself asserted licensed as a new PP class. The two ORIGINAL sixth/eighth coefficient instances need separate admissibility checks and estimates.

## Conditional internal inequality (inputs NOT proved)
The candidate full87_receiver_if_sharp_PP_pair proves that if the two explicit actual physical signed estimates satisfy

    |physical(sixthPolicy,sharpPrimeError)| ≤ ε6,
    |physical(eighthPolicy,sharpPrimeError)| ≤ ε8,

then

    |Gain(receiver)-π(N)*Gain(density)| ≤ ε6+ε8+absoluteGainBudget(centrePrimeAP).

Those signed bound hypotheses are NOT supplied here. Applying the manuscript's sharp-prime lemma still requires squarefree bounded complete support q≤N^θ for θ<1, coprimality (q,N)=1, actual licensed smooth-singleton class, legal local integer X, endpoint smoothing, cutoff/trim, fixed parameters first, and the SAME H_N and signed rho. No claim of these prerequisites or of o(H_N) is made. The centre-prime term is still unpaid. External §4 PP and sharp endpoint are REGISTERED_NOT_PROVED / NOT_CALLED.

## Check and explicit limits
New source P4AOriginalFull87SignedSharpReceiver.lean, Git blob 74949535b1ae9e5a46e6f9e12432f412fead4b03. Candidate proof bodies cover original prime centering, receiver cancellation, signed union-support coefficient, original87 owner call-site and the conditional two-instance bound.

Executed exact Python Fraction checks: 4410 finite even-N/modulus prime recenterings (4≤N≤100 even, 1≤d≤90), 20000 synthetic signed support-union equalities, 5000 receiver cancellations, and a signed-vs-absolute counterexample: all passed. This is NOT original87 source replay, PP, saved87 integration, Lean elaboration or kernel verification.

Checked local lean/lake/elan --version: each unavailable, exit 127. No matching pinned dependency tree was available for imports. SOURCE_ONLY / UNEVALUATED / UNCOMPILED, no kernel replay, transitive axiom audit or independent review. No CI/Codex/main/master/force push/resource increase.

## Exact remaining yellow obligations
1. Actual sixth/eighth full-q sharp PP eligibility and quantified signed estimates on SAME H_N; sharp smoothing with valid legal complete-product local X and fixed-parameter quantifiers.
2. Actual centre-prime gain bound o(H_N), not an assertion of zero.
3. Ordinary continuation to residual integral on the real shared history, weighted actualParent invoice control, saved87 original numerical witnesses.
4. Low/high q, raw/finite/filtered, rank9, changed/tagged and both distinct reserve payments.
5. Fixed Lean typecheck, kernel replay, transitive axiom audit, archive numerical replay and independent review.

P1.4 stays YELLOW.
