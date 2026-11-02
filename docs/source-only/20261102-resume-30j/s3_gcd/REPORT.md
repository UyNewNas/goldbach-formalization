# J s3_gcd: actual cutoff-qualified rough-pair gcd payment

Status: local source step complete, broad task OPEN. `task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`. The three Lean modules are static candidates for independent review. No Lean/compiler/build/CI/checker, finite or numerical replay, Git action, quota query, or subagent was run. Only `docs/source-only/20261102-resume-30j/s3_gcd` was written.

The task row and J README, the original source tree `1_+_1.748_lean_proofs/9ffe5d3.md`, current manuscript body, original medium completion, and I/H predecessor registries and reports were read. The tree's P3.5 yellow leaf remains open. The current manuscript SHA is recorded in REGISTRY. Original global constants c=49044063/25000000 and K=8452171/1250000 are unchanged; the Lean parameter `c` below is the independent logarithmic cutoff exponent, not the manuscript's global c.

## Exact next internal obligation

The medium completion, lines 169–171, first removes large coefficients and nonzero-shift divisor counts. I has an actual close-pair estimate under that literal cutoff, but no estimate for its complement. The earliest large-shift bound remains OPEN here.

This delivery proves the next independently payable original exclusion at lines 172–175: the contribution with `(r,s)>1`, still under both nonzero-shift divisor cutoffs. It uses the original off-diagonal `PairIndex`, original common q,d,m, independently labelled r,n1 and s,n2, original `lambdaTrim`, alpha, primitive-q filter and paperPsi. The far condition is I's literal `not Close T`; no n1/n2 or s/ell gcd condition is added.

The split removes close pairs first, then bad rough pairs among the far pairs. This is a disjoint finite rearrangement of the manuscript's two cutoff-qualified deletions. I already paid all close pairs, including their noncoprime subset. No pair is paid twice in the signed identity.

## Derived arithmetic and count

Write N=atom.U, M=atom.V, x=N*M, Y=keyY atom k, V(D)=M*N^2/Y and H=(log x)^c.

`Part3OriginalS3RoughPairGcd.lean` proves the following from active ORIGINAL summands:

1. The actual trimmed Lambda has inclusive rough prime support. At `strictReceiverCutoff z`, the original receiver arithmetic converts this to strict p>z. A noncoprime pair therefore has f=gcd(r,s)>z. No rough-support hypothesis on replacement coefficients is introduced.
2. Both original congruences descend modulo ell*f, ell=qd. Original primitive residue support makes the residue coprime to ell*f; cancellation of m gives n2=n1 modulo ell*f. The proof permits r to share prime factors with ell and preserves repeated prime powers.
3. The actual alpha carrier is inside [N,2N]. Since ell>=Y/2, the n2 fibre has at most `2*N/(Y*z)+1` elements.
4. An explicit injective sigma-type encoding retains `(m,n1,q,d,f,n2,r,s)`, with an explicit decoder. q,d cost H^2; f costs H; r,s cost H^2. The two original Lambda coefficients cost H^2. The original first (m,n1) carrier has at most 12*x elements.

The resulting proved estimate is

```
norm(badPairDeleted) <= 12*x*(2*N/(Y*z)+1)*H^7.
```

The exponent seven includes every divisor multiplicity and both actual coefficients. No divisor subpower is used on a logarithmic main term. The endpoint `12*x*H^7` is retained. The result is uniform in the separation width T, including I's already chosen width.

## Original cutoff and outside payment

`Part3OriginalS3RoughPairGcdPayment.lean` obtains

```
24*V(D)*(log x)^(7*c)/z + 12*x*(log x)^(7*c).
```

At the ORIGINAL `roughZ x=x^(1/(loglog x)^3)`, the existing proved rough-cutoff growth lemma supplies `(log x)^(A+7*c)<=z`. Original occupied-key geometry gives `x^(1+sigma/2)<=V(D)` and pays the endpoint. One threshold, before every atom and key, therefore gives

```
norm(badPairDeleted) <= 36*V(D)/(log x)^A.
```

The theorem also permits numeric receivers z>=roughZ x; taking z=roughZ x recovers the original source exactly. This is an explicit cutoff geometry condition, not an assumed gcd-saving estimate.

For the actual outside sum, local precision is the existing `D=A+betaMomentOrder(B)+12`. The proof uses original `outerL2<=6*Y*betaL2`, the actual beta divisor-square mean, and BOTH original owner-bank multiplicities. It obtains

```
actualOuterGcdBudget <=
  432 * betaLogConstant^betaMomentOrder(B) * (2*keyLogConstant)^12
      * x^2/(log x)^A.
```

Fixed B,sigma,kappa,c,A precede constants and threshold; c0, atom, signed residue, receiver and key follow. Original `0<sigma<1/100`, `MediumAdmissible`, c0>0, smooth trim and occupied key bank are retained. No new SW, Shiu, spectral, correction or final-residual estimate is assumed.

## Signed original consumer

`Part3OriginalS3RoughPairGcdResidual.lean` proves the exact identities

```
farFull = coprimeFarFull + badPairDeleted
primitiveS3 = largeShiftFull + coprimeFarFull + badPairDeleted
              + closeDeleted + restorationCorrection.
```

Only r/s coprimality is imposed on `coprimeFarFull`; its name does not claim it is a clean E2 Fourier source. Full and deleted terms are identified only under the TWO nonzero-shift cutoffs.

`largeShiftFull` remains the very same I-defined complement. It still contains the two original single-zero additions, with their compensating minus signs inside H's unchanged restoration correction. No double-zero diagonal is restored.

The final theorem `exists_actualResidualFunctional_gcd_paid` bounds the EXISTING `actualResidualFunctional` by a newly explicit unpaid ledger plus C*x^2/log(x)^A. The unpaid ledger replaces only farFull by coprimeFarFull; it retains full largeShiftFull, the full off-diagonal zero subtraction, omitted modes, retained Fourier diagonal, roughReplacementCorrection, genuineDiagonalZero and all four original S2 norms with their factor 2. All original outside weights remain literal. No bound on this unpaid ledger is a premise or conclusion.

## Exact remaining blockers

- The earliest large-coefficient/nonzero-shift cutoff estimate (169–171), and cutoff reinstatement (181), remain OPEN. This work does not pay largeShiftDeleted or largeShiftFull.
- Original n1/n2 and s/ell gcd exclusions remain OPEN. They are still inside coprimeFarFull.
- Close/gcd zero-mode restoration at 212–217 remains OPEN. The independently existing full off-diagonal zero is retained and no equality to a cleaned/restored principal term is asserted.
- Original physical-to-clean E2 Fourier/CRT disintegration, retained-phase/Abel estimates, omitted-mode and Fourier-diagonal payments, genuine zero diagonal, S2 packets, spectral return and full restricted-medium assembly remain OPEN.
- Source-only imports need installation, independent review and user-owned elaboration/kernel verification. No Mathlib local source checkout or transitive verification is claimed.

The I-reported inherited source-body issue was rechecked: exact draft `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-ExactProduct-Sol6/Part3MediumLiteralS3DeletedCarrier.lean` still places the second hmod branch at line 56 after `deletedIndicator_norm_le_one`, outside the earlier theorem's scope. This is a concrete inherited elaboration blocker, not a mathematical manuscript contradiction. Root was notified and no predecessor was edited. REGISTRY pins the actual bytes rather than pretending the import closure is repaired.

No new suspected manuscript contradiction was found. The contribution is a substantive exact-source gcd count and its complete original outside payment, with the broader requested cutoff/gcd/zero-restoration target explicitly OPEN.
