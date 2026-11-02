# K s3_n_gcd: original alpha-gcd exclusion and outside payment

Status: local source step complete; the broad original S3/restricted-medium target remains OPEN. `task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`. The three Lean modules are static candidates awaiting independent review and later user-owned elaboration. Only this K task directory was written. No compiler, build, CI, finite certificate or numerical replay, Git action, quota query or subagent was used.

The K task row and README, current manuscript 125–238, original medium completion through section 4, source tree P3.5, J's complete rough-pair source/payment/residual and its medium review were read. J has a narrow SOURCE_REVIEW_PASS, not kernel verification. Current original c=49044063/25000000 and K=8452171/1250000 are unchanged. The Lean variable `c` is the independent logarithmic shift-cutoff exponent.

## Exact source and arithmetic

This delivery handles completion 172–177's `(n1,n2)>1` deletion in J's actual `coprimeFarFull`. The carrier is still the original `offDiagonalCarrier` of literal `PairIndex`; every term has the same q,d,m and independent labels (r,n1),(s,n2), primitive q filter, actual `lambdaTrim` pair, original alpha pair and joint `paperPsi`. Both original shifts remain nonzero and have tau at most H. Close pairs and `(r,s)>1` have already been removed by I/J. No `(s,ell)=1` restriction is imposed here.

For an active term let f=gcd(n1,n2), ell=qd, N=atom.U, M=atom.V, x=NM, Y=keyY, and Z=roughZ(x). `alphaBadActive_gcd_data` derives:

- f>Z from the nonzero actual alpha coefficient and its original roughness gate;
- 0<f<=2N, f divides both n1 and n2;
- gcd(f,ell)=1 from the original first product congruence and primitive moving residue;
- n2=n1 modulo ell from I's original two-product cancellation.

The alpha roughness is at Z, independently of the Lambda receiver. A larger receiver z does not imply alpha is z-rough, and this proof never makes that inference. Local counting permits arbitrary z,y; the outside statement uses the existing numeric receiver `strictReceiverCutoff z` with z>=Z, including the exact original z=Z.

Neither the manuscript's medium alpha class nor `MediumAdmissible` assumes squarefree alpha. The proof uses the full gcd and handles prime powers; it therefore preserves all original squarefree subclasses without dropping the non-squarefree allowed cases. No auxiliary squarefree hypothesis, replacement coefficient family or assumed source identity is introduced.

## Actual count and logarithmic payment

`Part3OriginalS3AlphaGcdCount.lean` injects every active original label into

```
(m, f, n1, q, d, n2, r, s).
```

There is an explicit decoder and injectivity proof. The counts are derived, not premises:

- The original paperPsi m carrier has at most 4M points.
- For each actual f<=2N, the actual alpha multiples count is at most N/f+1<=3N/f.
- The original q,d divisors of the first nonzero shift cost H².
- The second point simultaneously satisfies n2=n1 mod ell and f|n2. Coprimality gives lcm(f,ell)=f*ell, so its count is at most 2N/(Yf)+1. This is the second reciprocal f factor.
- The original r,s divisors cost H². The actual pair of Lambda coefficients costs H²; alpha and paperPsi remain bounded by one.

The full finite gcd bank is summed with an elementary reciprocal-square telescope and the harmonic bound. No pointwise divisor subpower multiplies the 1/Z main term. The result is

```
norm(alphaBadDeleted)
  <= (48*V(D)/Z + 12*x*(1+log(2N)))*H^6,
V(D)=M*N^2/Y.
```

The entire second-point +1 endpoint remains in the harmonic term. With H=(log x)^c and log x>=1, `1+log(2N)<=3 log x` gives

```
48*V(D)*(log x)^(6c+1)/Z + 36*x*(log x)^(6c+1).
```

`Part3OriginalS3AlphaGcdPayment.lean` pays the first term by the existing proved growth of the literal original Z and the endpoint by the actual occupied geometry `x^(1+sigma/2)<=V(D)`. One threshold before every atom, signed residue, receiver, key and separation width gives

```
norm(alphaBadDeleted) <= 84*V(D)/(log x)^A.
```

No cutoff-complement estimate, Shiu/SW estimate or gcd correction is assumed. All fixed B,sigma,kappa,c,A precede constants and threshold. The count is uniform in T, including the original close width selected after c.

The outside theorem uses the literal `outerL2<=6Y*betaL2`, actual beta-square mean and both original owner-bank multiplicities. At D=A+betaMomentOrder(B)+12 it proves

```
actualOuterAlphaGcdBudget
  <= 1008*Cbeta^betaMomentOrder(B)*(2*Ckey)^12*x^2/(log x)^A.
```

Here 1008=84*6*2; no outside weight is suppressed.

## Signed consumer and retained obligations

`Part3OriginalS3AlphaGcdResidual.lean` proves the exact signed split

```
coprimeFarFull = doubleCoprimeFarFull + alphaBadDeleted,
primitiveS3 = largeShiftFull + doubleCoprimeFarFull + alphaBadDeleted
              + badPairDeleted + closeDeleted + restorationCorrection.
```

Deleted/full terms agree only because both shifts are nonzero. The new retained packet imposes exactly r/s and n1/n2 coprimality. It is not declared to be clean E2. The final theorem inserts the proved outside payment into the existing `actualResidualFunctional`, with explicit `unpaidOriginalAlphaGcdLedger` and one combined arbitrary-log cost for prior I/J payments and this payment.

The remaining ledger keeps the original full `largeShiftFull`, genuine off-diagonal zero subtraction, omitted modes, Fourier diagonal, rough replacement, genuine diagonal zero and all four S2 norms with factor 2. Old single-zero terms and their compensating restoration signs are unchanged. There is no double-zero restoration.

Still OPEN:

- The original large-shift/large-coefficient cutoff complement and its later reinstatement (169–171,181).
- `(s,ell)>1` exclusion, handled separately from this n-gcd source.
- Close/gcd zero-mode restoration (212–217), actual physical-to-clean E2 CRT/Fourier binding and the unchanged residual packet estimates.
- Retained-phase/Abel payment, common completed-variable spectral return, all-key S123/restricted-medium assembly and the full original P3.5 yellow leaf.
- Source-only import installation, inherited source repair, independent review, elaboration and kernel verification.

The inherited source issue was rechecked at `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-ExactProduct-Sol6/Part3MediumLiteralS3DeletedCarrier.lean`: the second hmod branch remains displaced to line 56 after `deletedIndicator_norm_le_one`, outside its original proof. This is an inherited concrete source issue, not a compiler diagnosis or manuscript contradiction. It was not edited.

REGISTRY records actual raw bytes/hashes, installation presence, imports, exact declarations and selected dependency/reference pins. Mathlib is pinned by the existing manifest; its local package sources are absent, so no local Mathlib source or transitive verification is claimed. There are no new external assumptions, axioms, admitted obligations or decisive finite guards.
