# K s3_s_ell: actual rough/level gcd exclusion

Status: the cutoff-qualified `(s,ell)>1` count, original logarithmic payment and original outside residual insertion have source-only proof bodies. The broad original S3 and P3.5 targets remain OPEN. `task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`. Independent review and user-owned elaboration remain necessary. No compiler, build, CI, finite decision/certificate execution, numerical replay, Git action, quota query or subagent was used. Only this assigned K directory was written.

The K task row/README, original tree `1_+_1.748_lean_proofs/9ffe5d3.md`, current manuscript 164–238, original medium completion 114–181, J's three exact source files/REGISTRY/REPORT and its narrow medium review were read. J's review grants SOURCE_REVIEW_PASS only, not kernel credit. Current manuscript and all direct imports are pinned in REGISTRY. Original global c=49044063/25000000 and K=8452171/1250000 are unchanged. The Lean variable `c` is a separate logarithmic cutoff exponent.

## Original source and new arithmetic

The correction is the literal subset of J's `coprimeFarFull` with `(s,ell)>1`, ell=qd. It retains the original off-diagonal `PairIndex`, common q,d,m, both labelled r/s and n1/n2 slots, actual trimmed Lambda coefficients, alpha coefficients, primitive-q support and joint paperPsi. Its filters are BOTH original nonzero-shift divisor cutoffs, `not Close T`, `(r,s)=1`, and `(s,ell)>1`. No n1/n2 coprimality or replacement source is assumed.

`Part3OriginalS3RoughLevelGcd.lean` proves a new arithmetic mechanism, distinct from J's common r/s factor:

1. Nonzero **second** actual Lambda gives roughness of s. At the original strict receiver, f=gcd(s,ell)>1 therefore satisfies f>z, including repeated prime factors.
2. Since f divides ell and ell divides the first nonzero shift, f lies in that first shift's divisor bank. The first shift cutoff supplies at most H choices of f.
3. Since f divides s, the second original congruence descends to `mn2=a mod ell*f`. Original primitive residue support at ell and f|ell imply `(a,ell*f)=1`.
4. Every nonempty second-product fibre has one n2 residue modulo ell*f: choose any actual member n0 and cancel m between its product congruence and each other member's. The proof does **not** assert `n2=n1 mod ell*f`; n1 need only satisfy the original ell congruence. Empty fibres are treated explicitly.
5. Original alpha support in [N,2N] and ell>=Y/2 give fibre cardinality at most `2*N/(Y*z)+1`.

The injective sigma-type code retains `(m,n1,q,d,f,n2,r,s)` with an explicit decoder. The first pair carrier costs at most 12x, q/d cost H², the new level gcd costs H, and r/s labels cost H². Actual coefficient norms cost another H². Thus, with N=atom.U, M=atom.V, x=NM, Y=keyY and V(D)=MN²/Y, the proved bound is

```
norm(badLevelDeleted) <= 12*x*(2*N/(Y*z)+1)*H^7.
```

The endpoint `12*x*H^7` is retained. This proof uses actual finite divisor banks and primitive progression spacing; no assumed count, Shiu boundary, divisor mean, subpower substitution or desired excluded-source estimate appears. The count is uniform in the separation width T.

## Original logarithmic and outside payment

`Part3OriginalS3RoughLevelGcdPayment.lean` reuses the reviewed J payment argument with the newly proved, distinct `badLevelDeleted_le` as its source input. The numerical constants and precision are justified by that bound, rather than by comparing this new correction to J's r/s correction. For H=(log x)^c it proves

```
norm(badLevelDeleted)
  <= 24*V(D)*(log x)^(7*c)/z + 12*x*(log x)^(7*c).
```

At original `roughZ x=x^(1/(loglog x)^3)`, the existing rough-cutoff growth theorem supplies `(log x)^(A+7c)<=z`. Original occupied-key geometry gives `x^(1+sigma/2)<=V(D)` and pays the endpoint. One threshold, before all atoms/keys/receivers and all T, yields

```
norm(badLevelDeleted) <= 36*V(D)/(log x)^A.
```

Receivers z>=roughZ x are allowed; equality is the exact original instance. The outside theorem uses actual `outerL2<=6*Y*betaL2`, the actual beta-square divisor mean and BOTH original owner-bank multiplicities. With local precision `D=A+betaMomentOrder(B)+12`, it proves

```
actualOuterLevelBudget
  <= 432*betaLogConstant^betaMomentOrder(B)*(2*keyLogConstant)^12
       * x^2/(log x)^A.
```

No new arithmetic or analytic assumption is added. Fixed B,sigma,kappa,c,A precede constants and threshold; c0, atom and the signed residue encoded by atom, receiver and keys follow. Original `0<sigma<1/100`, `MediumAdmissible`, c0>0, roughY smooth trim, and occupied key bank remain literal.

## Original signed consumer

`Part3OriginalS3RoughLevelGcdResidual.lean` proves exact identities before any norm inequality:

```
coprimeFarFull = levelCoprimeFarFull + badLevelDeleted

primitiveS3 = largeShiftFull + levelCoprimeFarFull
              + badLevelDeleted + badPairDeleted + closeDeleted
              + restorationCorrection.
```

The retained-source identity includes the unchanged `-genuineOffDiagonalZero -offDiagonalOmitted +diagonalRetained`, then the unchanged `largeShiftFull`, this new correction, J's r/s correction and I's close correction. Full and deleted summands are identified only under BOTH nonzero-shift cutoffs.

The resulting `levelCoprimeFarFull` imposes `(r,s)=1` and `(s,ell)=1`; n1/n2 remains unrestricted. It is not identified with a clean Fourier E2 packet. Close pairs and noncoprime r/s pairs have already been paid by I and J, so this order covers the remaining level-gcd exclusion without double counting in the signed identity.

The final theorem `exists_actualResidualFunctional_level_paid` applies to the EXISTING `actualResidualFunctional`. It bounds that functional by `unpaidOriginalLevelLedger + C*x²/log(x)^A`. The new ledger replaces only J's `coprimeFarFull`. It retains the complete old `largeShiftFull`, full off-diagonal zero subtraction, omitted modes, retained Fourier diagonal, rough replacement, genuine zero diagonal, and all FOUR original S2 norms with their factor 2. The unchanged large-shift complement still contains the original single-zero additions; H's restoration signs are preserved. No double-zero term is restored or silently removed.

## Remaining obligations and source limitations

- The earliest large-coefficient/nonzero-shift cutoff estimate, completion 169–171, and cutoff reinstatement at 181 remain OPEN.
- The n1/n2 gcd exclusion remains in this retained packet; another K task owns that exclusion. No peer result is assumed or imported here.
- Gcd/close zero-mode restoration, completion 212–217, remains OPEN. This delivery pays the original physical doubly deleted correction and its outside norm budget, not a newly cleaned principal mean.
- Physical-to-clean E2 identification, retained phase/Abel/spectral estimates, omitted-mode and Fourier-diagonal payments, rough replacement, genuine zero diagonal, remaining S2 packets, full S123/restricted-medium/PP assembly remain OPEN.
- Source-only imports require installation and elaboration. The exact inherited `Part3MediumLiteralS3DeletedCarrier.lean` still has the displaced second hmod branch at lines 44–56; it was read and not modified. This is a pre-existing concrete source/elaboration blocker, not a new manuscript contradiction.
- Mathlib's pinned revision/toolchain are recorded, but the local `Mathlib/Tactic.lean` source file is absent at the expected package path. No transitive import-closure or kernel verification is claimed.

Static checks were confined to manual source/mathematical inspection, text searches, filesystem existence, byte counts and SHA256 hashing. No new suspected manuscript contradiction was found. Root must be notified before any modification after this delivery is submitted.
