# Part 4: one physical upper weight, density and real bad count

## Status and fixed sources

This checkpoint contains candidate proofs of finite same-weight bridges,
exact normalization, and explicitly conditional assembly theorems. **The
new Lean sources have not yet passed compilation and kernel replay. This
checkpoint does not prove the manuscript's sharp K bound or the final
hUpper.** A successful compilation
of an assembly theorem does not discharge its displayed analytic inputs.

- Accepted base: `1a80c1bcce67886f699d097fc37fd245cd3620bf`.
- Accepted base tree: `1fd54b8b4d5fd89abc767ee7e8d814453453b29c`.
- Working branch: `chatgpt/chen-p4-upper`.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes` at
  `ba6ec11d800eccc54406490631895e174de85766`.
- Body: `paper/source/manuscript-body.tex`, Git blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- `currentK = 8452171 / 1250000 = 6.7617368`.
- Lean: `leanprover/lean4:v4.33.0-rc1`; all eleven dependency revisions and
  the bytes of the three toolchain/dependency files remain frozen.

The verification artifact records its own complete checked-out commit SHA,
source hashes, final object hashes, declaration inventory and actual gate
results. Use that SHA and its run result when forwarding this checkpoint.
No change to `ImbalancedChen.lean`, existing modules, existing workflows or
Lake configuration is required by these additions.

## Owned files and real outputs

| Module | Output | What it does not supply |
|---|---|---|
| `ActualUpperPolicyDensity` | Identifies an even-retaining Boolean policy with its actual odd-first-exit coefficient, support and physical attachment; proves the selected and historical policies preserve this parity. | A complete adopted policy, its certified integral, or a boxed-compiler identity. |
| `UpperCoefficientPerturbation` | Transports coefficientwise rough domination to the actual sign-attached majorant and bounds physical density changes by a weighted absolute coefficient difference. | A numerical compiler-error bound or legal factorization support. |
| `ActualUpperDensityAssembly` | Exact manuscript-scale identities; correct precision-before-target limit-to-density assembly; a separate compiler budget transport. | Instantiation of the full-policy integral and certificate premises. |
| `RealPhysicalUpperWeightBridge` | Exact real-b source Fubini and three-term decomposition; finite RealB bound with both losses; positive outer-source comparison; raw actual-rho strict-ceiling and support adapters. | An analytic signed distribution theorem or legal smooth outer approximation. |
| `RealUpperCountingAssembly` | The exact epsilon/eventual real hUpper conclusion from precision-indexed same-weight inputs, using the already proved source mass and endpoint absorption. | Proofs of its displayed density, coprime-error and signed-distribution inputs for the final compiled weight. |

## Weight identity and normalization

For a raw odd retention predicate, the actual coefficient is the existing
`actualSmallRoughRho retainOdd N cap w z L`. It is the literal

```lean
smallRoughRho
  (actualSmallRosserSupport N cap w)
  (fixedRoughSupport retainOdd N cap w z)
  (fixedRoughCoefficient retainOdd N cap w z)
  (actualSmallRosserMinus N cap w L)
  (actualSmallRosserPlus N cap w L)
```

The sign of the rough coefficient selects beta-plus or beta-minus before
the small/rough pair is uniquely reindexed by its product. For every use,
the density is exactly

```lean
physicalDensitySum Q rho = ∑ q ∈ Q, rho q / (Nat.totient q : ℝ)
```

The manuscript coefficient is measured by
`physicalDensitySum Q rho * Real.log N / singularSeries N`.
For `N >= 2`, bounding this by `k` is equivalent to bounding the unnormalized
density by `k * (singularSeries N / Real.log N)`. The source scale multiplies
it exactly:

```lean
((N : ℝ) / Real.log (N : ℝ)) *
  (singularSeries N / Real.log (N : ℝ)) = singularNormalization N
```

The existing `ActualNormalizedRhoError` already proves the conversion from
`D = N^nu`, including the factor `nu`; it has not been reproved or replaced.
For the manuscript's upper cutoff the parameters must satisfy
`nu * sieveR = 19/96`. Neither internal exponent is the imbalance `b`.
There is no Chen quarter, extra factor two or ordering factorial in this
upper density. The ordered source mass is exactly `log (1/b)`.

The real strict prime cutoff `p < z` is precisely the natural strict
cutoff at `Nat.ceil z`, including an integral value of z. The new indicator
identity also covers all integer test arguments, zero and negative ones.
The raw actual coefficient's prime-product support divides this same sieve
product; that divisibility does not imply the manuscript's modulus exponent.

## Raw policy and compiled coefficient are separate obligations

The manuscript boxes an ideal policy into a rough coefficient `a_N(d)`
that dominates the raw coefficient. A boxed support need not be prefix
closed. Therefore `a_N` is not silently identified with
`fixedRoughCoefficient` for another policy.

If Part 1 proves such a literal equality, `ActualUpperPolicyDensity` provides
the exact attachment identification. Otherwise the final coefficient must
be the generic `smallRoughRho small rough a_N betaMinus betaPlus`, on a
common rough carrier. `UpperCoefficientPerturbation` proves both the
domination and density-perturbation transports for that generic coefficient.

One sufficient compiler budget is

```lean
M * reciprocalTotientDensity rough (fun d => |a_N d - raw_N d|)
  <= compilerReserve * (singularSeries N / Real.log (N : ℝ))
```

where both actual small densities have absolute value at most M. This is a
sufficient absolute-error interface, not a claim that the manuscript's
adopted boxes satisfy it. A direct proved one-sided density transport for
the same compiled coefficient can serve the same role.

## Minimal unresolved handoffs

### Part 1 to Part 4: complete actual construction

Supply the full adopted causal policy and its actual compiled coefficient,
with support and coefficient identities. This includes all adopted stages,
inherited decisions, tails, owned endpoints and the one-time accounting of
each saving. The fixed-family fifth-prefix limit is already available but
does not cover the complete adopted historical construction.

For the raw-attachment path, the new
`exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits`
expects the actual full reciprocal-totient density, multiplied by
`log N / C_N`, to tend to an explicitly defined integral. If the policy
depends on attachment precision, this must hold for every sufficiently
small positive precision. The attachment theorem then chooses a precision
in that interval before taking a common target threshold. A theorem at an
unrelated single precision is insufficient.

The more general
`exists_actualSmallRoughRho_density_le_of_full_policy_limits` retains an
explicit `densityCap`. For example, after the true integral is bounded by
E, a cap of E+u allocates u to the limit/attachment step and leaves the
second u for compilation. The two internal approximation errors each use
one third of `densityCap - rawBound`. Returning only a raw bound at K
would discard the reserve needed by a later compiler step.

For the compiled path, also supply coefficient domination, an actual
compiler-error budget, cutoff-separated support, squarefreeness,
target-coprimality, bounded coefficients and the physical/support
factorization gates needed by Part 3. Raw support divisibility alone does
not supply `theta_* = 599/1000` or the auxiliary local factorization cover.

### Part 2 to Part 4: the adopted upper certificate

Supply the Lean inequality for the real integral of that exact full
construction and the adopted data, with fixed source/data hashes. The
manuscript endpoint is

```text
E = 9979702576710911234850619807816847864907359959
    / 1475913550962201227946780619099353215139840000
u = 145007961227048312210593427530128000784681
    / 11807308407697609823574244952794825721118720000
K - E - 2u = 71229286727542131248758574547050908572431
    / 737956775481100613973390309549676607569920000000 > 0
```

The two u budgets pay different finite operations: density approximation
and compilation. The already proved small-prime attachment reserve must
be allocated within this chain, not treated as proof of the entire
compiler budget. The rational identity above is not the integral theorem.
The 17,572-cell lower certificate is not an upper-K supplier.

A read-only check of Part 2 at
`195f19cfcedeaf7793ccce3f1d42d27fcfe4f815` confirms that its new first-row
paired-fibre integral certificate is a lower-side result. Its
[`docs/part2/PART1_INTERFACE.md`](https://github.com/UyNewNas/goldbach-formalization/blob/195f19cfcedeaf7793ccce3f1d42d27fcfe4f815/docs/part2/PART1_INTERFACE.md)
explicitly excludes certification of the whole upper K. It does not supply
the missing upper integral premise here. Its independent workflow
`38193423556` failed before any job steps ran and has no successful
compilation artifact. That snapshot has not been imported or used as an
accepted replacement baseline.

### Part 3 to Part 4: the same final physical weight

Supply the signed physical modulus sum for the exact real ordered source,
or a proved transfer from a licensed smooth outer source. The sharp-source
spelling is `realPhysicalDistributionError b N T (Q N) (rho N)`, with
`T = manuscriptHalfProductCutoff kappa N`. Its center retains the actual
coprime source mass divided by the actual totient.

The outer-source bridge compares nonnegative complete divisor sums before
using the signed expression
`sum d in Q, rho d * finitePrimitiveDiscrepancy S weight N d`.
It does not replace this by the sum of moduluswise absolute discrepancies.
That bridge explicitly assumes `m <= N` on its outer carrier. A licensed
outer approximation crossing `m > N` still needs the integer-shift Fubini
adapter; natural subtraction cannot be used there.

The real half-product coprime correction is exactly zero if the displayed
roughness and active-support gate holds. Otherwise its normalized error
remains a visible input. A general labelled product family still needs its
own coprime-mask estimate; it is not covered by this zero-correction claim.

### Part 4 to Part 5 and Part 0

**No unconditional current-K conclusion is handed to Part 5 in this
checkpoint.** Part 5 must not instantiate its upper-product cost from the
conditional limit or counting assemblers. After Parts 1 and 2 supply the
construction, full integral certificate and compilation budget, Part 4 can
apply these interfaces to the same final coefficient and forward the
result immediately, without waiting for the final bad-semiprime count.

Part 0 can integrate these independent modules when their actual proof
gates pass. The five-module verification target is intentionally independent
of the root import list, to avoid conflicting ownership of that list.

## Verification scope

The local official Lean archive and all fixed dependencies were obtained
and checked, but Lean's `/proc/<pid>/exe` lookup is denied by this execution
environment. No runtime permission bypass or patched Lean is used.

The standalone `part4-upper.yml` workflow checks the exact source commit,
fixed pins, explicit module builds, strict individual source elaboration,
fresh bundled-kernel replay of all five modules, and every defining-module
declaration's safety and transitive axioms. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Full elaborated types,
including private/generated declarations, are retained with the run logs.
A failed, skipped, incomplete or only statically scanned run is not a
verified proof. Existing full-project checks remain independently visible.

### Observed attempts

- The complete local runner reached `lean-version.log` and failed with
  `error: failed to locate application`; its report status is `FAILED`.
- First candidate commit:
  `4befa13602117435a3a64dfca001c20bbbb7d4c2`.
  [Part 4 run 38193908304](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38193908304)
  failed with no jobs. The job-level cache path used a `runner` context
  where GitHub does not permit that context; the present workflow moves
  that assignment into the existing shell step through `GITHUB_ENV`.
- At the same first candidate commit, existing core run `38193909112` and
  variable-envelope run `38193909046` each failed with `steps = []` and
  `runner_id = 0`. No Lean log exists for those attempts. This is not
  evidence of either proof success or an elaboration error.
- Static checks passed: three frozen configuration hashes, all eleven
  dependency HEADs and source cleanliness, Python syntax, YAML parsing,
  five shell-block syntax checks and whitespace checks. All 303 baseline
  source blobs remain byte-for-byte identical.

Use the final handoff's fixed SHA and its own actual workflow result for
the latest attempt. The candidate source types below are copied from the
source; they are not an elaborated type inventory.

## Candidate key declaration types

All declarations are in namespace `ImbalancedChen`; `Filter` and
`Topology` are open. These are complete source signatures with every
hypothesis retained. They remain uncompiled candidates at this checkpoint.

### Exact density normalization

```lean
theorem density_le_manuscriptScale_iff_normalized {N : ℕ}
    (hN : 2 ≤ N) (density coefficient : ℝ) :
    density ≤ coefficient * (singularSeries N / Real.log (N : ℝ)) ↔
      density * Real.log (N : ℝ) / singularSeries N ≤ coefficient
```

### Exact main-term product

```lean
theorem same_rho_normalized_mainTerm (N : ℕ) (mass : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (mass * physicalDensitySum Q rho) / singularNormalization N =
      (mass * Real.log (N : ℝ) / (N : ℝ)) *
        (physicalDensitySum Q rho * Real.log (N : ℝ) / singularSeries N)
```

### A raw density cap that preserves the compiler reserve

```lean
theorem exists_actualSmallRoughRho_density_le_of_full_policy_limits
    (nu sieveR epsilonMax rawBound densityCap : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < densityCap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          densityCap * (singularSeries N / Real.log (N : ℝ))
```

### The currentK specialization for the raw attachment

```lean
theorem exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits
    (nu sieveR epsilonMax rawBound : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < currentK) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          currentK * (singularSeries N / Real.log (N : ℝ))
```

### Transport to the compiled physical coefficient

```lean
theorem compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget
    {N : ℕ} (hN : 2 ≤ N) {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) (M rawBound compilerReserve : ℝ)
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M)
    (hraw : physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) ≤
      rawBound * (singularSeries N / Real.log (N : ℝ)))
    (hcompiler : M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
      compilerReserve * (singularSeries N / Real.log (N : ℝ)))
    (hbudget : rawBound + compilerReserve ≤ currentK) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) *
        Real.log (N : ℝ) / singularSeries N ≤ currentK
```

### Actual raw weight majorant

```lean
theorem actualSmallRoughRho_sieveProduct_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n
```

### Actual raw weight in the finite real count

```lean
theorem RealB_cast_le_actualSmallRoughRho_main_add_errors
    {b T : ℝ} (N cap : ℕ) (retainOdd : List ℕ → Bool) (w z L : ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) *
        physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalCoprimeCorrection b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalDistributionError b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) + (Nat.ceil z : ℝ) + (T + 1)
```

### Conditional hUpper with the same precision-indexed weight

```lean
theorem eventually_RealB_le_currentK_log_of_same_rho_inputs
    {b kappa sieveExponent : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hsieve : sieveExponent < 1)
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ sieveExponent)))
        then (1 : ℝ) else 0) ≤ physicalDivisorSum (Q delta N) (rho delta N) n)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (Q delta N) (rho delta N) ≤
        (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hdistribution : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + epsilon) * singularNormalization N
```
