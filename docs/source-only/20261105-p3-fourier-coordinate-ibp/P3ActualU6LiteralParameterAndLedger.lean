import ImbalancedChen.P3ActualU6ReserveEpsilonSelected
import Mathlib.Tactic

/-!
P3.6 MANUSCRIPT-INTERNAL, pinned paper
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/manuscript-body.tex eq:current-PP and the distribution
prime-product completion module §§1,3,4.

The last packet selected epsilon for arbitrary nu,r but STILL required
an external matching parameter equality nu*r=417/5000. Here the genuine
reserve theorem's own positive nu,r quantifiers are instantiated with
nu=1 and r=417/5000. This makes the original U6 z=cutoff(N)
literal, not a hypothesis about a future compiler.

The SAME selected epsilon and N0 are now used simultaneously for:
* the genuine even first-exit density with cap=ceil(cutoff(N)), b=t1*t2
  and the ORIGINAL label-dependent policy, for each sixthSupport label;
* the true original U6 row minorant and exact signed primitive ledger;
* the all-labelled INTEGER LOWER rho quotient-prime correction bound.
The identity displays the signed nonzero-shift term, but does NOT bound it.
No statement about a final global rho_N, another PP/HB source, an
enhanced compiler policy, or any Fourier estimate is inferred.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6LiteralParameterAndLedger

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5CausalRhoQuotientBridge
open ImbalancedChen.P3ActualU6EnhancedPowerLevel
open ImbalancedChen.P3ActualU6ReserveEpsilonSelected
open ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
open ImbalancedChen.P3ActualRawActiveLevelTotientCap

/-- No auxiliary equation nu*r=417/5000 remains: choose actual
production reserve parameters nu=1, r=417/5000. The original
real z=cutoff(N), its ceil cap, the original even-exit retain policy,
all t-labels, and the literal physical phi((t1*t2)*q) survive.

The first estimate is an exact row minorant, the second is an EXACT
algebraic signed AP ledger (not an error bound), the third pays only
the quotient-prime correction, and the fourth is the literal
M/phi(b) lower reserve at every true U6 label.

C is chosen before eta, epsilon, N, all policies and row labels.
The threshold N0 is chosen together with epsilon and before N/policy.
Nothing proves this policy to be the FINAL causal PP compiler policy. -/
theorem exists_literal_U6_reserve_ledger_and_correction :
    ∃ C : ℝ, 0 < C ∧
      ∀ eta : ℝ, 0 < eta →
        ∃ epsilon : ℝ,
          0 < epsilon ∧ epsilon < 1 / 8 ∧
          epsilon ^ 2 ≤ (417 / 5000 : ℝ) ∧ epsilon ≤ 1 ∧
          ∃ N₀ : ℕ, 2 ≤ N₀ ∧
            ∀ N : ℕ, N₀ ≤ N → Even N →
              ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
                (∀ t ∈ sixthSupport N,
                  rowEstimator N policy
                    (fun _ => enhancedSmallW N 1 epsilon)
                    (fun _ => enhancedRosserL N 1 epsilon) t ≤
                    sixthWeight N t) ∧
                ((∑ t ∈ sixthSupport N,
                  labelledRowAP N policy
                    (fun _ => enhancedSmallW N 1 epsilon)
                    (fun _ => enhancedRosserL N 1 epsilon) t) =
                  (∑ t ∈ sixthSupport N,
                    rowPrimitiveMean N policy
                      (fun _ => enhancedSmallW N 1 epsilon)
                      (fun _ => enhancedRosserL N 1 epsilon) t) +
                  (∑ t ∈ sixthSupport N,
                    rowPrimitiveDiscrepancy N policy
                      (fun _ => enhancedSmallW N 1 epsilon)
                      (fun _ => enhancedRosserL N 1 epsilon) t) -
                  (∑ t ∈ sixthSupport N,
                    rowQuotientPrimeCorrection N policy
                      (fun _ => enhancedSmallW N 1 epsilon)
                      (fun _ => enhancedRosserL N 1 epsilon) t)) ∧
                (|∑ t ∈ sixthSupport N,
                  rowQuotientPrimeCorrection N policy
                    (fun _ => enhancedSmallW N 1 epsilon)
                    (fun _ => enhancedRosserL N 1 epsilon) t| ≤
                  (logTotientCap N) ^ 3 *
                    (C * (1 + Real.log (N : ℝ))) *
                    ((Nat.log 2 N : ℝ) +
                      C * (1 + Real.log (N : ℝ)))) ∧
                (∀ t ∈ sixthSupport N, ∀ M : ℝ, 0 ≤ M →
                  M / (Nat.totient (t.1 * t.2) : ℝ) *
                    (reciprocalTotientDensity
                      (fixedEvenRoughSupport (policy t) N
                        (Nat.ceil (cutoff N)) 0 (cutoff N))
                      (fixedEvenRoughCoefficient (policy t) N
                        (Nat.ceil (cutoff N)) 0 (cutoff N)) -
                      eta * singularSeries N / Real.log (N : ℝ)) ≤
                  M / (Nat.totient (t.1 * t.2) : ℝ) *
                    physicalDensitySum
                      (actualLowerSmallRoughModuli (policy t) N
                        (Nat.ceil (cutoff N))
                        (enhancedSmallW N 1 epsilon) (cutoff N))
                      (actualLowerSmallRoughRho (policy t) N
                        (Nat.ceil (cutoff N))
                        (enhancedSmallW N 1 epsilon) (cutoff N)
                        (enhancedRosserL N 1 epsilon))) := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_one_constant_original_lower_reserve_and_U6_correction
  refine ⟨C, hC, ?_⟩
  intro eta heta
  have hnu : (0 : ℝ) < 1 := by norm_num
  have hr : (0 : ℝ) < 417 / 5000 := by norm_num
  have hnur : (1 : ℝ) * (417 / 5000 : ℝ) = 417 / 5000 := by ring
  obtain ⟨epsilon, heps, heps8, hepsr, hgate, N₀, hN₀,
      hreserve, hcorrection⟩ :=
    hselected 1 (417 / 5000) eta hnu hr heta hnur
  refine ⟨epsilon, heps, heps8, hepsr, ?_, N₀, hN₀, ?_⟩
  · simpa only [one_mul] using hgate
  intro N hN hEven policy
  have hN2 : 2 ≤ N := le_trans hN₀ hN
  have hgates :=
    enhanced_power_gates 1 (417 / 5000) epsilon
      hnu heps heps8 hepsr hnur N hN2
  have hwz : ∀ t ∈ sixthSupport N,
      enhancedSmallW N 1 epsilon ≤ cutoff N := by
    intro t ht
    exact hgates.2.2
  have hminor :=
    enhanced_power_all_original_U6_rows_minorize
      1 (417 / 5000) epsilon
      hnu heps heps8 hepsr hnur N hN2 policy
  have hledger :=
    all_original_U6_lower_labelled_recenter N policy
      (fun _ => enhancedSmallW N 1 epsilon)
      (fun _ => enhancedRosserL N 1 epsilon) hwz
  have hbound := hcorrection N hN hEven policy
  refine ⟨hminor, hledger, hbound, ?_⟩
  intro t ht M hM
  have hcap : cutoff N ≤ (Nat.ceil (cutoff N) : ℝ) := Nat.le_ceil _
  have hrow :=
    hreserve N hN hEven (Nat.ceil (cutoff N))
      (by simpa only [one_mul] using hcap)
      (policy t) (t.1 * t.2) M hM
  simpa only [P5CausalRhoQuotientBridge.cutoff, one_mul,
    enhancedSmallW, enhancedRosserL] using hrow

end
end ImbalancedChen.P3ActualU6LiteralParameterAndLedger
