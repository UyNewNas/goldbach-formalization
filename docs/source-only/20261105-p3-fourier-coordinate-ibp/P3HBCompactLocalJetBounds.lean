import ImbalancedChen.P3HBLocalTwoAxisL1
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
P3.6 manuscript-internal analytic step, pinned
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F), six original ordered HB logarithmic coordinates.
SOURCE_ONLY: not elaborated, not compiled, not checked by the Lean kernel.
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The true original six-slot closed logarithmic HB support rectangle is compact.
For ONE FIXED genuine geometry W with continuous actual canonical order-two
coordinate jets, its four local norms attain finite maxima on that rectangle.
This pays the previous LOCAL M0/M1/M2 premises and gives an existential,
nonuniform, 729-child coupled L1 bound for that W and both i=j and i≠j.

Crucial limitation: compactness gives NO bound uniform in original T, HB
length m(N), U5 or trim. It does not supply the actual physical W_T jets,
full repeated 2S, Fourier tails, same-rho arithmetic or any PP input.
-/

namespace ImbalancedChen.P3HBCompactLocalJetBounds
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBCoupledTwoAxisL1
open ImbalancedChen.P3HBActualTwoAxisLocalization
open ImbalancedChen.P3HBLocalTwoAxisL1

/-- Exact original six-coordinate HB rectangle is compact. -/
theorem originalHBLogBox_isCompact : IsCompact originalHBLogBox := by
  change IsCompact
    {u : Fin 6 → ℝ | ∀ k : Fin 6,
      u k ∈ Set.Icc (-Real.log 2) (Real.log 2)}
  exact isCompact_pi_infinite
    (s := fun _ : Fin 6 => Set.Icc (-Real.log 2) (Real.log 2))
    (fun _ => isCompact_Icc)

/-- The original HB rectangle is nonempty; all six slots can equal zero. -/
theorem originalHBLogBox_nonempty : originalHBLogBox.Nonempty := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨fun _ => 0, ?_⟩
  change ∀ k : Fin 6,
    (0 : ℝ) ∈ Set.Icc (-Real.log 2) (Real.log 2)
  intro k
  exact ⟨by linarith, hlog⟩

/-- A continuous *actual* complex jet has a finite nonnegative norm
ceiling on the literal original compact log rectangle. Nothing here
asserts uniformity over a parameterized family of geometries. -/
theorem continuousJet_exists_local_bound
    (F : (Fin 6 → ℝ) → ℂ) (hF : Continuous F) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ originalHBLogBox, ‖F u‖ ≤ M := by
  obtain ⟨v, hv, hmax⟩ :=
    originalHBLogBox_isCompact.exists_isMaxOn
      originalHBLogBox_nonempty hF.norm.continuousOn
  refine ⟨‖F v‖, norm_nonneg _, ?_⟩
  intro u hu
  exact hmax hu

/-- For a fixed SAME W, all four ordered two-axis local jet ceilings
exist simultaneously. The common M1 is the maximum of the two genuine
first coordinate jet bounds; it is not an independent derivative field. -/
theorem actualTwoAxis_exists_local_jet_bounds
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6)
    (hWc : Continuous W)
    (hic : Continuous (actualAxisDeriv W i))
    (hjc : Continuous (actualAxisDeriv W j))
    (h2c : Continuous (actualAxisDeriv (actualAxisDeriv W i) j)) :
    ∃ M0 M1 M2 : ℝ,
      0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧
      (∀ u ∈ originalHBLogBox, ‖W u‖ ≤ M0) ∧
      (∀ u ∈ originalHBLogBox, ‖actualAxisDeriv W i u‖ ≤ M1) ∧
      (∀ u ∈ originalHBLogBox, ‖actualAxisDeriv W j u‖ ≤ M1) ∧
      (∀ u ∈ originalHBLogBox,
        ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) := by
  obtain ⟨M0, hM0, h0⟩ := continuousJet_exists_local_bound W hWc
  obtain ⟨Mi, hMi, hi⟩ :=
    continuousJet_exists_local_bound (actualAxisDeriv W i) hic
  obtain ⟨Mj, hMj, hj⟩ :=
    continuousJet_exists_local_bound (actualAxisDeriv W j) hjc
  obtain ⟨M2, hM2, h2⟩ :=
    continuousJet_exists_local_bound
      (actualAxisDeriv (actualAxisDeriv W i) j) h2c
  refine ⟨M0, max Mi Mj, M2, hM0,
    le_trans hMi (le_max_left Mi Mj), hM2,
    h0, ?_, ?_, h2⟩
  · intro u hu
    exact (hi u hu).trans (le_max_left Mi Mj)
  · intro u hu
    exact (hj u hu).trans (le_max_right Mi Mj)

/-- Fixed-geometric-weight genuinely integrated two-axis original HB
mass needs NO separately assumed local jet ceilings: continuity on the
compact original box supplies them. The existential M's may depend on
W, i and j and must NOT be fed into a T/m(N)-uniform Fourier/PP claim. -/
theorem actualTwoAxisMass_exists_integrable_L1_bound
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (hk : ∀ k, orders k + 2 ≤ K)
    (W : (Fin 6 → ℝ) → ℂ) (i j : Fin 6)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (hDi : ∀ u : Fin 6 → ℝ, DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (hWc : Continuous W)
    (hic : Continuous (actualAxisDeriv W i))
    (hjc : Continuous (actualAxisDeriv W j))
    (h2c : Continuous (actualAxisDeriv (actualAxisDeriv W i) j)) :
    ∃ M0 M1 M2 : ℝ,
      0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧
      Integrable (actualTwoAxisMass chi orders W i j) ∧
      (∫ u : Fin 6 → ℝ, actualTwoAxisMass chi orders W i j u) ≤
        (M2 + 2*M1 + M0) *
        ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6) := by
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, h0, hi, hj, h2⟩ :=
    actualTwoAxis_exists_local_jet_bounds W i j hWc hic hjc h2c
  obtain ⟨hint, hbound⟩ :=
    actualTwoAxisMass_integrable_and_L1_of_local_jets
      chi hchi hsmall hlarge K C hC orders hk W i j
      hW hDi hWc hic hjc h2c
      M0 M1 M2 hM0 hM1 hM2 h0 hi hj h2
  exact ⟨M0, M1, M2, hM0, hM1, hM2, hint, hbound⟩

end
end ImbalancedChen.P3HBCompactLocalJetBounds
