import ImbalancedChen.HistoricalFifthCutoffInvariance
import ImbalancedChen.P1HistoricalFifthJointIntegralSign
import ImbalancedChen.P1HistoricalFixedCoefficientAssembly

/-!
Eventual orders for the actual historical fourth-to-fifth update.

The only limits used are the existing actual saving/density-difference
limits on `atTop ⊓ principal {N | 0 < N ∧ Even N}`. No limit or final bound
for either complete policy density is supplied as a hypothesis. The same
T3 frontier and inherited fourth old levels remain those of D throughout.
The physical-density corollary reuses the assembly's identical fixed rough
coefficient. Its support and coefficient are not reconstructed here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped Classical BigOperators

namespace HistoricalPrefixCapData

/-- A nonnegative genuine correction integral permits an arbitrarily
small eventual negative error in the literal normalized saving. -/
theorem p1Eventually_actualHistoricalFifthSaving_ge_neg
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      -epsilon ≤ actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N (cap N) (z N) * Real.log (N : ℝ) / singularSeries N := by
  have hI := D.p1FifthCorrectionIntegral_nonneg ha hab hcheck
  have hlim := D.tendsto_actualHistoricalFifthSaving_of_cutoff_ge
    ha hab hold hcheck cap z hcap hz
  exact (hlim.eventually (lt_mem_nhds
    (show -epsilon < D.fifthCorrectionIntegral by linarith))).mono (fun _ h => h.le)

/-- The original cube cutoff is a specialization, with no moving-cutoff
premise beyond the actual residual cap coverage. -/
theorem p1Eventually_actualHistoricalFifthSaving_ge_neg_cube
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      -epsilon ≤ actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N (cap N) ((N : ℝ) ^ (D.b : ℝ)) * Real.log (N : ℝ) / singularSeries N := by
  exact D.p1Eventually_actualHistoricalFifthSaving_ge_neg ha hab hold hcheck cap
    (fun N => (N : ℝ) ^ (D.b : ℝ)) hcap
    (Eventually.of_forall (fun _ => le_rfl)) epsilon hepsilon

theorem p1Eventually_actualHistoricalFifthSaving_ge_neg_ceil
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      -epsilon ≤ actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) ((N : ℝ) ^ (D.b : ℝ)) *
          Real.log (N : ℝ) / singularSeries N := by
  exact D.p1Eventually_actualHistoricalFifthSaving_ge_neg_cube ha hab hold hcheck
    (fun N => Nat.ceil ((N : ℝ) ^ (D.b : ℝ)))
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (D.b : ℝ)))) epsilon hepsilon

/-- This uses the proved limit of the actual policy difference, not a
new mean hypothesis about either whole polynomial. -/
theorem p1Eventually_upperFourthToFifthSaving_ge_neg
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      -epsilon ≤
        (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
            (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
            (roughPrimeUniverse N (cap N) 0 (z N)) -
          firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
            (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
            (roughPrimeUniverse N (cap N) 0 (z N))) *
          Real.log (N : ℝ) / singularSeries N := by
  have hI := D.p1FifthCorrectionIntegral_nonneg ha hab hcheck
  have hlim := D.tendsto_upperFourthToFifthSaving_of_cutoff_ge
    ha hab hold hcheck cap z hcap hz
  exact (hlim.eventually (lt_mem_nhds
    (show -epsilon < D.fifthCorrectionIntegral by linarith))).mono (fun _ h => h.le)

theorem p1Eventually_upperFifth_normalized_le_fourth_add
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 (z N)) * Real.log (N : ℝ) / singularSeries N ≤
        firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 (z N)) *
            Real.log (N : ℝ) / singularSeries N + epsilon := by
  filter_upwards [D.p1Eventually_upperFourthToFifthSaving_ge_neg
    ha hab hold hcheck cap z hcap hz epsilon hepsilon] with N hN
  simp only [div_eq_mul_inv] at hN ⊢
  nlinarith only [hN]

/-- The identical order in the original unnormalized density units. -/
theorem p1Eventually_upperFifth_le_fourth_add_densityScale
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 (z N)) ≤
        firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 (z N)) +
            epsilon * (singularSeries N / Real.log (N : ℝ)) := by
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [D.p1Eventually_upperFourthToFifthSaving_ge_neg
    ha hab hold hcheck cap z hcap hz epsilon hepsilon, hlarge] with N hsave hN
  let u4 := firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N (cap N) 0 (z N))
  let u5 := firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N (cap N) 0 (z N))
  change -epsilon ≤ (u4 - u5) * Real.log (N : ℝ) / singularSeries N at hsave
  change u5 ≤ u4 + epsilon * (singularSeries N / Real.log (N : ℝ))
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hprod := (le_div_iff₀ (singularSeries_pos N)).mp hsave
  apply (mul_le_mul_right hlog).mp
  calc
    u5 * Real.log (N : ℝ) ≤
        u4 * Real.log (N : ℝ) + epsilon * singularSeries N := by nlinarith only [hprod]
    _ = (u4 + epsilon * (singularSeries N / Real.log (N : ℝ))) *
        Real.log (N : ℝ) := by
      field_simp [hlog.ne']
      <;> ring

/-- Same fixed physical coefficient as the assembly, with no replacement rho. -/
theorem p1Eventually_fifthPhysicalDensity_normalized_le_fourth_add
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      physicalDensitySum (D.p1FifthRoughSupport N (cap N) (z N))
          (D.p1FifthRoughCoefficient N (cap N) (z N)) *
            Real.log (N : ℝ) / singularSeries N ≤
        firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 (z N)) *
            Real.log (N : ℝ) / singularSeries N + epsilon := by
  filter_upwards [D.p1Eventually_upperFifth_normalized_le_fourth_add
    ha hab hold hcheck cap z hcap hz epsilon hepsilon] with N hN
  rw [D.p1FifthRoughDensity_eq_polynomial]
  exact hN

/-- Strict positivity is a condition on the independently defined genuine
joint-cell integral. It is not supplied here as a final mean theorem. -/
theorem p1Eventually_actualHistoricalFifthSaving_normalized_pos
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (hI : 0 < D.fifthCorrectionIntegral) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N (cap N) (z N) * Real.log (N : ℝ) / singularSeries N := by
  exact (D.tendsto_actualHistoricalFifthSaving_of_cutoff_ge
    ha hab hold hcheck cap z hcap hz).eventually (lt_mem_nhds hI)

theorem p1Eventually_actualHistoricalFifthSaving_pos
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (hI : 0 < D.fifthCorrectionIntegral) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N (cap N) (z N) := by
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [D.p1Eventually_actualHistoricalFifthSaving_normalized_pos
    ha hab hold hcheck cap z hcap hz hI, hlarge] with N hsave hN
  have hscale : 0 < Real.log (N : ℝ) / singularSeries N :=
    div_pos (Real.log_pos (by exact_mod_cast hN)) (singularSeries_pos N)
  rw [mul_div_assoc] at hsave
  exact pos_of_mul_pos_right hsave hscale.le

theorem p1Eventually_upperFifth_polynomial_lt_fourth
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (hI : 0 < D.fifthCorrectionIntegral) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N (cap N) 0 (z N)) <
      firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N (cap N) 0 (z N)) := by
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  have hpos := (D.tendsto_upperFourthToFifthSaving_of_cutoff_ge
    ha hab hold hcheck cap z hcap hz).eventually (lt_mem_nhds hI)
  filter_upwards [hpos, hlarge] with N hsave hN
  have hscale : 0 < Real.log (N : ℝ) / singularSeries N :=
    div_pos (Real.log_pos (by exact_mod_cast hN)) (singularSeries_pos N)
  rw [mul_div_assoc] at hsave
  exact sub_pos.mp (pos_of_mul_pos_right hsave hscale.le)

theorem p1Eventually_fifthPhysicalDensity_lt_fourth
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) (hI : 0 < D.fifthCorrectionIntegral) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      physicalDensitySum (D.p1FifthRoughSupport N (cap N) (z N))
        (D.p1FifthRoughCoefficient N (cap N) (z N)) <
      firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N (cap N) 0 (z N)) := by
  filter_upwards [D.p1Eventually_upperFifth_polynomial_lt_fourth
    ha hab hold hcheck cap z hcap hz hI] with N hN
  rw [D.p1FifthRoughDensity_eq_polynomial]
  exact hN

end HistoricalPrefixCapData

end

end ImbalancedChen
