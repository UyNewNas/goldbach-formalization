import ImbalancedChen.Part3OriginalSamePsiS1OwnedAtlas
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Polynomial caps are derived for occupied original dyadic keys and actual
q pieces. No polynomial-size field or log-budget premise is supplied.
-/

namespace ImbalancedChen.Part3.OriginalOwnedS1PolynomialCaps
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalSamePsiS1OwnedAtlas OriginalMediumPhysicalE3Block
open MediumGlobalDyadicOwnership20261028 MediumCanonicalFixedBlock20261028
open OriginalMediumS1ActualCoefficientBinding

theorem occupied_key_scales_le_physical_cap {atom : MediumAtom} {z y : ℝ} {k : Key}
    (hk : k ∈ keyBank atom z y) :
    keyD k ≤ (MediumGlobalDyadicOwnership20261028.physicalCap atom : ℝ) ∧
      keyR k ≤ (MediumGlobalDyadicOwnership20261028.physicalCap atom : ℝ) := by
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
  obtain ⟨hpair, h2, h3, _⟩ := mem_filter.mp hq
  have hp : q.1 * q.2 ≤ MediumGlobalDyadicOwnership20261028.physicalCap atom :=
    Nat.mul_le_mul (mem_Icc.mp (mem_product.mp hpair).1).2
      (mem_Icc.mp (mem_product.mp hpair).2).2
  have hcap : MediumGlobalDyadicOwnership20261028.physicalCap atom ≠ 0 :=
    (lt_of_lt_of_le (mul_pos (Nat.pos_of_ne_zero h2) (Nat.pos_of_ne_zero h3)) hp).ne'
  have hdlog := Nat.le_of_lt_succ (actual_coordinate_bounds hq (4 : Fin 6))
  have hwlog := Nat.le_of_lt_succ (actual_coordinate_bounds hq (5 : Fin 6))
  have hdlog' : (owner z q).d ≤
      Nat.log2 (MediumGlobalDyadicOwnership20261028.physicalCap atom) := by
    simpa [toSix] using hdlog
  have hwlog' : (owner z q).w ≤
      Nat.log2 (MediumGlobalDyadicOwnership20261028.physicalCap atom) := by
    simpa [toSix] using hwlog
  constructor
  · exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hdlog').trans
      (Nat.log2_self_le hcap)
  · exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hwlog').trans
      (Nat.log2_self_le hcap)

theorem physical_cap_le_four_scale_sq {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (hσ : 0 ≤ σ) :
    (MediumGlobalDyadicOwnership20261028.physicalCap atom : ℝ) ≤ 4 * atom.scale ^ 2 := by
  obtain ⟨hx, _, _, hQ2, hQ3⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have h2 : 0 ≤ 2 * atom.Q2 := by linarith [hA.2.2.2.1]
  have h3 : 0 ≤ 2 * atom.Q3 := by linarith [hA.2.2.2.2.1]
  rw [MediumGlobalDyadicOwnership20261028.physicalCap, Nat.cast_mul]
  calc
    _ ≤ (2 * atom.Q2) * (2 * atom.Q3) :=
      mul_le_mul (Nat.floor_le h2) (Nat.floor_le h3) (Nat.cast_nonneg _) h2
    _ ≤ (2 * atom.scale) * (2 * atom.scale) := by gcongr
    _ = _ := by ring

theorem qHi_le_three_scale {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (hσ : 0 ≤ σ) (j : Fin 3) :
    (qHi atom.Q1 j : ℝ) ≤ 3 * atom.scale := by
  obtain ⟨hx, _, hQ1, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hQ0 : 0 ≤ atom.Q1 := zero_le_one.trans hA.2.2.1
  fin_cases j
  · change (Nat.floor atom.Q1 : ℝ) ≤ _
    exact (Nat.floor_le hQ0).trans (by linarith)
  · change (Nat.floor (2 * atom.Q1) : ℝ) ≤ _
    exact (Nat.floor_le (by positivity)).trans (by linarith)
  · change (Nat.floor (5 * atom.Q1 / 2) : ℝ) ≤ _
    exact (Nat.floor_le (by positivity)).trans (by linarith)

theorem atlas_polynomial_caps {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (hσ : 0 ≤ σ) (hk : k ∈ keyBank atom z y)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) :
    let B := atlasBlock atom z y k hA j d hd
    (OriginalMediumS1ActualCoefficientBinding.physicalCap B : ℝ) ≤ 192 * atom.scale ^ 5 ∧
      (qCap B : ℝ) ≤ 3 * atom.scale ∧
      (roughCap B : ℝ) ≤ 8 * atom.scale ^ 2 ∧
      2 * keyD k ≤ 8 * atom.scale ^ 2 := by
  let B := atlasBlock atom z y k hA j d hd
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  have hcap := physical_cap_le_four_scale_sq hA hσ
  obtain ⟨hD, hR⟩ := occupied_key_scales_le_physical_cap hk
  have hD' : keyD k ≤ 4 * atom.scale ^ 2 := hD.trans hcap
  have hR' : keyR k ≤ 4 * atom.scale ^ 2 := hR.trans hcap
  have hd' : (d : ℝ) ≤ 8 * atom.scale ^ 2 := by
    have h := B.d_window_hi
    change (d : ℝ) ≤ 2 * keyD k at h
    linarith
  have hr' : (Nat.floor (2 * keyR k) : ℝ) ≤ 8 * atom.scale ^ 2 :=
    (Nat.floor_le (by dsimp [keyR]; positivity)).trans (by linarith)
  have hq' : (B.qHi : ℝ) ≤ 3 * atom.scale := qHi_le_three_scale hA hσ j
  have hx0 : 0 ≤ atom.scale := zero_le_one.trans hx
  have hx2 : 1 ≤ atom.scale ^ 2 := one_le_pow₀ hx
  refine ⟨?_, ?_, ?_, by linarith⟩
  · change ((qHi atom.Q1 j * d * Nat.floor (2 * keyR k) : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ (3 * atom.scale) * (8 * atom.scale ^ 2) * (8 * atom.scale ^ 2) := by
        gcongr
      _ = _ := by ring
  · change ((max 1 (qHi atom.Q1 j) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) hq'
  · change ((max 1 (Nat.floor (2 * keyR k)) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) hr'

def sourceLog (x : ℝ) : ℝ := (6 + Real.log 256) * (1 + Real.log x)

private theorem log_of_polynomial_cap_le {x t : ℝ}
    (hx : 1 ≤ x) (ht : 1 ≤ t) (hcap : t ≤ 256 * x ^ 5) :
    1 + Real.log t ≤ sourceLog x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlc : 0 ≤ Real.log (256 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one ht) hcap
  rw [Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) (pow_ne_zero _ hx0.ne'),
    Real.log_pow] at hlog
  dsimp [sourceLog]
  nlinarith [mul_nonneg hlc hlx]

/-- The exact fixed-cap logarithms all cost one common multiple of
1+log(x), derived from original admissibility and occupied ownership. -/
theorem atlas_log_caps {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key) (hA : MediumAdmissible b σ κ c0 atom)
    (hσ : 0 ≤ σ) (hk : k ∈ keyBank atom z y)
    (j : Fin 3) (d : ℕ) (hd : d ∈ activeD atom k) :
    let B := atlasBlock atom z y k hA j d hd
    P5Z.RoughSquareWeightedBudget.logBudget
        (OriginalMediumS1ActualCoefficientBinding.physicalCap B) ≤ sourceLog atom.scale ∧
      1 + Real.log (qCap B : ℝ) ≤ sourceLog atom.scale ∧
      1 + Real.log (roughCap B : ℝ) ≤ sourceLog atom.scale ∧
      1 + Real.log (2 * keyD k) ≤ sourceLog atom.scale := by
  let B := atlasBlock atom z y k hA j d hd
  obtain ⟨hx, _, _, _, _⟩ :=
    ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hσ
  obtain ⟨hP, hQ, hR, hD⟩ := atlas_polynomial_caps atom z y k hA hσ hk j d hd
  have hx0 : 0 ≤ atom.scale := zero_le_one.trans hx
  have hx5 : 1 ≤ atom.scale ^ 5 := one_le_pow₀ hx
  have hxle5 : atom.scale ≤ atom.scale ^ 5 := by
    calc
      _ = atom.scale * 1 := by ring
      _ ≤ atom.scale * atom.scale ^ 4 :=
        mul_le_mul_of_nonneg_left (show 1 ≤ atom.scale ^ 4 from one_le_pow₀ hx) hx0
      _ = _ := by ring
  have hx2le5 : atom.scale ^ 2 ≤ atom.scale ^ 5 := by
    calc
      _ = atom.scale ^ 2 * 1 := by ring
      _ ≤ atom.scale ^ 2 * atom.scale ^ 3 :=
        mul_le_mul_of_nonneg_left (show 1 ≤ atom.scale ^ 3 from one_le_pow₀ hx) (sq_nonneg _)
      _ = _ := by ring
  have hD1 : 1 ≤ 2 * keyD k := by
    have h : (1 : ℝ) ≤ ((2 : ℕ) ^ k.d : ℕ) := by
      exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
    change 1 ≤ 2 * (((2 : ℕ) ^ k.d : ℕ) : ℝ)
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply log_of_polynomial_cap_le hx (le_max_left _ _)
    exact max_le (by nlinarith) (hP.trans (by nlinarith))
  · apply log_of_polynomial_cap_le hx
      (by exact_mod_cast (le_max_left 1 B.qHi))
    exact hQ.trans (by nlinarith)
  · apply log_of_polynomial_cap_le hx
      (by exact_mod_cast (le_max_left 1 (Nat.floor (2 * B.roughLength))))
    exact hR.trans (by nlinarith)
  · exact log_of_polynomial_cap_le hx hD1 (hD.trans (by nlinarith))

end
end ImbalancedChen.Part3.OriginalOwnedS1PolynomialCaps
