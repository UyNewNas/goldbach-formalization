import ImbalancedChen.P5ZU1011AutomaticBuchstabIntervals
import ImbalancedChen.P5ZU1011OriginalSixteenSwitchedBoxBounds

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual switched rational box coefficients using the GENERATED Buchstab
interval supplier. No switched-cell bound or omega node data is supplied.
The true original-domain argument licenses clipping to [2,8]. Every
numerator and denominator is directed before division.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenTightSwitchedBoxes

noncomputable section

open Set U11Integral U11Canonical LiLiuPrereqBuchstab
open U1011OriginalSixteenPolicyBank.BoxCertificates
open OriginalSixteenSwitchedBoxBounds
open AutomaticBuchstabIntervals

def numeratorLower (B : Box) : ℚ := max 0 (1 - (B.hi 0 + B.hi 1 + B.hi 2 + B.hi 3))
def numeratorUpper (B : Box) : ℚ := max 0 (1 - (B.lo 0 + B.lo 1 + B.lo 2 + B.lo 3))
def queryLower (B : Box) : ℚ := max 2 (min 8 (numeratorLower B / zUpper B))
def queryUpper (B : Box) : ℚ := max (queryLower B) (min 8 (numeratorUpper B / zLower B))

theorem query_valid (B : Box) :
    2 ≤ queryLower B ∧ queryLower B ≤ queryUpper B ∧ queryUpper B ≤ 8 := by
  have hLo : queryLower B ≤ 8 := by
    exact max_le (by norm_num) (min_le_left _ _)
  exact ⟨le_max_left _ _, le_max_left _ _, max_le hLo (min_le_left _ _)⟩

theorem coordinate_bounds (mask : Set (ℝ × ℝ)) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    0 < (zLower B : ℝ) ∧ (zLower B : ℝ) ≤ v 2 ∧ v 2 ≤ (zUpper B : ℝ) := by
  have hA : (a : ℝ) ≤ v 2 := (originalDomain_subset_compactBox mask hD).1 2
  have hLo : (zLower B : ℝ) ≤ v 2 := by
    simp only [zLower, Rat.cast_max]
    exact max_le hA (hv.1 2)
  have hHi : v 2 ≤ (zUpper B : ℝ) := by
    exact (hv.2 2).trans (by simp only [zUpper, Rat.cast_max]; exact le_max_right _ _)
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hLower : (a : ℝ) ≤ (zLower B : ℝ) := by
    simp only [zLower, Rat.cast_max]
    exact le_max_left _ _
  exact ⟨ha.trans_le hLower, hLo, hHi⟩

/-- The computed rational query covers the ACTUAL switched argument. -/
theorem argument_bounds (mask : Set (ℝ × ℝ)) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 ∈
      Icc (queryLower B : ℝ) (queryUpper B : ℝ) := by
  let s : ℝ := (1 - (v 0 + v 1 + v 2 + v 3)) / v 2
  let r : ℝ := 1 - (v 0 + v 1 + v 2 + v 3)
  have hz := coordinate_bounds mask B hv hD
  have hz0 : 0 < v 2 := hz.1.trans_le hz.2.1
  have hzU0 : 0 < (zUpper B : ℝ) := hz0.trans_le hz.2.2
  have hsD := originalDomain_argument_mem mask v hD
  have hs2 : 2 ≤ s := by dsimp [s]; linarith only [hsD.1]
  have hs8 : s ≤ 8 := hsD.2
  have hr0 : 0 ≤ r := by
    have hh : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 2).trans hs2
    have hh' := (le_div_iff₀ hz0).mp (show (0 : ℝ) ≤ r / v 2 from hh)
    simpa only [zero_mul] using hh'
  have hnLo : (numeratorLower B : ℝ) ≤ r := by
    simp only [numeratorLower, Rat.cast_max, Rat.cast_zero, Rat.cast_sub,
      Rat.cast_one, Rat.cast_add]
    refine max_le hr0 ?_
    dsimp [r]
    linarith only [hv.2 0, hv.2 1, hv.2 2, hv.2 3]
  have hnHi : r ≤ (numeratorUpper B : ℝ) := by
    have hh : r ≤ 1 - ((B.lo 0 : ℝ) + B.lo 1 + B.lo 2 + B.lo 3) := by
      dsimp [r]
      linarith only [hv.1 0, hv.1 1, hv.1 2, hv.1 3]
    simp only [numeratorUpper, Rat.cast_max, Rat.cast_zero, Rat.cast_sub,
      Rat.cast_one, Rat.cast_add]
    exact hh.trans (le_max_right _ _)
  have hnLo0 : (0 : ℝ) ≤ (numeratorLower B : ℝ) := by
    simp only [numeratorLower, Rat.cast_max, Rat.cast_zero]
    exact le_max_left _ _
  have hnHi0 : (0 : ℝ) ≤ (numeratorUpper B : ℝ) := hr0.trans hnHi
  have hRawLo : (numeratorLower B : ℝ) / (zUpper B : ℝ) ≤ s :=
    (div_le_div_of_nonneg_left hnLo0 hz0 hz.2.2).trans
      (div_le_div_of_nonneg_right hnLo hz0.le)
  have hRawHi : s ≤ (numeratorUpper B : ℝ) / (zLower B : ℝ) :=
    (div_le_div_of_nonneg_right hnHi hz0.le).trans
      (div_le_div_of_nonneg_left hnHi0 hz.1 hz.2.1)
  constructor
  · simp only [queryLower, Rat.cast_max, Rat.cast_min, Rat.cast_ofNat, Rat.cast_div]
    exact max_le hs2 ((min_le_right _ _).trans hRawLo)
  · have hh' : s ≤ min 8 ((numeratorUpper B : ℝ) / (zLower B : ℝ)) := le_min hs8 hRawHi
    simp only [queryUpper, Rat.cast_max, Rat.cast_min, Rat.cast_ofNat, Rat.cast_div]
    exact hh'.trans (le_max_right _ _)

def omegaLower (m : ℕ) (B : Box) : ℚ := max 0 (intervalLower m (queryLower B) (queryUpper B))
def omegaUpper (m : ℕ) (B : Box) : ℚ := intervalUpper m (queryLower B) (queryUpper B)
def switchedLower (m : ℕ) (B : Box) : ℚ := k * omegaLower m B / zUpper B
def switchedUpper (m : ℕ) (B : Box) : ℚ := k * omegaUpper m B / zLower B

theorem omega_bounds (m : ℕ) (hm : 0 < m) (B : Box) {s : ℝ}
    (hs : s ∈ Icc (queryLower B : ℝ) (queryUpper B : ℝ)) :
    (omegaLower m B : ℝ) ≤ buchstab s ∧ buchstab s ≤ (omegaUpper m B : ℝ) := by
  have hq := query_valid B
  have hb := actual_interval_bounds m hm (by linarith only [hq.1]) hq.2.1 hq.2.2 hs
  have hql1 : (1 : ℝ) ≤ (queryLower B : ℝ) := by
    exact_mod_cast (show (1 : ℚ) ≤ queryLower B by linarith only [hq.1])
  have hs1 : 1 ≤ s := hql1.trans hs.1
  simp only [omegaLower, omegaUpper, Rat.cast_max, Rat.cast_zero]
  exact ⟨max_le (buchstab_nonneg hs1) hb.1, hb.2⟩

theorem omega_width (m : ℕ) (hm : 0 < m) (B : Box) :
    0 ≤ omegaUpper m B - omegaLower m B ∧
      omegaUpper m B - omegaLower m B ≤
        (queryUpper B - queryLower B) / 2 + 3000 / (m : ℚ) := by
  have hq := query_valid B
  have hw := (actual_interval_width m hm hq.1 hq.2.1 hq.2.2).2
  have hb := omega_bounds m hm B (s := (queryLower B : ℝ))
    ⟨le_rfl, by exact_mod_cast hq.2.1⟩
  have h0 : (0 : ℝ) ≤ (omegaUpper m B : ℝ) - (omegaLower m B : ℝ) := by
    linarith only [hb.1, hb.2]
  refine ⟨by exact_mod_cast h0, ?_⟩
  have hL : intervalLower m (queryLower B) (queryUpper B) ≤ omegaLower m B := le_max_right _ _
  dsimp only [omegaUpper]
  linarith only [hw, hL]

/-- Genuine tight rational bounds for the actual original switched cost. -/
theorem switched_box_bounds (m : ℕ) (hm : 0 < m) (mask : Set (ℝ × ℝ))
    (B : Box) {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    (switchedLower m B : ℝ) ≤ switchedKernel currentK buchstab v ∧
      switchedKernel currentK buchstab v ≤ (switchedUpper m B : ℝ) := by
  have hz := coordinate_bounds mask B hv hD
  have hz0 : 0 < v 2 := hz.1.trans_le hz.2.1
  have hω := omega_bounds m hm B (argument_bounds mask B hv hD)
  have hK : 0 ≤ currentK := by norm_num [currentK]
  have hLo0 : (0 : ℝ) ≤ (omegaLower m B : ℝ) := by
    simp only [omegaLower, Rat.cast_max, Rat.cast_zero]
    exact le_max_left _ _
  have hU0 : (0 : ℝ) ≤ (omegaUpper m B : ℝ) := hLo0.trans (hω.1.trans hω.2)
  simp only [switchedLower, switchedUpper, Rat.cast_div, Rat.cast_mul,
    k_cast, switchedKernel]
  constructor
  · exact (div_le_div_of_nonneg_left (mul_nonneg hK hLo0) hz0 hz.2.2).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω.1 hK) hz0.le)
  · exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω.2 hK) hz0.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hK hU0) hz.1 hz.2.1)

theorem omegaLower_range (m : ℕ) (hm : 0 < m) (B : Box) :
    0 ≤ omegaLower m B ∧ omegaLower m B ≤ 1 := by
  have hq := query_valid B
  have hb := omega_bounds m hm B (s := (queryLower B : ℝ))
    ⟨le_rfl, by exact_mod_cast hq.2.1⟩
  have hq1 : (1 : ℝ) ≤ (queryLower B : ℝ) := by
    exact_mod_cast (show (1 : ℚ) ≤ queryLower B by linarith only [hq.1])
  exact ⟨le_max_left _ _, by exact_mod_cast hb.1.trans (buchstab_le_one hq1)⟩

/-- Explicit directed switched coefficient width, with all costs paid.
The query span, coordinate span and 1/m errors are separate genuine
computed quantities; none is a supplied kernel-error certificate. -/
theorem switched_width (m : ℕ) (hm : 0 < m) (B : Box) (hB : B.Valid) :
    0 ≤ switchedUpper m B - switchedLower m B ∧
      switchedUpper m B - switchedLower m B ≤
        (k / a) * ((queryUpper B - queryLower B) / 2 + 3000 / (m : ℚ)) +
          (k / a ^ 2) * (zUpper B - zLower B) := by
  have ha : (0 : ℚ) < a := by norm_num [a]
  have hk : (0 : ℚ) ≤ k := by norm_num [k]
  have hzL : a ≤ zLower B := le_max_left _ _
  have hzU : a ≤ zUpper B := le_max_left _ _
  have hzL0 : 0 < zLower B := ha.trans_le hzL
  have hzU0 : 0 < zUpper B := ha.trans_le hzU
  have hzLU : zLower B ≤ zUpper B := max_le_max le_rfl (hB 2)
  have hω := omega_width m hm B
  have hωL := omegaLower_range m hm B
  have hInv0 : 0 ≤ 1 / zLower B - 1 / zUpper B :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hzL0 hzLU)
  have hFirst : k * (omegaUpper m B - omegaLower m B) / zLower B ≤
      (k / a) * ((queryUpper B - queryLower B) / 2 + 3000 / (m : ℚ)) := by
    have hh := (div_le_div_of_nonneg_left (mul_nonneg hk hω.1) ha hzL).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω.2 hk) ha.le)
    convert hh using 1 <;> ring
  have hSecond : k * omegaLower m B * (1 / zLower B - 1 / zUpper B) ≤
      (k / a ^ 2) * (zUpper B - zLower B) := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hωL.2 hk) hInv0
    simp only [mul_one] at hh
    have heq : k * (1 / zLower B - 1 / zUpper B) =
        k * (zUpper B - zLower B) / (zLower B * zUpper B) := by
      field_simp [hzL0.ne', hzU0.ne']
      <;> ring
    rw [heq] at hh
    have hProd : a ^ 2 ≤ zLower B * zUpper B := by
      simpa only [pow_two] using mul_le_mul hzL hzU ha.le hzL0.le
    have hDiv := div_le_div_of_nonneg_left (mul_nonneg hk (sub_nonneg.mpr hzLU))
      (pow_pos ha 2) hProd
    have hFinal := hh.trans hDiv
    convert hFinal using 1 <;> ring
  have hEq : switchedUpper m B - switchedLower m B =
      k * (omegaUpper m B - omegaLower m B) / zLower B +
        k * omegaLower m B * (1 / zLower B - 1 / zUpper B) := by
    dsimp only [switchedUpper, switchedLower]
    ring
  rw [hEq]
  exact ⟨add_nonneg (div_nonneg (mul_nonneg hk hω.1) hzL0.le)
      (mul_nonneg (mul_nonneg hk hωL.1) hInv0), add_le_add hFirst hSecond⟩

end

end ImbalancedChen.P5Z.OriginalSixteenTightSwitchedBoxes
