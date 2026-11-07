import ImbalancedChen.P5ZU1011OriginalSixteenOrdinaryBoxBounds

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual switched fallback bounds for original sixteen-bank certificates.
The genuine original-domain argument and Buchstab [1/2,1] range discharge
both switched endpoints. A positive original-coordinate clamp makes the
rational endpoint functions total without a switched-cell-bound premise.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenSwitchedBoxBounds

noncomputable section

open Set U11Integral U11Canonical
open U1011OriginalSixteenPolicyBank.BoxCertificates
open LiLiuPrereqBuchstab

def k : ℚ := 8452171 / 1250000
def a : ℚ := 417 / 5000
def zLower (B : Box) : ℚ := max a (B.lo 2)
def zUpper (B : Box) : ℚ := max a (B.hi 2)
def switchedLower (B : Box) : ℚ := k / (2 * zUpper B)
def switchedUpper (B : Box) : ℚ := k / zLower B

theorem k_cast : (k : ℝ) = currentK := by norm_num [k, currentK]

theorem switched_box_bounds (mask : Set (ℝ × ℝ)) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    (switchedLower B : ℝ) ≤ switchedKernel currentK buchstab v ∧
      switchedKernel currentK buchstab v ≤ (switchedUpper B : ℝ) := by
  have hz := (originalDomain_denominators_pos mask v hD).2
  have hA : (a : ℝ) ≤ v 2 := (originalDomain_subset_compactBox mask hD).1 2
  have hzLo : (zLower B : ℝ) ≤ v 2 := by
    simp only [zLower, Rat.cast_max]
    exact max_le hA (hv.1 2)
  have hzHi : v 2 ≤ (zUpper B : ℝ) :=
    (hv.2 2).trans (by simp only [zUpper, Rat.cast_max]; exact le_max_right _ _)
  have hLo0 : (0 : ℝ) < (zLower B : ℝ) := by
    have hh : (a : ℝ) ≤ (zLower B : ℝ) := by
      simp only [zLower, Rat.cast_max]
      exact le_max_left _ _
    norm_num [a] at hh
    linarith only [hh]
  have hHi0 : (0 : ℝ) < (zUpper B : ℝ) := hz.trans_le hzHi
  have hs := originalDomain_argument_mem mask v hD
  have hs1 : 1 ≤ (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 := by
    linarith only [hs.1]
  have hωL := one_half_le_buchstab hs1
  have hωU := buchstab_le_one hs1
  have hK : 0 ≤ currentK := by norm_num [currentK]
  have hKL : currentK / 2 ≤ currentK * buchstab
      ((1 - (v 0 + v 1 + v 2 + v 3)) / v 2) := by
    have hh := mul_le_mul_of_nonneg_left hωL hK
    nlinarith only [hh]
  have hKU : currentK * buchstab
      ((1 - (v 0 + v 1 + v 2 + v 3)) / v 2) ≤ currentK := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hωU hK
  simp only [switchedLower, switchedUpper, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, k_cast, switchedKernel]
  constructor
  · have heq : currentK / (2 * (zUpper B : ℝ)) = (currentK / 2) / (zUpper B : ℝ) := by ring
    rw [heq]
    exact (div_le_div_of_nonneg_left (by positivity : 0 ≤ currentK / 2) hz hzHi).trans
      (div_le_div_of_nonneg_right hKL hz.le)
  · exact (div_le_div_of_nonneg_right hKU hz.le).trans
      (div_le_div_of_nonneg_left hK hLo0 hzLo)

end

end ImbalancedChen.P5Z.OriginalSixteenSwitchedBoxBounds
