import ImbalancedChen.P5ZU1011BuchstabTailLipschitz
import ImbalancedChen.P5ZU1011OriginalSixteenOscillation

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Quantitative oscillation of the TRUE original switched fallback. A
max-two extension agrees on the original domain and is quantitatively
controlled throughout the original compact coordinate box, including mesh
corners outside the ordered support. No kernel-modulus premise occurs.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSwitchedOscillation

noncomputable section

open Set Filter Topology U11Integral U11Canonical
open U1011OriginalSixteenOscillation U1011BuchstabTailLipschitz
open LiLiuPrereqBuchstab
open scoped BigOperators

def argument (v : LogFour) : ℝ := (1 - U11SelectedLargest.prefixSum v) / v 2
def extendedSwitched (v : LogFour) : ℝ := currentK * buchstab (max 2 (argument v)) / v 2

theorem compact_residual_bounds {v : LogFour} (hv : v ∈ compactBox) :
    0 ≤ 1 - U11SelectedLargest.prefixSum v ∧ 1 - U11SelectedLargest.prefixSum v ≤ 1 := by
  have hlo (i : Fin 4) : (417 / 5000 : ℝ) ≤ v i := hv.1 i
  have hhi (i : Fin 4) : v i ≤ (59 / 250 : ℝ) := hv.2 i
  unfold U11SelectedLargest.prefixSum
  constructor <;> linarith only [hlo 0, hlo 1, hlo 2, hlo 3, hhi 0, hhi 1, hhi 2, hhi 3]

private theorem inverse_abs_le_thirteen {x : ℝ} (hx : (1 / 13 : ℝ) ≤ x) : |1 / x| ≤ 13 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [abs_of_pos (one_div_pos.mpr hx0)]
  apply (div_le_iff₀ hx0).mpr
  linarith only [hx]

private theorem inverse_abs_sub_le {x y : ℝ}
    (hx : (1 / 13 : ℝ) ≤ x) (hy : (1 / 13 : ℝ) ≤ y) :
    |1 / x - 1 / y| ≤ 169 * |x - y| := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hden : (1 / 169 : ℝ) ≤ x * y := by
    have hh := mul_le_mul hx hy (by norm_num : (0 : ℝ) ≤ 1 / 13) hx0.le
    norm_num only [show (1 / 13 : ℝ) * (1 / 13) = 1 / 169 by norm_num] at hh
    exact hh
  have heq : 1 / x - 1 / y = (y - x) / (x * y) := by
    field_simp [hx0.ne', hy0.ne']
    <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm y x]
  calc
    _ ≤ |x - y| / (1 / 169) := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
    _ = _ := by ring

theorem argument_abs_sub_le {v w : LogFour} (hv : v ∈ compactBox) (hw : w ∈ compactBox) :
    |argument v - argument w| ≤ 182 * l1Delta v w := by
  have hD := l1Delta_nonneg v w
  have hzV : (1 / 13 : ℝ) ≤ v 2 := by linarith only [hv.1 2]
  have hzW : (1 / 13 : ℝ) ≤ w 2 := by linarith only [hw.1 2]
  have hzV0 : 0 < v 2 := lt_of_lt_of_le (by norm_num) hzV
  have hzW0 : 0 < w 2 := lt_of_lt_of_le (by norm_num) hzW
  have hPrefix := prefixSum_abs_sub_le v w
  have hCoord := coordinate_abs_sub_le_l1Delta v w 2
  have hInv := (inverse_abs_sub_le hzV hzW).trans
    (mul_le_mul_of_nonneg_left hCoord (by norm_num))
  have hNW : |1 - U11SelectedLargest.prefixSum w| ≤ 1 := by
    rw [abs_of_nonneg (compact_residual_bounds hw).1]
    exact (compact_residual_bounds hw).2
  have heq : argument v - argument w =
      (U11SelectedLargest.prefixSum w - U11SelectedLargest.prefixSum v) * (1 / v 2) +
        (1 - U11SelectedLargest.prefixSum w) * (1 / v 2 - 1 / w 2) := by
    unfold argument
    field_simp [hzV0.ne', hzW0.ne']
    <;> ring
  have h1 : |(U11SelectedLargest.prefixSum w - U11SelectedLargest.prefixSum v) * (1 / v 2)| ≤
      13 * l1Delta v w := by
    rw [abs_mul, abs_sub_comm (U11SelectedLargest.prefixSum w) (U11SelectedLargest.prefixSum v)]
    have hh := mul_le_mul hPrefix (inverse_abs_le_thirteen hzV) (abs_nonneg _) hD
    nlinarith only [hh]
  have h2 : |(1 - U11SelectedLargest.prefixSum w) * (1 / v 2 - 1 / w 2)| ≤
      169 * l1Delta v w := by
    rw [abs_mul]
    have hh := mul_le_mul hNW hInv (abs_nonneg _) zero_le_one
    simpa only [one_mul] using hh
  rw [heq]
  have hh := (abs_add _ _).trans (add_le_add h1 h2)
  nlinarith only [hh]

theorem clamped_argument_abs_sub_le {v w : LogFour} (hv : v ∈ compactBox) (hw : w ∈ compactBox) :
    |max 2 (argument v) - max 2 (argument w)| ≤ 182 * l1Delta v w := by
  have hh := abs_max_sub_max_le_max (2 : ℝ) (argument v) 2 (argument w)
  exact hh.trans (max_le (by simp; positivity) (argument_abs_sub_le hv hw))

/-- A genuine explicit modulus on the WHOLE original compact coordinate
box, even when the two points cross delay-integer or max-two seams. -/
theorem extendedSwitched_abs_sub_le {v w : LogFour}
    (hv : v ∈ compactBox) (hw : w ∈ compactBox) :
    |extendedSwitched v - extendedSwitched w| ≤ 10000 * l1Delta v w := by
  have hD := l1Delta_nonneg v w
  have hzV : (1 / 13 : ℝ) ≤ v 2 := by linarith only [hv.1 2]
  have hzW : (1 / 13 : ℝ) ≤ w 2 := by linarith only [hw.1 2]
  have hzV0 : 0 < v 2 := lt_of_lt_of_le (by norm_num) hzV
  have hzW0 : 0 < w 2 := lt_of_lt_of_le (by norm_num) hzW
  have hω := (abs_sub_le_half (le_max_left (2 : ℝ) (argument v))
    (le_max_left (2 : ℝ) (argument w))).trans
      (div_le_div_of_nonneg_right (clamped_argument_abs_sub_le hv hw) (by norm_num))
  have hω' : |buchstab (max 2 (argument v)) - buchstab (max 2 (argument w))| ≤ 91 * l1Delta v w := by
    nlinarith only [hω]
  have hInv := (inverse_abs_sub_le hzV hzW).trans
    (mul_le_mul_of_nonneg_left (coordinate_abs_sub_le_l1Delta v w 2) (by norm_num))
  have hωW : |buchstab (max 2 (argument w))| ≤ 1 := by
    have hs : 1 ≤ max 2 (argument w) := by linarith [le_max_left (2 : ℝ) (argument w)]
    rw [abs_of_nonneg (buchstab_nonneg hs)]
    exact buchstab_le_one hs
  have h1 : |(buchstab (max 2 (argument v)) - buchstab (max 2 (argument w))) * (1 / v 2)| ≤
      1183 * l1Delta v w := by
    rw [abs_mul]
    have hh := mul_le_mul hω' (inverse_abs_le_thirteen hzV) (abs_nonneg _) (by positivity)
    nlinarith only [hh]
  have h2 : |buchstab (max 2 (argument w)) * (1 / v 2 - 1 / w 2)| ≤
      169 * l1Delta v w := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hωW hInv (abs_nonneg _) zero_le_one
  have heq : extendedSwitched v - extendedSwitched w = currentK *
      ((buchstab (max 2 (argument v)) - buchstab (max 2 (argument w))) * (1 / v 2) +
        buchstab (max 2 (argument w)) * (1 / v 2 - 1 / w 2)) := by
    unfold extendedSwitched
    field_simp [hzV0.ne', hzW0.ne']
    <;> ring
  have hSum := (abs_add _ _).trans (add_le_add h1 h2)
  have hK : 0 ≤ currentK := by norm_num [currentK]
  have hK7 : currentK ≤ 7 := by norm_num [currentK]
  have hkD := mul_le_mul_of_nonneg_right hK7 hD
  rw [heq, abs_mul, abs_of_nonneg hK]
  have hh := mul_le_mul_of_nonneg_left hSum hK
  nlinarith only [hh, hkD, hD]

theorem extendedSwitched_eq_actual (mask : Set (ℝ × ℝ)) (v : LogFour)
    (hv : v ∈ originalDomain mask) : extendedSwitched v = switchedKernel currentK buchstab v := by
  have hs := originalDomain_argument_mem mask v hv
  have harg : argument v = (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 := by
    rfl
  have hs2 : 2 ≤ argument v := by rw [harg]; linarith only [hs.1]
  simp only [extendedSwitched, max_eq_right hs2, switchedKernel, harg]

theorem actual_switched_abs_sub_le (mask : Set (ℝ × ℝ)) (v w : LogFour)
    (hv : v ∈ originalDomain mask) (hw : w ∈ originalDomain mask) :
    |switchedKernel currentK buchstab v - switchedKernel currentK buchstab w| ≤
      10000 * l1Delta v w := by
  rw [← extendedSwitched_eq_actual mask v hv, ← extendedSwitched_eq_actual mask w hw]
  exact extendedSwitched_abs_sub_le (originalDomain_subset_compactBox mask hv)
    (originalDomain_subset_compactBox mask hw)

theorem meshLo_mem_compact (m : ℕ) (j : Fin 4 → Fin (m + 1)) :
    logPrimeMeshLo (417 / 5000) (59 / 250) m j ∈ compactBox := by
  constructor <;> intro i
  · exact (logPrimeMeshLoHi_bounds (by norm_num : (417 / 5000 : ℝ) < 59 / 250) m j i).1
  · have hh := logPrimeMeshLoHi_bounds (by norm_num : (417 / 5000 : ℝ) < 59 / 250) m j i
    exact hh.2.1.le.trans hh.2.2

/-- The actual original switched kernel is approximated by a true
max-two Buchstab value at the mesh corner, with an explicit shrinking
40000*step error. No arbitrary modulus is supplied. -/
theorem actual_switched_mesh_error (mask : Set (ℝ × ℝ)) (m : ℕ)
    (j : Fin 4 → Fin (m + 1)) (v : LogFour)
    (hv : v ∈ originalDomain mask)
    (hcell : v ∈ logPrimeMeshCell (417 / 5000) (59 / 250) m j) :
    |switchedKernel currentK buchstab v -
      extendedSwitched (logPrimeMeshLo (417 / 5000) (59 / 250) m j)| ≤
        40000 * logPrimeMeshStep (417 / 5000) (59 / 250) m := by
  rw [← extendedSwitched_eq_actual mask v hv]
  have hh := extendedSwitched_abs_sub_le (originalDomain_subset_compactBox mask hv) (meshLo_mem_compact m j)
  exact hh.trans (by nlinarith [l1Delta_meshLo_le j hcell])

/-- One actual mesh is chosen before every tuple, cell and arbitrary
original keep mask. The accuracy is paid by the proved quantitative
fallback estimate, not by an assumed uniform continuity supplier. -/
theorem exists_actual_switched_mesh {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, ∀ (mask : Set (ℝ × ℝ)) (j : Fin 4 → Fin (m + 1)) (v : LogFour),
      v ∈ originalDomain mask →
      v ∈ logPrimeMeshCell (417 / 5000) (59 / 250) m j →
      |switchedKernel currentK buchstab v -
        extendedSwitched (logPrimeMeshLo (417 / 5000) (59 / 250) m j)| ≤ epsilon := by
  obtain ⟨m, hm⟩ := ((tendsto_logPrimeMeshStep (417 / 5000 : ℝ) (59 / 250)).eventually
    (gt_mem_nhds (show (0 : ℝ) < epsilon / 40000 by positivity))).exists
  refine ⟨m, ?_⟩
  intro mask j v hv hcell
  have hh := actual_switched_mesh_error mask m j v hv hcell
  linarith only [hh, hm]

end

end ImbalancedChen.P5Z.U1011OriginalSwitchedOscillation
