import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30.
Exact P=2^160 signed lower product and OLD weight clipping from the original
independent compact certifier. No numeric replay or analytic assumption. -/
namespace ImbalancedChen.OriginalThirdClippedChordSourceOnly
noncomputable section

def P160 : ℤ := 2^160

def value (z : ℤ) : ℝ := (z:ℝ)/(P160:ℝ)

def clippedLo (l : ℤ) : ℤ := max 0 l

def clippedHi (u : ℤ) : ℤ := min P160 u

/-- Four endpoint products of V(l,u)*V(d,d) reduce to these two. -/
def signedProductLo (l u d : ℤ) : ℤ := min (l*d) (u*d) / P160

def oldChordLo (l u fl fh : ℤ) : ℤ :=
  fl + signedProductLo (clippedLo l) (clippedHi u) (fh-fl)

def meanHigh (l u fl fh out : ℤ) : ℤ := max 0 (out-oldChordLo l u fl fh)

theorem P160_pos : (0:ℤ)<P160 := by norm_num [P160]

theorem P160_real_pos : (0:ℝ)<(P160:ℝ) := by exact_mod_cast P160_pos

@[simp] theorem value_zero : value 0=0 := by simp [value]

@[simp] theorem value_P160 : value P160=1 := by
  exact div_self P160_real_pos.ne'

theorem value_mono {i j : ℤ} (h : i≤j) : value i≤value j := by
  apply (div_le_div_iff_of_pos_right P160_real_pos).2
  exact_mod_cast h

theorem value_le_iff {i j : ℤ} : value i≤value j ↔ i≤j := by
  constructor
  · intro h
    have hc : (i:ℝ)≤(j:ℝ) := (div_le_div_iff_of_pos_right P160_real_pos).1 h
    exact_mod_cast hc
  · exact value_mono

@[simp] theorem value_add (i j : ℤ) : value (i+j)=value i+value j := by
  simp [value,add_div]

@[simp] theorem value_sub (i j : ℤ) : value (i-j)=value i-value j := by
  simp [value,sub_div]

@[simp] theorem value_max (i j : ℤ) : value (max i j)=max (value i) (value j) := by
  rcases le_total i j with h|h
  · rw [max_eq_right h,max_eq_right (value_mono h)]
  · rw [max_eq_left h,max_eq_left (value_mono h)]

@[simp] theorem value_min (i j : ℤ) : value (min i j)=min (value i) (value j) := by
  rcases le_total i j with h|h
  · rw [min_eq_left h,min_eq_left (value_mono h)]
  · rw [min_eq_right h,min_eq_right (value_mono h)]

theorem signedProductLo_original_four_products (l u d : ℤ) :
    signedProductLo l u d = min (min (l*d) (l*d)) (min (u*d) (u*d)) / P160 := by
  simp [signedProductLo]

/-- Int.ediv is floor here, including a negative numerator. -/
theorem value_ediv_le (z : ℤ) :
    value (z/P160) ≤ (z:ℝ)/(P160:ℝ)/(P160:ℝ) := by
  have hf : ⌊(z:ℝ)/(P160:ℝ)⌋=z/P160 := by
    simpa using Int.floor_div_cast_of_nonneg (k:=ℝ) P160_pos.le (z:ℝ)
  have hc : ((z/P160:ℤ):ℝ)≤(z:ℝ)/(P160:ℝ) := by
    rw [← hf]
    exact Int.floor_le _
  exact (div_le_div_iff_of_pos_right P160_real_pos).2 hc

theorem signedProductLo_le_left (l u d : ℤ) :
    value (signedProductLo l u d)≤value l*value d := by
  have hm : ((min (l*d) (u*d):ℤ):ℝ)≤((l*d:ℤ):ℝ) := by
    exact_mod_cast min_le_left (l*d) (u*d)
  calc
    _ ≤ ((min (l*d) (u*d):ℤ):ℝ)/(P160:ℝ)/(P160:ℝ) := value_ediv_le _
    _ ≤ ((l*d:ℤ):ℝ)/(P160:ℝ)/(P160:ℝ) :=
      (div_le_div_iff_of_pos_right P160_real_pos).2
        ((div_le_div_iff_of_pos_right P160_real_pos).2 hm)
    _ = _ := by simp only [value,Int.cast_mul,div_eq_mul_inv]; ring

theorem signedProductLo_le_right (l u d : ℤ) :
    value (signedProductLo l u d)≤value u*value d := by
  have hm : ((min (l*d) (u*d):ℤ):ℝ)≤((u*d:ℤ):ℝ) := by
    exact_mod_cast min_le_right (l*d) (u*d)
  calc
    _ ≤ ((min (l*d) (u*d):ℤ):ℝ)/(P160:ℝ)/(P160:ℝ) := value_ediv_le _
    _ ≤ ((u*d:ℤ):ℝ)/(P160:ℝ)/(P160:ℝ) :=
      (div_le_div_iff_of_pos_right P160_real_pos).2
        ((div_le_div_iff_of_pos_right P160_real_pos).2 hm)
    _ = _ := by simp only [value,Int.cast_mul,div_eq_mul_inv]; ring

theorem signedProductLo_sound {l u d : ℤ} {w : ℝ}
    (hl : value l≤w) (hu : w≤value u) :
    value (signedProductLo l u d)≤w*value d := by
  by_cases hd : 0≤value d
  · exact (signedProductLo_le_left l u d).trans (mul_le_mul_of_nonneg_right hl hd)
  · exact (signedProductLo_le_right l u d).trans
      (mul_le_mul_of_nonpos_right hu (le_of_not_ge hd))

/-- The clipping uses the mathematically justified OLD weight range.
It also proves the constructor's clipped lo<=hi invariant. -/
theorem clipped_weight_encloses {l u : ℤ} {w : ℝ}
    (hw0 : 0≤w) (hw1 : w≤1) (hl : value l≤w) (hu : w≤value u) :
    value (clippedLo l)≤w ∧ w≤value (clippedHi u) ∧ clippedLo l≤clippedHi u := by
  have hcl : value (clippedLo l)≤w := by
    simpa only [clippedLo,value_max,value_zero] using max_le hw0 hl
  have hcu : w≤value (clippedHi u) := by
    simpa only [clippedHi,value_min,value_P160] using le_min hw1 hu
  exact ⟨hcl,hcu,value_le_iff.mp (hcl.trans hcu)⟩

/-- No monotonicity of the rounded endpoint pair fl,fh is assumed. -/
theorem oldChordLo_sound {l u fl fh : ℤ} {w : ℝ}
    (hw0 : 0≤w) (hw1 : w≤1) (hl : value l≤w) (hu : w≤value u) :
    value (oldChordLo l u fl fh)≤value fl+w*(value fh-value fl) := by
  have hc := clipped_weight_encloses hw0 hw1 hl hu
  have hp := signedProductLo_sound (d:=fh-fl) hc.1 hc.2.1
  simpa only [oldChordLo,value_add,value_sub,add_comm] using add_le_add_left hp (value fl)

/-- The original integer nonnegative candidate majorizes the real Jensen
candidate after its signed lower chord is rounded down. -/
theorem meanHigh_sound {l u fl fh out : ℤ} {w : ℝ}
    (hw0 : 0≤w) (hw1 : w≤1) (hl : value l≤w) (hu : w≤value u) :
    max 0 (value out-(value fl+w*(value fh-value fl)))≤value (meanHigh l u fl fh out) := by
  have hc := oldChordLo_sound (fl:=fl) (fh:=fh) hw0 hw1 hl hu
  simp only [meanHigh,value_max,value_zero,value_sub]
  exact max_le_max le_rfl (sub_le_sub_left hc (value out))

end
end ImbalancedChen.OriginalThirdClippedChordSourceOnly
