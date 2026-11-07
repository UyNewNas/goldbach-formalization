import ImbalancedChen.ActualThirdOriginalFixedpointClippedChord
import Mathlib.Data.Rat.Floor

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30. Original V operations needed by
NEW symmetric mean. P160 is imported once, not replaced or redefined. -/
namespace ImbalancedChen.OriginalThirdRoundedNewSourceOnly
noncomputable section
open OriginalThirdClippedChordSourceOnly

structure IV where
  lo : ℤ
  hi : ℤ

def Encloses (v : IV) (x : ℝ) : Prop := value v.lo≤x ∧ x≤value v.hi

def up (a b : ℤ) : ℤ := -((-a)/b)

def ofReal (x : ℝ) : IV := ⟨⌊x*(P160:ℝ)⌋,-⌊(-x)*(P160:ℝ)⌋⟩

def sub (v w : IV) : IV := ⟨v.lo-w.hi,v.hi-w.lo⟩

def fourLo (v w : IV) : ℤ := min (min (v.lo*w.lo) (v.lo*w.hi))
  (min (v.hi*w.lo) (v.hi*w.hi))

def fourHi (v w : IV) : ℤ := max (max (v.lo*w.lo) (v.lo*w.hi))
  (max (v.hi*w.lo) (v.hi*w.hi))

def mul (v w : IV) : IV := ⟨fourLo v w/P160,up (fourHi v w) P160⟩

/-- This is the literal V-divisor reciprocal, including its two roundings. -/
def recip (w : IV) : IV := ⟨P160*P160/w.hi,up (P160*P160) w.lo⟩

def divide (v w : IV) : IV := mul v (recip w)

private theorem value_neg (z : ℤ) : value (-z) = -value z := by simp [value, neg_div]

private theorem floor_int_div {d : ℤ} (hd : 0<d) (n : ℤ) :
    ⌊(n:ℝ)/(d:ℝ)⌋=n/d := by
  simpa using Int.floor_div_cast_of_nonneg (k:=ℝ) hd.le (n:ℝ)

/-- Literal rational coercion identity: original V(F(n,d)) rounds n*P/d.
The real constructor is used only to keep semantic formulas readable. -/
theorem ofReal_int_div_source (n d : ℤ) (hd : 0<d) :
    ofReal ((n:ℝ)/(d:ℝ)) = ⟨n*P160/d,up (n*P160) d⟩ := by
  have hl : ((n:ℝ)/(d:ℝ))*(P160:ℝ)=((n*P160:ℤ):ℝ)/(d:ℝ) := by
    push_cast
    ring
  have hu : (-((n:ℝ)/(d:ℝ)))*(P160:ℝ)=((- (n*P160):ℤ):ℝ)/(d:ℝ) := by
    push_cast
    ring
  simp only [ofReal,hl,hu,floor_int_div hd,up]

theorem ofReal_sound (x : ℝ) : Encloses (ofReal x) x := by
  have hl := Int.floor_le (x*(P160:ℝ))
  have hu := Int.floor_le ((-x)*(P160:ℝ))
  constructor
  · change (⌊x*(P160:ℝ)⌋:ℝ)/(P160:ℝ)≤x
    exact (div_le_iff₀ P160_real_pos).2 hl
  · change x≤((-⌊(-x)*(P160:ℝ)⌋:ℤ):ℝ)/(P160:ℝ)
    apply (le_div_iff₀ P160_real_pos).2
    push_cast
    linarith

theorem sub_sound {v w : IV} {x y : ℝ} (hv : Encloses v x) (hw : Encloses w y) :
    Encloses (sub v w) (x-y) := by
  constructor
  · simpa only [sub,value_sub] using sub_le_sub hv.1 hw.2
  · simpa only [sub,value_sub] using sub_le_sub hv.2 hw.1

private theorem lower_product {L a b c d x y : ℝ}
    (h11 : L≤a*c) (h12 : L≤a*d) (h21 : L≤b*c) (h22 : L≤b*d)
    (hx : a≤x ∧ x≤b) (hy : c≤y ∧ y≤d) : L≤x*y := by
  by_cases hy0 : 0≤y
  · apply le_trans (b:=a*y) _ (mul_le_mul_of_nonneg_right hx.1 hy0)
    by_cases ha0 : 0≤a
    · exact h11.trans (mul_le_mul_of_nonneg_left hy.1 ha0)
    · exact h12.trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha0))
  · apply le_trans (b:=b*y) _ (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0))
    by_cases hb0 : 0≤b
    · exact h21.trans (mul_le_mul_of_nonneg_left hy.1 hb0)
    · exact h22.trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hb0))

private theorem upper_product {U a b c d x y : ℝ}
    (h11 : a*c≤U) (h12 : a*d≤U) (h21 : b*c≤U) (h22 : b*d≤U)
    (hx : a≤x ∧ x≤b) (hy : c≤y ∧ y≤d) : x*y≤U := by
  by_cases hy0 : 0≤y
  · apply le_trans (b:=b*y) (mul_le_mul_of_nonneg_right hx.2 hy0)
    by_cases hb0 : 0≤b
    · exact (mul_le_mul_of_nonneg_left hy.2 hb0).trans h22
    · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)).trans h21
  · apply le_trans (b:=a*y) (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0))
    by_cases ha0 : 0≤a
    · exact (mul_le_mul_of_nonneg_left hy.2 ha0).trans h12
    · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)).trans h11

private theorem floor_product_le {z x y : ℤ} (h : z≤x*y) :
    value (z/P160)≤value x*value y := by
  have hc : (z:ℝ)≤((x*y:ℤ):ℝ) := by exact_mod_cast h
  calc
    _ ≤ (z:ℝ)/(P160:ℝ)/(P160:ℝ) := value_ediv_le z
    _ ≤ ((x*y:ℤ):ℝ)/(P160:ℝ)/(P160:ℝ) :=
      (div_le_div_iff_of_pos_right P160_real_pos).2
        ((div_le_div_iff_of_pos_right P160_real_pos).2 hc)
    _ = _ := by simp only [value,Int.cast_mul,div_eq_mul_inv]; ring

private theorem le_up_product {z x y : ℤ} (h : x*y≤z) :
    value x*value y≤value (up z P160) := by
  have hn : -z≤(-x)*y := by nlinarith
  have hh := neg_le_neg (floor_product_le hn)
  simpa only [up,value_neg,neg_mul,neg_neg] using hh

theorem mul_sound {v w : IV} {x y : ℝ} (hv : Encloses v x) (hw : Encloses w y) :
    Encloses (mul v w) (x*y) := by
  have hl11 : fourLo v w≤v.lo*w.lo := (min_le_left _ _).trans (min_le_left _ _)
  have hl12 : fourLo v w≤v.lo*w.hi := (min_le_left _ _).trans (min_le_right _ _)
  have hl21 : fourLo v w≤v.hi*w.lo := (min_le_right _ _).trans (min_le_left _ _)
  have hl22 : fourLo v w≤v.hi*w.hi := (min_le_right _ _).trans (min_le_right _ _)
  have hu11 : v.lo*w.lo≤fourHi v w := (le_max_left _ _).trans (le_max_left _ _)
  have hu12 : v.lo*w.hi≤fourHi v w := (le_max_right _ _).trans (le_max_left _ _)
  have hu21 : v.hi*w.lo≤fourHi v w := (le_max_left _ _).trans (le_max_right _ _)
  have hu22 : v.hi*w.hi≤fourHi v w := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨lower_product (floor_product_le hl11) (floor_product_le hl12)
      (floor_product_le hl21) (floor_product_le hl22) hv hw,
    upper_product (le_up_product hu11) (le_up_product hu12)
      (le_up_product hu21) (le_up_product hu22) hv hw⟩

private theorem value_div_le {d : ℤ} (hd : 0<d) (n : ℤ) :
    value (n/d)≤(n:ℝ)/(d:ℝ)/(P160:ℝ) := by
  have h := Int.floor_le ((n:ℝ)/(d:ℝ))
  rw [floor_int_div hd n] at h
  exact (div_le_div_iff_of_pos_right P160_real_pos).2 h

private theorem le_value_up {d : ℤ} (hd : 0<d) (n : ℤ) :
    (n:ℝ)/(d:ℝ)/(P160:ℝ)≤value (up n d) := by
  have h := neg_le_neg (value_div_le hd (-n))
  simpa only [up,value_neg,Int.cast_neg,neg_div,neg_neg] using h

theorem recip_sound {w : IV} {y : ℝ} (hw : Encloses w y) (hlo : 0<w.lo) :
    Encloses (recip w) (1/y) := by
  have hlr : 0<(w.lo:ℝ) := by exact_mod_cast hlo
  have hvl : 0<value w.lo := div_pos hlr P160_real_pos
  have hy : 0<y := hvl.trans_le hw.1
  have hvh : 0<value w.hi := hy.trans_le hw.2
  have hhr : 0<(w.hi:ℝ) := (div_pos_iff_of_pos_right P160_real_pos).1 hvh
  have hhi : 0<w.hi := by exact_mod_cast hhr
  have alg (z : ℤ) (hz : (z:ℝ)≠0) : ((P160*P160:ℤ):ℝ)/(z:ℝ)/(P160:ℝ)=1/value z := by
    unfold value
    push_cast
    field_simp [hz,P160_real_pos.ne']
  constructor
  · calc
      value (P160*P160/w.hi) ≤ ((P160*P160:ℤ):ℝ)/(w.hi:ℝ)/(P160:ℝ) :=
        value_div_le hhi _
      _ = 1/value w.hi := alg _ hhr.ne'
      _ ≤ 1/y := div_le_div_of_nonneg_left (by norm_num) hy hw.2
  · calc
      1/y ≤ 1/value w.lo := div_le_div_of_nonneg_left (by norm_num) hvl hw.1
      _ = ((P160*P160:ℤ):ℝ)/(w.lo:ℝ)/(P160:ℝ) := (alg _ hlr.ne').symm
      _ ≤ value (up (P160*P160) w.lo) := le_value_up hlo _

theorem divide_sound {v w : IV} {x y : ℝ}
    (hv : Encloses v x) (hw : Encloses w y) (hlo : 0<w.lo) :
    Encloses (divide v w) (x/y) := by
  simpa only [divide,div_eq_mul_inv,one_div,one_mul] using mul_sound hv (recip_sound hw hlo)

end
end ImbalancedChen.OriginalThirdRoundedNewSourceOnly
