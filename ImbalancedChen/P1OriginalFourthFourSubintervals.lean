import ImbalancedChen.P1OriginalFourthN8193

/-! The four positive subintervals of the fourth-prefix cap difference,
with the upward-rounded mesh index and the original two fourth-coordinate
factors. The reciprocal difference formula also holds for equal endpoints. -/
namespace ImbalancedChen.P1OriginalFourthFourSubintervals
noncomputable section
open Set
open scoped BigOperators
open OriginalU2CoupledRecurrenceSourceOnly
open P1OriginalFourthDerivativeNumerator P1OriginalFourthN8193

def ceilIndex (s : ℚ) : ℕ := ⌈4096*(s-3)⌉₊

theorem ceilIndex_lt {s : ℚ} (h : s ≤ 5) : ceilIndex s < 8193 := by
  have hh : ceilIndex s ≤ 8192 := Nat.ceil_le.mpr (by norm_num; linarith)
  omega

theorem ceilIndex_upper (s : ℚ) : (s:ℝ) ≤ node (ceilIndex s) := by
  have hq : 4096*(s-3) ≤ (ceilIndex s:ℚ) := Nat.le_ceil _
  have hr : 4096*((s:ℝ)-3) ≤ (ceilIndex s:ℝ) := by exact_mod_cast hq
  unfold node
  linarith only [hr]

def credit (j : Fin 8193) : ℝ := (stored j.val:ℝ)/2^80

theorem credit_nonneg (j : Fin 8193) : 0 ≤ credit j := by unfold credit; positivity

theorem upper_differentiable {s : ℝ} (hs : 1 < s) : DifferentiableAt ℝ upper s := by
  rcases lt_trichotomy s 3 with h | rfl | h
  · exact (hasDerivAt_upper_base hs h).differentiableAt
  · exact hasDerivAt_upper_three.differentiableAt
  · exact (hasDerivAt_upper_tail h).differentiableAt

theorem reciprocal_difference (j : Fin 8193) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ node j.val) :
    credit j/a-credit j/b ≤ upper a-upper b := by
  let f (x : ℝ) := upper x-credit j/x
  let d (x : ℝ) := (credit j-numerator x)/x^2
  have hd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt f (d x) x := by
    have hx0 : x ≠ 0 := ne_of_gt (by linarith [hx.1])
    have hh := (upper_differentiable (ha.trans_le hx.1)).hasDerivAt.sub
      ((hasDerivAt_const x (credit j)).fun_div (hasDerivAt_id x) hx0)
    apply hh.congr_deriv
    dsimp [d,numerator]
    field_simp [hx0] <;> ring
  have hmono : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (f' := d)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hi : x ∈ Icc a b := interior_subset hx
      have hn := original_ceiling_lookup j (ha.trans_le hi.1) (hi.2.trans hb)
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn) (sq_nonneg x)
  have hh := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  dsimp only [f] at hh
  linarith only [hh]

def blend (a b : ℝ) (k : ℕ) : ℝ := (1-(k:ℝ)/4)*a+((k:ℝ)/4)*b

@[simp] theorem blend_zero (a b : ℝ) : blend a b 0 = a := by simp [blend]
@[simp] theorem blend_four (a b : ℝ) : blend a b 4 = b := by norm_num [blend]

theorem blend_step (a b : ℝ) (k : ℕ) :
    blend a b (k+1)-blend a b k = (b-a)/4 := by push_cast [blend]; ring

theorem blend_bounds {a b : ℝ} (hab : a ≤ b) {k : ℕ} (hk : k ≤ 4) :
    a ≤ blend a b k ∧ blend a b k ≤ b := by
  have hk1 : (k:ℝ) ≤ 4 := by exact_mod_cast hk
  have h0 : 0 ≤ (k:ℝ)/4 := by positivity
  have h1 : 0 ≤ 1-(k:ℝ)/4 := by linarith
  unfold blend
  constructor
  · nlinarith only [mul_nonneg h0 (sub_nonneg.mpr hab)]
  · nlinarith only [mul_nonneg h1 (sub_nonneg.mpr hab)]

theorem blend_compare {a b A B : ℝ} (ha : a ≤ A) (hb : b ≤ B) {k : ℕ} (hk : k ≤ 4) :
    blend a b k ≤ blend A B k := by
  have hk1 : (k:ℝ) ≤ 4 := by exact_mod_cast hk
  exact add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
    (mul_le_mul_of_nonneg_left hb (by positivity))

def segmentWeight (A B : ℝ) (ix : Fin 4 → Fin 8193) (k : Fin 4) : ℝ :=
  credit (ix k)/(4*blend A B k.val*blend A B (k.val+1))

/-- Four original reciprocal endpoint products. All four comparisons are
against the same old and new residuals. -/
theorem cap_difference {w a b A B : ℝ} (hw : 0 < w) (ha : w < a) (hab : a ≤ b)
    (hA : a ≤ A) (hB : b ≤ B) (ix : Fin 4 → Fin 8193)
    (hi : ∀ k : Fin 4, blend A B (k.val+1)/w ≤ node (ix k).val) :
    w*(b-a)*(∑ k, segmentWeight A B ix k) ≤ upper (a/w)-upper (b/w) := by
  let p (k : ℕ) := blend a b k
  have hp {k : ℕ} (hk : k ≤ 4) : w < p k := ha.trans_le (blend_bounds hab hk).1
  have one (k : Fin 4) :
      w*(b-a)*segmentWeight A B ix k ≤ upper (p k.val/w)-upper (p (k.val+1)/w) := by
    have h4 : k.val+1 ≤ 4 := by omega
    have hL : 0 < p k.val := hw.trans (hp (by omega))
    have hR : 0 < p (k.val+1) := hw.trans (hp h4)
    have hAL : p k.val ≤ blend A B k.val := blend_compare hA hB (by omega)
    have hAR : p (k.val+1) ≤ blend A B (k.val+1) := blend_compare hA hB h4
    have hd : p (k.val+1)-p k.val = (b-a)/4 := blend_step _ _ _
    have hdiff := reciprocal_difference (ix k)
      ((one_lt_div hw).mpr (hp (by omega) : w < p k.val))
      (div_le_div_of_nonneg_right (show p k.val ≤ p (k.val+1) by linarith only [hd,hab]) hw.le)
      ((div_le_div_of_nonneg_right hAR hw.le).trans (hi k))
    have hden : 4*p k.val*p (k.val+1) ≤ 4*blend A B k.val*blend A B (k.val+1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hAL (by norm_num)) hAR hR.le
        (mul_nonneg (by norm_num) (hL.le.trans hAL))
    have hweight := div_le_div_of_nonneg_left (credit_nonneg (ix k))
      (show 0 < 4*p k.val*p (k.val+1) by positivity) hden
    calc
      _ ≤ w*(b-a)*(credit (ix k)/(4*p k.val*p (k.val+1))) :=
        mul_le_mul_of_nonneg_left hweight (mul_nonneg hw.le (sub_nonneg.mpr hab))
      _ = credit (ix k)/(p k.val/w)-credit (ix k)/(p (k.val+1)/w) := by
        rw [show b-a = 4*(p (k.val+1)-p k.val) by linarith only [hd]]
        field_simp [hw.ne',hL.ne',hR.ne'] <;> ring
      _ ≤ _ := hdiff
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum (fun k _ => one k)).trans ?_
  have ht : (∑ k : Fin 4, (upper (p k.val/w)-upper (p (k.val+1)/w))) =
      upper (p 0/w)-upper (p 4/w) := by
    simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ]
    norm_num
    <;> ring
  rw [ht]
  simp [p]

theorem fourth_density {x y z w a b A B : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hw : 0 < w) (ha : w < a) (hab : a ≤ b) (hA : a ≤ A) (hB : b ≤ B)
    (ix : Fin 4 → Fin 8193)
    (hi : ∀ k : Fin 4, blend A B (k.val+1)/w ≤ node (ix k).val) :
    4*(b-a)/(x*y*z*w)*(∑ k, segmentWeight A B ix k) ≤
      4*(upper (a/w)-upper (b/w))/(x*y*z*w^2) := by
  have hd := cap_difference hw ha hab hA hB ix hi
  have hden : 0 < x*y*z*w^2 := by positivity
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 4)) hden.le
  refine le_trans (le_of_eq ?_) h
  field_simp [hx.ne',hy.ne',hz.ne',hw.ne'] <;> ring

end
end ImbalancedChen.P1OriginalFourthFourSubintervals
