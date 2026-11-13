import ImbalancedChen.Part3OriginalInverseShortSums
import ImbalancedChen.Part3IntervalFourierChordLower

/-! Thresholds of the *actual* geometric sums have quantitatively short
circular arcs, uniformly in the starting integer of each interval. -/
namespace ImbalancedChen.Part3.OriginalShortIntervalLayers20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalInverseShortSums20261113 ActualIntervalGeometricSumSourceOnly
open private phase_sum_length_bound phaseAt_norm from ImbalancedChen.Part3ActualIntervalGeometricSum

def nearest (x : ℝ) : ℤ := ⌊x+1/2⌋

private theorem half_arc (x : ℝ) : |x-(nearest x:ℝ)|≤1/2 := by
  have lo := Int.floor_le (x+1/2)
  have hi := Int.lt_floor_add_one (x+1/2)
  dsimp [nearest]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem period (x : ℝ) (q : ℤ) : phaseBase (x-(q:ℝ))=phaseBase x := by
  unfold phaseBase
  have shift : 2*(Real.pi:ℂ)*Complex.I*((x-(q:ℝ):ℝ):ℂ) =
      2*(Real.pi:ℂ)*Complex.I*(x:ℂ)+((-q:ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
    push_cast
    ring
  rw [shift,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

private theorem chord (x : ℝ) : 4*|x-(nearest x:ℝ)| ≤ ‖1-phaseBase x‖ := by
  let y := x-(nearest x:ℝ)
  have cap : |y|≤1/2 := half_arc x
  have e : phaseBase y=Complex.exp (Complex.I*((2*Real.pi*y:ℝ):ℂ)) := by
    unfold phaseBase
    congr 1
    push_cast
    ring
  have c : ‖1-phaseBase x‖=2*|Real.sin (Real.pi*y)| := by
    rw [←period x (nearest x),show phaseBase (x-(nearest x:ℝ))=phaseBase y from rfl,
      norm_sub_rev,e,Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2*Real.pi*y/2=Real.pi*y by ring]
    simp [Real.norm_eq_abs,abs_mul]
  have j := Real.mul_le_sin (mul_nonneg Real.pi_pos.le (abs_nonneg y))
    (by nlinarith only [mul_le_mul_of_nonneg_left cap Real.pi_pos.le] :
      Real.pi*|y|≤Real.pi/2)
  have eq : (2/Real.pi)*(Real.pi*|y|)=2*|y| := by field_simp [Real.pi_ne_zero] <;> ring
  rw [eq] at j
  have s : Real.sin (Real.pi*|y|)≤|Real.sin (Real.pi*y)| := by
    rcases le_total 0 y with h|h
    · rw [abs_of_nonneg h]
      exact le_abs_self _
    · rw [abs_of_nonpos h,mul_neg,Real.sin_neg]
      exact neg_le_abs _
  rw [c]
  change 4*|y|≤_
  linarith

/-- Integer layer i of a short interval forces the frequency into an arc
of radius 1/i. This includes exact resonance, a zero-length interval and
the first layer. -/
theorem short_arc (x : ℝ) {a b i : ℕ} (hab : a≤b) (hi : 1≤i)
    (h : i≤⌈‖shortSum (Ico a b) x‖⌉₊) : |x-(nearest x:ℝ)| ≤ 1/(i:ℝ) := by
  by_cases first : i=1
  · subst i
    simpa only [Nat.cast_one,div_one] using (half_arc x).trans (by norm_num : (1:ℝ)/2≤1)
  have ip : (0:ℝ)<i := by exact_mod_cast hi
  have two : (2:ℝ)≤i := by exact_mod_cast (by omega : 2≤i)
  let V := ‖shortSum (Ico a b) x‖
  have vp : 0≤V := norm_nonneg _
  have ceil_lt := Nat.ceil_lt_add_one vp
  have h' : (i:ℝ) ≤ (⌈V⌉₊:ℕ) := by exact_mod_cast h
  have hs : (i:ℝ)≤2*V := by linarith only [h',ceil_lt,two]
  have prod : ‖1-phaseBase x‖*V≤2 := calc
    _ = ‖phaseAt x a-phaseAt x b‖ := by
      change ‖1-phaseBase x‖*‖∑ m ∈ Ico a b, phaseAt x m‖ = _
      rw [←norm_mul,phase_geom_identity x hab]
    _ ≤ ‖phaseAt x a‖+‖phaseAt x b‖ := norm_sub_le _ _
    _ = _ := by rw [phaseAt_norm,phaseAt_norm]; norm_num
  apply (le_div_iff₀ ip).mpr
  nlinarith only [prod,mul_le_mul_of_nonneg_right (chord x) vp,
    mul_le_mul_of_nonneg_left hs (abs_nonneg (x-(nearest x:ℝ)))]

def layer (i : ℕ) (x : ℝ) : ℝ := if i≤⌈x⌉₊ then 1 else 0

theorem layer_nonneg (i : ℕ) (x : ℝ) : 0≤layer i x := by unfold layer; split <;> norm_num

/-- Layer counting costs at most one unit of rounding. The upper endpoint
of the integer sum stays at the actual interval length bound. -/
theorem layer_cover {a b M : ℕ} (hab : a≤b) (cap : b-a≤M) (x : ℝ) :
    ‖shortSum (Ico a b) x‖ ≤ ∑ i ∈ Icc 1 M, layer i ‖shortSum (Ico a b) x‖ := by
  let V := ‖shortSum (Ico a b) x‖
  have bound : V≤M := (phase_sum_length_bound x hab).trans (by exact_mod_cast cap)
  have c : ⌈V⌉₊≤M := Nat.ceil_le.mpr bound
  have cut : (Icc 1 M).filter (fun i => i≤⌈V⌉₊)=Icc 1 ⌈V⌉₊ := by
    ext i
    simp only [mem_filter,mem_Icc]
    omega
  change V≤∑ i ∈ Icc 1 M, layer i V
  simp only [layer,←sum_filter,cut,sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,
    Nat.add_sub_cancel]
  exact Nat.le_ceil V

end
end ImbalancedChen.Part3.OriginalShortIntervalLayers20261113
