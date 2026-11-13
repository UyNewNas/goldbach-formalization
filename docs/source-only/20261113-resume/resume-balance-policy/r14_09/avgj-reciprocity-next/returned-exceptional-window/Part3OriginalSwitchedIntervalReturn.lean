import ImbalancedChen.Part3OriginalSwitchedIntervalMellin
import ImbalancedChen.Part3OriginalSwitchedAdditiveWeight
import ImbalancedChen.Part3OriginalSwitchedNativePrefixEnergy

/-! The actual finite complementary return on a common interval.
The family is cut only by its literal complementary order. -/
namespace ImbalancedChen.Part3.OriginalSwitchedIntervalReturn20261113
noncomputable section
open Finset MeasureTheory Complex
open scoped BigOperators Classical
open OriginalSwitchedMellinRows20261113 (nativeRow density density_integrable wave wave_norm twistedRow row_norm_le)
open OriginalSwitchedIntervalMellin20261113 (tested carrier marked interval_mellin)
open OriginalSwitchedAdditiveWeight20261113 (native_additive)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)

def squares (S : Finset ℕ) (v : ℕ→ℂ) (t : ℝ) :=
  ‖twistedRow S v (-(t/2))‖^2+‖twistedRow S v (t/2)‖^2

private theorem squares_nonneg (S : Finset ℕ) (v : ℕ→ℂ) (t : ℝ) : 0≤squares S v t :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem squares_integrable (S : Finset ℕ) (v : ℕ→ℂ) :
    Integrable (fun t : ℝ => ‖density t‖*squares S v t) := by
  let L := ∑ m∈S,‖v m‖
  apply density_integrable.norm.mul_bdd (c:=2*L^2)
  · have cont : Continuous (squares S v) := by unfold squares twistedRow wave;fun_prop
    exact cont.aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_of_nonneg (squares_nonneg S v t)]
    have minus := pow_le_pow_left₀ (norm_nonneg _) (row_norm_le S v (-(t/2))) 2
    have plus := pow_le_pow_left₀ (norm_nonneg _) (row_norm_le S v (t/2)) 2
    dsimp only [squares,L]
    linarith only [minus,plus]

private theorem single_price (z : ℕ+) (i : ↥(exceptional z)) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q)
    (ω : ℝ) (S : Finset ℕ) (pos : ∀ m∈S,0<m) {W : ℝ} (wp : 0≤W)
    (ceiling : ∀ t,‖tested z i Y t‖≤W) :
    ‖marked z i Y Q ω S‖≤((2*Real.pi)⁻¹/2)*W*
        ∫ t : ℝ,‖density t‖*squares S (nativeRow z i.val ω) t := by
  let v := nativeRow z i.val ω
  let r (t : ℝ) := star (twistedRow S v (-(t/2)))*twistedRow S v (t/2)
  let P := (2*Real.pi)⁻¹
  have pp : 0≤P := by dsimp only [P];positivity
  have major (t : ℝ) : ‖carrier z i Y Q t*r t‖≤(W/2)*(‖density t‖*squares S v t) := by
    let a := ‖twistedRow S v (-(t/2))‖
    let b := ‖twistedRow S v (t/2)‖
    have ar : a*b≤(a^2+b^2)/2 := by nlinarith only [sq_nonneg (a-b)]
    have p := mul_le_mul (ceiling t) ar (mul_nonneg (norm_nonneg _) (norm_nonneg _)) wp
    have q := mul_le_mul_of_nonneg_left p (norm_nonneg (density t))
    simp only [carrier,r,norm_mul,wave_norm,one_mul,norm_star]
    dsimp only [squares]
    change ‖density t‖*‖tested z i Y t‖*(a*b)≤W/2*(‖density t‖*(a^2+b^2))
    convert q using 1 <;> ring
  have bound := norm_integral_le_of_norm_le ((squares_integrable S v).const_mul (W/2)) (ae_of_all _ major)
  rw [integral_const_mul] at bound
  rw [interval_mellin z i yp qp ω S pos,Complex.real_smul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg pp]
  exact (mul_le_mul_of_nonneg_left bound pp).trans_eq (by dsimp only [P,v];ring)

def retained (T : ℝ) (z : ℕ+) := (univ : Finset ↥(exceptional z)).filter (fun i => tau z i.val≤T)

def bill (L : Finset ℕ+) (T Y Q ω : ℝ) (a b : ℕ) :=
  ∑ z ∈ L,∑ i ∈ retained T z,‖marked z i Y Q ω (Ico a b)‖

def both (L : Finset ℕ+) (X ω : ℝ) (a b : ℕ) (t : ℝ) :=
  intervalEnergy L X ω a b (-(t/2))+intervalEnergy L X ω a b (t/2)

private theorem weighted (L : Finset ℕ+) (X ω : ℝ) (a b : ℕ) (t : ℝ) :
    (∑ z ∈ L,∑ i : ↥(exceptional z),X^(tau z i.val)*squares (Ico a b) (nativeRow z i.val ω) t)
      =both L X ω a b t := by
  simp only [squares,both,intervalEnergy,mul_add,Finset.sum_add_distrib]

theorem returned {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ C Y₀ : ℝ,0<C ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ Q : ℝ,0<Q → ∀ (L : Finset ℕ+) (ω : ℝ) (a b : ℕ),0<a →
      bill L T Y Q ω a b≤C*∫ t : ℝ,‖density t‖*(both L Y ω a b t+Y^ε*both L 1 ω a b t) := by
  obtain ⟨K,X,kp,x1,H⟩ := native_additive tp t1 ep
  let P := (2*Real.pi)⁻¹/2
  have pp : 0<P := by dsimp only [P];positivity
  refine ⟨P*K,X,mul_pos pp kp,x1,fun Y hy Q qp L ω a b ap => ?_⟩
  have yp := zero_lt_one.trans_le (x1.trans hy)
  let S := Ico a b
  let v (z : ℕ+) (i : ↥(exceptional z)) := nativeRow z i.val ω
  let W (z : ℕ+) (i : ↥(exceptional z)) := Y^(tau z i.val)+Y^ε
  let f (z : ℕ+) (i : ↥(exceptional z)) (t : ℝ) := W z i*(‖density t‖*squares S (v z i) t)
  let F (z : ℕ+) (i : ↥(exceptional z)) := ∫ t,f z i t
  have wp (z : ℕ+) (i : ↥(exceptional z)) : 0≤W z i := add_nonneg (Real.rpow_nonneg yp.le _) (Real.rpow_nonneg yp.le _)
  have fi (z : ℕ+) (i : ↥(exceptional z)) : Integrable (f z i) := (squares_integrable S (v z i)).const_mul _
  have fp (z : ℕ+) (i : ↥(exceptional z)) : 0≤F z i := integral_nonneg (fun t =>
    mul_nonneg (wp z i) (mul_nonneg (norm_nonneg _) (squares_nonneg _ _ _)))
  have price (z : ℕ+) (i : ↥(exceptional z)) (hi : i∈retained T z) :
      ‖marked z i Y Q ω S‖≤(P*K)*F z i := by
    have cap := (Finset.mem_filter.mp hi).2
    have q := single_price z i yp qp ω S (fun m hm => ap.trans_le (mem_Ico.mp hm).1)
      (mul_nonneg kp.le (wp z i)) (H Y hy z i cap)
    dsimp only [F,f]
    rw [integral_const_mul]
    exact q.trans_eq (by dsimp only [P,v,S,W];ring)
  have per (z : ℕ+) : (∑ i∈retained T z,‖marked z i Y Q ω S‖)≤
      (P*K)*∑ i : ↥(exceptional z),F z i := by
    have p := sum_le_sum (s:=retained T z) (fun i hi => price z i hi)
    rw [←Finset.mul_sum] at p
    exact p.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun i _ _ => fp z i)) (mul_pos pp kp).le)
  have sum := Finset.sum_le_sum (s:=L) (fun z _ => per z)
  rw [←Finset.mul_sum] at sum
  apply sum.trans_eq
  congr 1
  have split (t : ℝ) : (∑ z∈L,∑ i : ↥(exceptional z),f z i t)=
      ‖density t‖*(both L Y ω a b t+Y^ε*both L 1 ω a b t) := by
    rw [←weighted L Y ω a b t,←weighted L 1 ω a b t]
    rw [mul_add]
    simp only [Real.one_rpow,one_mul,Finset.mul_sum,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro i _
    dsimp only [f,W,S,v];ring
  calc
    _ = ∫ t,∑ z∈L,∑ i : ↥(exceptional z),f z i t := by
      rw [integral_finsetSum L (fun z _ => integrable_finsetSum univ (fun i _ => fi z i))]
      apply sum_congr rfl
      intro z _
      exact (integral_finsetSum univ (fun i _ => fi z i)).symm
    _ = _ := integral_congr_ae (ae_of_all _ split)

end
end ImbalancedChen.Part3.OriginalSwitchedIntervalReturn20261113
