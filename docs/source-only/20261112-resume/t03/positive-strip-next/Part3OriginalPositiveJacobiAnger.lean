import ImbalancedChen.Part3ActualPositiveHolomorphicWeights
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! The odd Jacobi--Anger coefficients are the original integer Gamma-series J's. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveJacobiAnger20261112

open Complex
open scoped BigOperators
open ActualPositiveHolomorphicWeights20261112 (intJ)
open ActualGeneralJBesselSourceOnly (generalJ generalJTerm generalJ_hasSum)
open GeneralComplexISeriesSourceOnly (generalICoeff)

def oddOrder (j : ℕ) := 2*j+1

private def triangles : ℤ × ℕ ≃ ℕ × ℕ where
  toFun t := match t.1 with
    | .ofNat n => (t.2+n,t.2)
    | .negSucc n => (t.2,t.2+(n+1))
  invFun p := if p.2≤p.1 then (.ofNat (p.1-p.2),p.2) else (.negSucc (p.2-p.1-1),p.1)
  left_inv := by
    rintro ⟨k,a⟩
    cases k with
    | ofNat n => simp
    | negSucc n => simp [show ¬a+(n+1)≤a by omega]
  right_inv := by
    rintro ⟨a,b⟩
    split_ifs with h <;> apply Prod.ext <;> dsimp <;> omega

private def taylor (x : ℂ) (k : ℕ) := x^k/(k.factorial:ℂ)

private theorem taylor_sum (x : ℂ) : HasSum (taylor x) (Complex.exp x) := by
  simpa only [taylor,Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp x

private theorem taylor_norm (x : ℂ) : Summable fun n => ‖taylor x n‖ := by
  simpa only [taylor,norm_div,norm_pow,Complex.norm_natCast] using Real.summable_pow_div_factorial ‖x‖

private def term (q : ℝ) (n k : ℕ) : ℂ :=
  (-1:ℂ)^k*((q/2:ℝ):ℂ)^(n+2*k)/((k.factorial:ℂ)*((k+n).factorial:ℂ))

private theorem term_sum (q : ℝ) (n : ℕ) : HasSum (term q n) (intJ n q) := by
  apply (generalJ_hasSum (nu := (n:ℂ)) (by simp) q).congr_fun
  intro k
  rw [generalJTerm,generalICoeff,← Nat.cast_add,Complex.Gamma_nat_eq_factorial]
  simp only [term,Complex.cpow_natCast,pow_add,div_eq_mul_inv]
  ring

private def mode (q : ℝ) (Z : ℂ) : ℤ → ℂ
  | .ofNat n => intJ n q*Z^n
  | .negSucc n => intJ (n+1) q*(-Z⁻¹)^(n+1)

private theorem leading (q : ℝ) {Z : ℂ} (hz : Z≠0) (n k : ℕ) :
    taylor (((q/2:ℝ):ℂ)*Z) (k+n) * taylor (-((q/2:ℝ):ℂ)*Z⁻¹) k =
      term q n k*Z^n := by
  simp only [taylor,term,pow_add,mul_pow,neg_pow,inv_pow,pow_mul]
  field_simp [hz] <;> ring

private theorem trailing (q : ℝ) {Z : ℂ} (hz : Z≠0) (n k : ℕ) :
    taylor (((q/2:ℝ):ℂ)*Z) k * taylor (-((q/2:ℝ):ℂ)*Z⁻¹) (k+n) =
      term q n k*(-Z⁻¹)^n := by
  simp only [taylor,term,pow_add,mul_pow,neg_pow,inv_pow,pow_mul]
  field_simp [hz] <;> ring

private theorem integer_expansion (q : ℝ) {Z : ℂ} (hz : Z≠0) :
    HasSum (mode q Z) (Complex.exp (((q/2:ℝ):ℂ)*(Z-Z⁻¹))) := by
  let a := ((q/2:ℝ):ℂ)*Z
  let b := -((q/2:ℝ):ℂ)*Z⁻¹
  have s := summable_mul_of_summable_norm (taylor_norm a) (taylor_norm b)
  have hs : HasSum (fun k : ℕ×ℕ => taylor a k.1*taylor b k.2)
      (Complex.exp (((q/2:ℝ):ℂ)*(Z-Z⁻¹))) := by
    apply s.hasSum_iff.mpr
    rw [← tsum_mul_tsum_of_summable_norm (taylor_norm a) (taylor_norm b),
      (taylor_sum a).tsum_eq,(taylor_sum b).tsum_eq,←Complex.exp_add]
    congr 1; dsimp [a,b]; ring
  apply (triangles.hasSum_iff.mpr hs).prod_fiberwise
  intro i
  cases i with
  | ofNat n =>
    exact ((term_sum q n).mul_right (Z^n)).congr_fun (fun k => leading q hz n k)
  | negSucc n =>
    exact ((term_sum q (n+1)).mul_right ((-Z⁻¹)^(n+1))).congr_fun
      (fun k => trailing q hz (n+1) k)

private theorem natural_expansion (q : ℝ) {Z : ℂ} (hz : Z≠0) :
    HasSum (fun n : ℕ => intJ n q*(Z^n+(-Z⁻¹)^n))
      (Complex.exp (((q/2:ℝ):ℂ)*(Z-Z⁻¹))+intJ 0 q) := by
  have h := (integer_expansion q hz).nat_add_neg
  simp only [mode,pow_zero,mul_one] at h
  apply h.congr_fun
  intro n
  cases n <;> simp [mode,mul_add]

/-- The odd part, with both Laurent tails and the diagonal counted once. -/
theorem generating (q : ℝ) {Z : ℂ} (hz : Z≠0) :
    HasSum (fun j : ℕ => intJ (oddOrder j) q*(Z^(oddOrder j)-(Z⁻¹)^(oddOrder j)))
      ((Complex.exp (((q/2:ℝ):ℂ)*(Z-Z⁻¹))-Complex.exp (-(((q/2:ℝ):ℂ)*(Z-Z⁻¹))))/2) := by
  have H := ((natural_expansion q hz).sub (natural_expansion q (neg_ne_zero.mpr hz))).div_const 2
  replace H := (Nat.divModEquiv 2).symm.hasSum_iff.mpr H
  dsimp [Function.comp_def] at H
  simp_rw [←mul_comm 2 _] at H
  have e : ((q/2:ℝ):ℂ)*(-Z-(-Z)⁻¹) = -(((q/2:ℝ):ℂ)*(Z-Z⁻¹)) := by rw [inv_neg]; ring
  rw [e,show ∀ a b c : ℂ,(a+c)-(b+c)=a-b from fun _ _ _ => by ring] at H
  apply H.prod_fiberwise
  intro j
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero,Fin.val_one,add_zero,oddOrder,pow_succ,pow_mul,neg_sq,
    inv_neg,neg_neg]
  ring

private theorem Iodd (j : ℕ) : Complex.I^(oddOrder j)=(-1:ℂ)^j*I := by
  rw [oddOrder,pow_succ,pow_mul,I_sq]

theorem sin_cosh (q : ℝ) (z : ℂ) :
    HasSum (fun j : ℕ => 2*(-1:ℂ)^j*intJ (oddOrder j) q*Complex.cosh ((oddOrder j:ℂ)*z))
      (Complex.sin ((q:ℂ)*Complex.cosh z)) := by
  let Z := Complex.I*Complex.exp z
  have hz : Z≠0 := mul_ne_zero I_ne_zero (Complex.exp_ne_zero _)
  have inv : Z⁻¹=(-I)*Complex.exp (-z) := by simp [Z,Complex.exp_neg,mul_comm]
  have e : ((q/2:ℝ):ℂ)*(Z-Z⁻¹)=((q:ℂ)*Complex.cosh z)*I := by
    rw [inv]; simp only [Z,Complex.cosh,Complex.ofReal_div,Complex.ofReal_ofNat]; ring
  have H := (generating q hz).mul_right (-I)
  rw [e,show (Complex.exp ((q*Complex.cosh z)*I)-Complex.exp (-((q*Complex.cosh z)*I)))/2*(-I)=
    Complex.sin ((q:ℂ)*Complex.cosh z) by rw [Complex.sin,neg_mul]; ring] at H
  apply H.congr_fun
  intro j
  have np : (-I)^(oddOrder j)=-((-1:ℂ)^j*I) := by
    rw [oddOrder,pow_succ,pow_mul,neg_sq,I_sq]; ring
  have p : Z^(oddOrder j)=((-1:ℂ)^j*I)*Complex.exp ((oddOrder j:ℂ)*z) := by
    rw [Z,mul_pow,Iodd,Complex.exp_nat_mul]
  have m : (Z⁻¹)^(oddOrder j)=-((-1:ℂ)^j*I)*Complex.exp (-((oddOrder j:ℂ)*z)) := by
    rw [inv,mul_pow,np,←Complex.exp_nat_mul,mul_neg]
  rw [p,m,Complex.cosh]
  ring_nf <;> simp [Complex.I_sq] <;> ring


theorem sin_sin (q t : ℝ) :
    HasSum (fun j : ℕ => 2*intJ (oddOrder j) q*(Real.sin ((oddOrder j:ℝ)*t):ℂ))
      (Real.sin (q*Real.sin t):ℂ) := by
  let Z := Complex.exp ((t:ℂ)*I)
  have hz : Z≠0 := Complex.exp_ne_zero _
  have inv : Z⁻¹=Complex.exp (-((t:ℂ)*I)) := (Complex.exp_neg _).symm
  have e : ((q/2:ℝ):ℂ)*(Z-Z⁻¹)=((q*Real.sin t:ℝ):ℂ)*I := by
    rw [inv]; dsimp only [Z]
    rw [Complex.ofReal_mul,Complex.ofReal_sin,Complex.sin]
    push_cast; ring_nf; simp [Complex.I_sq]
  have H := (generating q hz).mul_right (-I)
  rw [e,show (Complex.exp (((q*Real.sin t:ℝ):ℂ)*I)-Complex.exp (-(((q*Real.sin t:ℝ):ℂ)*I)))/2*(-I)=
    (Real.sin (q*Real.sin t):ℂ) by rw [Complex.ofReal_sin,Complex.sin,neg_mul]; ring] at H
  apply H.congr_fun
  intro j
  symm
  let a : ℂ := ((oddOrder j:ℝ)*t:ℝ)
  have p : Z^(oddOrder j)=Complex.exp (a*I) := by
    rw [Z,←Complex.exp_nat_mul]
    congr 1; dsimp only [a]; push_cast; ring
  have m : (Z⁻¹)^(oddOrder j)=Complex.exp (-(a*I)) := by
    rw [inv,←Complex.exp_nat_mul]
    congr 1; dsimp only [a]; push_cast; ring
  rw [p,m,Complex.ofReal_sin,Complex.sin,neg_mul]
  change _=2*intJ (oddOrder j) q*((Complex.exp (-(a*I))-Complex.exp (a*I))*I/2)
  ring

end ImbalancedChen.Part3.OriginalPositiveJacobiAnger20261112
end
