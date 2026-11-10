import ImbalancedChen.Part3ActualYoungCuspCoefficients
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Invert the genuine original character dilation matrix, including
imprimitive occupied levels. The real-part condition is Re(s)>0, so no
division at the central spectral parameter is needed. The local determinant
factors are 1-chi(l)^2 l^(-2s) at each prime dividing a divisor of L. -/
namespace ImbalancedChen.Part3.ActualYoungDilationInverse20261110

noncomputable section
open Complex Matrix ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction
open ActualYoungCuspCoefficients20261110

abbrev Div (L : ℕ) := {d : ℕ // d ∈ L.divisors}

theorem twist_one {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    twist χ s 1 = 1 := by simp [twist,posPower]

theorem twist_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) : twist χ s (a*b) = twist χ s a*twist χ s b := by
  simp only [twist,Nat.cast_mul,map_mul,posPower_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]
  ring

private def squared {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (twist χ s n)^2,by simp⟩

private theorem squared_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (a b : ℕ) :
    squared χ s (a*b) = squared χ s a*squared χ s b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp [squared,ha,hb,mul_ne_zero ha hb,twist_mul χ s (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb),mul_pow]

private theorem squared_mult {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (squared χ s).IsMultiplicative :=
  ⟨by simp [squared,twist_one],fun {a b} _ => squared_mul χ s a b⟩

private theorem squared_pow {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (p k : ℕ) :
    squared χ s (p^k) = (squared χ s p)^k := by
  induction k with
  | zero => simp [squared,twist_one]
  | succ k ih => rw [pow_succ,squared_mul,ih,pow_succ]

def eulerDiagonal {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else ∏ p ∈ n.primeFactors,(1-squared χ s p),by simp⟩

private theorem diagonal_mult {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (eulerDiagonal χ s).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [eulerDiagonal],?_⟩
  intro a b ha hb hc
  simp [eulerDiagonal,ha,hb,mul_ne_zero ha hb,Nat.primeFactors_mul ha hb,
    Finset.prod_union hc.disjoint_primeFactors]

private theorem geometric_identity (x : ℂ) (k : ℕ) :
    ∑ j ∈ Finset.range (k+1), (if j = 0 then 1 else 1-x)*x^(k-j) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h : (∑ j ∈ Finset.range (k+1), (if j = 0 then 1 else 1-x)*x^(k+1-j)) =
        x*(∑ j ∈ Finset.range (k+1), (if j = 0 then 1 else 1-x)*x^(k-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hle := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [show k+1-j = k-j+1 by omega,pow_succ]
      ring
    rw [h,ih]
    simp

private theorem convolution {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    eulerDiagonal χ s*squared χ s = (ArithmeticFunction.zeta : ArithmeticFunction ℂ) := by
  let D := eulerDiagonal χ s
  let W := squared χ s
  have hmult := (diagonal_mult χ s).mul (squared_mult χ s)
  ext n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [eulerDiagonal,squared,twist_one]
  | prime_pow p k hp hk =>
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal fun a b => D a*W b,
      Nat.sum_divisors_prime_pow hp]
    have h : (∑ j ∈ Finset.range (k+1),D (p^j)*W (p^k/p^j)) =
        ∑ j ∈ Finset.range (k+1),(if j=0 then 1 else 1-W p)*(W p)^(k-j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hle := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [Nat.pow_div hle hp.pos,squared_pow]
      by_cases hj0 : j=0
      · simp [D,eulerDiagonal,hj0]
      · simp [D,eulerDiagonal,show p^j ≠ 0 from pow_ne_zero _ hp.ne_zero,
          Nat.primeFactors_pow p hj0,hp.primeFactors,hj0,W]
    rw [h,geometric_identity]
    simp [hp.ne_zero]
  | coprime a b ha hb hc ia ib =>
    rw [hmult.map_mul_of_coprime hc,ia,ib,
      (ArithmeticFunction.isMultiplicative_zeta.natCast (R := ℂ)).map_mul_of_coprime hc]

private theorem divide_chain {d g n : ℕ} (hd : 0 < d) (hdg : d ∣ g) (hgn : g ∣ n) :
    n/d = (n/g)*(g/d) := by
  apply Nat.eq_of_mul_eq_mul_left hd
  rw [Nat.mul_div_cancel' (hdg.trans hgn),mul_left_comm,Nat.mul_div_cancel' hdg,Nat.div_mul_cancel hgn]

/-- Actual local-to-divisor identity behind the congruence decomposition. -/
theorem divisorKernel_factor {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    divisorKernel χ s a b = ∑ d ∈ (a.gcd b).divisors,
      twist χ s (a/d)*eulerDiagonal χ s d*twist χ s (b/d) := by
  let g := a.gcd b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ ha
  have hga := Nat.gcd_dvd_left a b
  have hgb := Nat.gcd_dvd_right a b
  have hA := Nat.div_pos (Nat.le_of_dvd ha hga) hg
  have hB := Nat.div_pos (Nat.le_of_dvd hb hgb) hg
  have H := congrArg (fun f : ArithmeticFunction ℂ => f g) (convolution χ s)
  change (eulerDiagonal χ s*squared χ s) g = _ at H
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal] at H
  have hconv : ∑ d ∈ g.divisors, eulerDiagonal χ s d*squared χ s (g/d) = 1 := by
    simpa [hg.ne'] using H
  calc
    _ = divisorKernel χ s a b*(∑ d ∈ g.divisors,eulerDiagonal χ s d*squared χ s (g/d)) := by rw [hconv,mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hD := (Nat.mem_divisors.mp hd).1
      have hdpos := Nat.pos_of_dvd_of_pos hD hg
      have hgd := Nat.div_pos (Nat.le_of_dvd hg hD) hdpos
      rw [divide_chain hdpos hD hga,divide_chain hdpos hD hgb,
        twist_mul χ s hA hgd,twist_mul χ s hB hgd]
      simp [divisorKernel,squared,hgd.ne',g] <;> ring

private theorem twist_prime_lt_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) : ‖twist χ s p‖ < 1 := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hneg : ((-s)*(Real.log (p : ℝ) : ℂ)).re < 0 := by
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hlog
  rw [twist,norm_mul,posPower,Complex.norm_exp]
  exact (mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)).trans_lt
    (Real.exp_lt_one_iff.mpr hneg)

theorem eulerDiagonal_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) (hn : n ≠ 0) : eulerDiagonal χ s n ≠ 0 := by
  classical
  change (if n = 0 then 0 else ∏ p ∈ n.primeFactors,(1-squared χ s p)) ≠ 0
  rw [if_neg hn,Finset.prod_ne_zero_iff]
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have ht := twist_prime_lt_one χ hs hprime
  have hsq : ‖squared χ s p‖ < 1 := by
    change ‖if p = 0 then (0 : ℂ) else (twist χ s p)^2‖ < 1
    rw [if_neg hprime.ne_zero,norm_pow]
    nlinarith [norm_nonneg (twist χ s p),mul_pos (sub_pos.mpr ht) (by positivity : 0 < 1+‖twist χ s p‖)]
  intro he
  rw [← sub_eq_zero.mp he,norm_one] at hsq
  exact lt_irrefl _ hsq

def kernelMatrix {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (L : ℕ) :
    Matrix (Div L) (Div L) ℂ := fun i j => divisorKernel χ s i.1 j.1

private def lowerMatrix {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (L : ℕ) :
    Matrix (Div L) (Div L) ℂ := fun i d => if d.1 ∣ i.1 then twist χ s (i.1/d.1) else 0

private theorem lower_det {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (L : ℕ) (hL : 0 < L) :
    (lowerMatrix χ s L).det = 1 := by
  have ht : (lowerMatrix χ s L).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.1 < j.1 := hij
    have hi : 0 < i.1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp i.2).1 hL
    exact if_neg (fun hh => (not_le_of_gt hlt) (Nat.le_of_dvd hi hh))
  rw [Matrix.det_of_lowerTriangular _ ht]
  apply Finset.prod_eq_one
  intro i _
  have hi : 0 < i.1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp i.2).1 hL
  simp [lowerMatrix,Nat.div_self hi,twist_one]

private theorem matrix_factor {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (L : ℕ) (hL : 0 < L) :
    kernelMatrix χ s L = lowerMatrix χ s L*Matrix.diagonal (fun d : Div L => eulerDiagonal χ s d.1)*
      (lowerMatrix χ s L).transpose := by
  classical
  ext i j
  let g := i.1.gcd j.1
  have hi := (Nat.mem_divisors.mp i.2).1
  have hj := (Nat.mem_divisors.mp j.2).1
  have h₁ := Nat.pos_of_dvd_of_pos hi hL
  have h₂ := Nat.pos_of_dvd_of_pos hj hL
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ h₁
  let F : ℕ → ℂ := fun d => twist χ s (i.1/d)*eulerDiagonal χ s d*twist χ s (j.1/d)
  have hfilter : L.divisors.filter (fun d => d ∣ g) = g.divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,hL.ne',hg.ne',and_true]
    exact ⟨And.right,fun hd => ⟨hd.trans ((Nat.gcd_dvd_left _ _).trans hi),hd⟩⟩
  change divisorKernel χ s i.1 j.1 = _
  rw [divisorKernel_factor χ s _ _ h₁ h₂,Matrix.mul_apply]
  change (∑ d ∈ g.divisors,F d) = _
  rw [← hfilter,Finset.sum_filter]
  calc
    _ = ∑ d : Div L, if d.1 ∣ g then F d.1 else 0 := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach L.divisors (fun d => if d ∣ g then F d else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply,lowerMatrix,F,g,Nat.dvd_gcd_iff]
      split_ifs <;> simp_all

/-- No prime factor in the actual finite matrix determinant vanishes in
the original critical strip Re(s)>0, for any composite L. -/
theorem kernel_det_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (L : ℕ) (hL : 0 < L) : (kernelMatrix χ s L).det ≠ 0 := by
  classical
  rw [matrix_factor χ s L hL,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    lower_det χ s L hL,Matrix.det_diagonal,one_mul,mul_one,Finset.prod_ne_zero_iff]
  intro d _
  exact eulerDiagonal_ne_zero χ hs d.1
    (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.2).1 hL).ne'

theorem original_dilation_matrix_inverse {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (L : ℕ) (hL : 0 < L) :
    (kernelMatrix χ s L)⁻¹*kernelMatrix χ s L = 1 ∧
    kernelMatrix χ s L*(kernelMatrix χ s L)⁻¹ = 1 := by
  have hu : IsUnit (kernelMatrix χ s L).det := isUnit_iff_ne_zero.mpr (kernel_det_ne_zero χ hs L hL)
  exact ⟨Matrix.nonsing_inv_mul _ hu,Matrix.mul_nonsing_inv _ hu⟩

end
end ImbalancedChen.Part3.ActualYoungDilationInverse20261110
