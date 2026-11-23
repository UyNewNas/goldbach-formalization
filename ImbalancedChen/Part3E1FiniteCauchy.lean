import ImbalancedChen.Part3E1ReciprocalPhase
import ImbalancedChen.Part3ComplexDispersion

/-!
# The finite E1 source and its weighted Cauchy inequality

This is the finite sum (E1) of `lichtman-E1-completion-explicit-20261010.txt`.
The two factor slots have the same support and their own primitive gates.
The first slot carries the signed nonzero Fourier sum. The second slot
carries the exact inverse totient.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry (reciprocalPhase)

namespace E1Finite

/-- The integer support restricted to factors coprime to the signed residue. -/
def primitive (a : ℤ) (S : Finset ℕ) : Finset ℕ := S.filter (fun s => s.Coprime a.natAbs)

private def phase (l n : ℕ) (A : ℤ) : ℂ :=
  if hl : l ≠ 0 then
    letI : NeZero l := ⟨hl⟩
    reciprocalPhase l A (n : ZMod l)
  else 0

/-- The local phase includes the original condition `(n,qr)=1`. -/
def leftPhase (q r n : ℕ) (a h : ℤ) : ℂ := phase (q * r) n (a * h)

theorem leftPhase_eq_reciprocalPhase (q r n : ℕ) (a h : ℤ) [NeZero (q * r)] :
    leftPhase q r n a h = reciprocalPhase (q * r) (a * h) (n : ZMod (q * r)) := by
  unfold leftPhase phase
  rw [dif_pos (NeZero.ne (q * r))]

/-- The first-slot coefficient retains its Fourier argument and reciprocal
modulus weight and is independent of the variable that is completed. -/
def leftAmplitude (M : ℝ) (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ)
    (q r : ℕ) (h : ℤ) : ℂ :=
  lambda q r * ψhat ((h : ℝ) * M / ((q * r : ℕ) : ℝ)) / ((q * r : ℕ) : ℂ)

def leftTerm (M : ℝ) (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (a : ℤ)
    (q r n : ℕ) (h : ℤ) : ℂ :=
  leftAmplitude M ψhat lambda q r h * leftPhase q r n a h

/-- The second-slot term with its primitive gate and exact mean. -/
def rightTerm (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ) (q s n' : ℕ) : ℂ :=
  if n'.Coprime (q * s) then star (lambda q s) * star (alpha n') / (q * s).totient else 0

/-- The original uncontracted E1 source, ordered by the outer Cauchy cells. -/
def source (Q R N : Finset ℕ) (H : Finset ℤ) (a : ℤ) (M : ℝ)
    (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ) : ℂ :=
  ∑ q ∈ primitive a Q, ∑ n ∈ N, ∑ s ∈ primitive a R, ∑ n' ∈ N,
    ∑ r ∈ primitive a R, ∑ h ∈ H,
      if n'.Coprime (q * s) then
        lambda q r * star (lambda q s) * alpha n * star (alpha n') /
          (((q * s).totient : ℂ) * ((q * r : ℕ) : ℂ)) *
          ψhat ((h : ℝ) * M / ((q * r : ℕ) : ℝ)) * leftPhase q r n a h
      else 0

def leftRow (R : Finset ℕ) (H : Finset ℤ) (a : ℤ) (M : ℝ)
    (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (q n : ℕ) : ℂ :=
  ∑ r ∈ primitive a R, ∑ h ∈ H, leftTerm M ψhat lambda a q r n h

def rightRow (R N : Finset ℕ) (a : ℤ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ)
    (q : ℕ) : ℂ :=
  ∑ s ∈ primitive a R, ∑ n' ∈ N, rightTerm lambda alpha q s n'

/-- The entire unrestricted `s,n'` sum factors out of the first-slot row.
Its primitive gate and inverse totient stay inside that sum. -/
theorem source_eq_rows (Q R N : Finset ℕ) (H : Finset ℤ) (a : ℤ) (M : ℝ)
    (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ) :
    source Q R N H a M ψhat lambda alpha =
      ∑ q ∈ primitive a Q, ∑ n ∈ N,
        (rightRow R N a lambda alpha q * alpha n) * leftRow R H a M ψhat lambda q n := by
  unfold source rightRow leftRow
  simp_rw [sum_mul]
  simp_rw [mul_sum]
  refine sum_congr rfl (fun q _ => sum_congr rfl (fun n _ => ?_))
  refine sum_congr rfl (fun s _ => sum_congr rfl (fun n' _ => ?_))
  refine sum_congr rfl (fun r _ => sum_congr rfl (fun h _ => ?_))
  unfold leftTerm leftAmplitude rightTerm
  by_cases hp : n'.Coprime (q * s)
  · simp only [if_pos hp, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  · simp only [if_neg hp, zero_mul]

/-- The literal right row can be paid by the sum of inverse totients over
its full support, including the primitive filter on the second variable. -/
theorem norm_rightRow_le (R N : Finset ℕ) (a : ℤ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ)
    (q : ℕ) (hlambda : ∀ s ∈ primitive a R, ‖lambda q s‖ ≤ 1)
    (halpha : ∀ n ∈ N, ‖alpha n‖ ≤ 1) :
    ‖rightRow R N a lambda alpha q‖ ≤
      ∑ s ∈ primitive a R, ∑ n ∈ N,
        if n.Coprime (q * s) then ((q * s).totient : ℝ)⁻¹ else 0 := by
  unfold rightRow
  refine (norm_sum_le _ _).trans (sum_le_sum (fun s hs => ?_))
  refine (norm_sum_le _ _).trans (sum_le_sum (fun n hn => ?_))
  unfold rightTerm
  by_cases hp : n.Coprime (q * s)
  · simp only [if_pos hp, norm_div, norm_mul, norm_star, Complex.norm_natCast]
    rw [← one_div]
    gcongr
    simpa using mul_le_mul (hlambda s hs) (halpha n hn) (norm_nonneg _) zero_le_one
  · simp only [if_neg hp, norm_zero, le_refl]

/-- Weighted Cauchy for the original finite E1 sum, with a common sampled
majorant of the first variable. Its mass is the exact squared outer weight. -/
theorem source_norm_sq_le_weighted (Q R N S : Finset ℕ) (H : Finset ℤ)
    (a : ℤ) (M : ℝ) (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ)
    (w : ℕ → ℝ) (hNS : N ⊆ S) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hmajorant : ∀ n ∈ N, 1 ≤ w n) :
    ‖source Q R N H a M ψhat lambda alpha‖ ^ 2 ≤
      (∑ q ∈ primitive a Q, ∑ n ∈ N, ‖rightRow R N a lambda alpha q * alpha n‖ ^ 2) *
      (∑ q ∈ primitive a Q, ∑ n ∈ S, w n * ‖leftRow R H a M ψhat lambda q n‖ ^ 2) := by
  rw [source_eq_rows]
  let outer : ℕ × ℕ → ℂ := fun qn => rightRow R N a lambda alpha qn.1 * alpha qn.2
  let inner : ℕ × ℕ → ℂ := fun qn => leftRow R H a M ψhat lambda qn.1 qn.2
  rw [← sum_product (f := fun qn => outer qn * inner qn),
    ← sum_product (f := fun qn => ‖outer qn‖ ^ 2)]
  have hinner : (∑ p ∈ primitive a Q ×ˢ N, ‖inner p‖ ^ 2) ≤
      ∑ q ∈ primitive a Q, ∑ n ∈ S, w n * ‖leftRow R H a M ψhat lambda q n‖ ^ 2 := by
    rw [sum_product]
    apply sum_le_sum
    intro q _
    calc
      _ ≤ ∑ n ∈ N, w n * ‖inner (q, n)‖ ^ 2 :=
        sum_le_sum (fun n hn => le_mul_of_one_le_left (sq_nonneg _) (hmajorant n hn))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hNS (fun n hn _ =>
        mul_nonneg (hw n hn) (sq_nonneg _))
  exact (complex_finset_cauchy_norm_sq (primitive a Q ×ˢ N) outer inner).trans
    (mul_le_mul_of_nonneg_left hinner (sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The common character on the signed determinant and the original n gate. -/
def completedPhase (q r r' n : ℕ) (a h h' : ℤ) : ℂ :=
  phase (q * r * r') n (a * e1Determinant h h' r r')

theorem completedPhase_eq_reciprocalPhase (q r r' n : ℕ) (a h h' : ℤ)
    [NeZero (q * r * r')] :
    completedPhase q r r' n a h h' =
      reciprocalPhase (q * r * r') (a * e1Determinant h h' r r') (n : ZMod (q * r * r')) := by
  unfold completedPhase phase
  rw [dif_pos (NeZero.ne (q * r * r'))]

theorem leftPhase_mul_star (q r r' n : ℕ) (a h h' : ℤ) :
    leftPhase q r n a h * star (leftPhase q r' n a h') = completedPhase q r r' n a h h' := by
  by_cases hq : q = 0
  · simp [hq, leftPhase, completedPhase, phase]
  by_cases hr : r = 0
  · simp [hr, leftPhase, completedPhase, phase]
  by_cases hr' : r' = 0
  · simp [hr', leftPhase, completedPhase, phase]
  let _ : NeZero q := ⟨hq⟩
  let _ : NeZero r := ⟨hr⟩
  let _ : NeZero r' := ⟨hr'⟩
  rw [leftPhase_eq_reciprocalPhase, leftPhase_eq_reciprocalPhase,
    completedPhase_eq_reciprocalPhase, e1ReciprocalPhase_mul_conj]

/-- The sample on the common modulus, with the same n support and weight. -/
def completedTerm (S : Finset ℕ) (w : ℕ → ℝ) (q r r' : ℕ) (a h h' : ℤ) : ℂ :=
  ∑ n ∈ S, (w n : ℂ) * completedPhase q r r' n a h h'

/-- The unweighted completion mass appearing after the triangle inequality. -/
def completedMass (Q R S : Finset ℕ) (H : Finset ℤ) (a : ℤ) (w : ℕ → ℝ) : ℝ :=
  ∑ q ∈ primitive a Q, ∑ r ∈ primitive a R, ∑ r' ∈ primitive a R,
    ∑ h ∈ H, ∑ h' ∈ H, ‖completedTerm S w q r r' a h h'‖

/-- Expansion of the weighted square keeps both ordered Fourier labels
and puts the sampled weight into the actual completed phase sum. -/
theorem leftRow_weighted_sq_eq (R S : Finset ℕ) (H : Finset ℤ) (a : ℤ) (M : ℝ)
    (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (q : ℕ) (w : ℕ → ℝ) :
    ((∑ n ∈ S, w n * ‖leftRow R H a M ψhat lambda q n‖ ^ 2 : ℝ) : ℂ) =
      ∑ u ∈ primitive a R ×ˢ H, ∑ v ∈ primitive a R ×ˢ H,
        (leftAmplitude M ψhat lambda q u.1 u.2 * star (leftAmplitude M ψhat lambda q v.1 v.2)) *
          completedTerm S w q u.1 v.1 a u.2 v.2 := by
  let I := primitive a R ×ˢ H
  let L (n : ℕ) (u : ℕ × ℤ) := leftTerm M ψhat lambda a q u.1 n u.2
  have hrow (n : ℕ) : leftRow R H a M ψhat lambda q n = ∑ u ∈ I, L n u := by
    exact (sum_product (primitive a R) H (L n)).symm
  unfold completedTerm
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul]
  simp_rw [hrow, complex_norm_sq_sum_eq_double_star, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro n _
  unfold L leftTerm
  rw [star_mul, ← leftPhase_mul_star q u.1 v.1 n a u.2 v.2]
  ring

/-- The exact Cauchy square can now be bounded by the completion mass.
All original amplitude values remain inside the squared sum on the left. -/
theorem leftRows_weighted_sq_le (Q R S : Finset ℕ) (H : Finset ℤ) (a : ℤ) (M : ℝ)
    (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (w : ℕ → ℝ) (P : ℝ) (hP : 0 ≤ P)
    (hamp : ∀ q ∈ primitive a Q, ∀ r ∈ primitive a R, ∀ h ∈ H,
      ‖leftAmplitude M ψhat lambda q r h‖ ≤ P) :
    (∑ q ∈ primitive a Q, ∑ n ∈ S, w n * ‖leftRow R H a M ψhat lambda q n‖ ^ 2) ≤
      P ^ 2 * completedMass Q R S H a w := by
  simp only [completedMass, mul_sum]
  apply sum_le_sum
  intro q hq
  let I := primitive a R ×ˢ H
  let amp (u : ℕ × ℤ) := leftAmplitude M ψhat lambda q u.1 u.2
  let k (u v : ℕ × ℤ) := completedTerm S w q u.1 v.1 a u.2 v.2
  calc
    _ ≤ ‖((∑ n ∈ S, w n * ‖leftRow R H a M ψhat lambda q n‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ ∑ u ∈ I, ∑ v ∈ I, ‖(amp u * star (amp v)) * k u v‖ := by
      rw [leftRow_weighted_sq_eq]
      refine (norm_sum_le _ _).trans (sum_le_sum (fun u _ => ?_))
      exact norm_sum_le _ _
    _ ≤ ∑ u ∈ I, ∑ v ∈ I, P ^ 2 * ‖k u v‖ := by
      apply sum_le_sum
      intro u hu
      apply sum_le_sum
      intro v hv
      unfold amp
      rw [norm_mul, norm_mul, norm_star, pow_two]
      exact mul_le_mul_of_nonneg_right (mul_le_mul
        (hamp q hq u.1 (mem_product.mp hu).1 u.2 (mem_product.mp hu).2)
        (hamp q hq v.1 (mem_product.mp hv).1 v.2 (mem_product.mp hv).2)
        (norm_nonneg _) hP) (norm_nonneg _)
    _ = _ := by
      simp only [I, sum_product, k]
      apply sum_congr rfl
      intro r _
      exact sum_comm

/-- The actual dyadic Cauchy multiplier in (E6), with a separately paid
inverse-totient factor `T` and the uniform Fourier amplitude `P`. -/
theorem source_norm_sq_le_completedMass (Q R N : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (S : Finset ℕ) (H : Finset ℤ) (a : ℤ) (M : ℝ)
    (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ)
    (w : ℕ → ℝ) (T P : ℝ) (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hNS : Ico N (2 * N) ⊆ S) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hmajorant : ∀ n ∈ Ico N (2 * N), 1 ≤ w n)
    (hlambda : ∀ q ∈ primitive a (Ico Q (2 * Q)),
      ∀ r ∈ primitive a (Ico R (2 * R)), ‖lambda q r‖ ≤ 1)
    (halpha : ∀ n ∈ Ico N (2 * N), ‖alpha n‖ ≤ 1)
    (hpsi : ∀ x, ‖ψhat x‖ ≤ P)
    (hφ : ∀ q ∈ primitive a (Ico Q (2 * Q)), ∀ s ∈ primitive a (Ico R (2 * R)),
      ((q * s).totient : ℝ)⁻¹ ≤ T / ((Q : ℝ) * R)) :
    ‖source (Ico Q (2 * Q)) (Ico R (2 * R)) (Ico N (2 * N)) H a M ψhat lambda alpha‖ ^ 2 ≤
      T ^ 2 * P ^ 2 * (N : ℝ) ^ 3 / ((Q : ℝ) ^ 3 * (R : ℝ) ^ 2) *
        completedMass (Ico Q (2 * Q)) (Ico R (2 * R)) S H a w := by
  let U := Ico Q (2 * Q)
  let V := Ico R (2 * R)
  let W := Ico N (2 * N)
  have hQ0 : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hR0 : 0 < (R : ℝ) := by exact_mod_cast hR
  have hQR0 : 0 < (Q : ℝ) * R := mul_pos hQ0 hR0
  have hcard (L : ℕ) : ((Ico L (2 * L)).card : ℝ) = L := by
    simp only [Nat.card_Ico]
    congr 1
    omega
  have hqCard : ((primitive a U).card : ℝ) ≤ Q := by
    rw [← hcard Q]
    exact_mod_cast card_filter_le _ _
  have hrCard : ((primitive a V).card : ℝ) ≤ R := by
    rw [← hcard R]
    exact_mod_cast card_filter_le _ _
  have hright (q : ℕ) (hq : q ∈ primitive a U) :
      ‖rightRow V W a lambda alpha q‖ ≤ T * N / Q := by
    refine (norm_rightRow_le V W a lambda alpha q (hlambda q hq) halpha).trans ?_
    calc
      _ ≤ ∑ s ∈ primitive a V, ∑ _n ∈ W, T / ((Q : ℝ) * R) := by
        refine sum_le_sum (fun s hs => sum_le_sum (fun n _ => ?_))
        split_ifs
        · exact hφ q hq s hs
        · positivity
      _ = ((primitive a V).card : ℝ) * (N * (T / ((Q : ℝ) * R))) := by
        simp only [sum_const, nsmul_eq_mul, W, hcard]
      _ ≤ R * (N * (T / ((Q : ℝ) * R))) :=
        mul_le_mul_of_nonneg_right hrCard (by positivity)
      _ = _ := by field_simp
  have houter : (∑ q ∈ primitive a U, ∑ n ∈ W, ‖rightRow V W a lambda alpha q * alpha n‖ ^ 2) ≤
      Q * (N * (T * N / Q) ^ 2) := by
    calc
      _ ≤ ∑ q ∈ primitive a U, ∑ _n ∈ W, (T * N / Q) ^ 2 := by
        refine sum_le_sum (fun q hq => sum_le_sum (fun n hn => ?_))
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (halpha n hn)).trans (hright q hq)
      _ = ((primitive a U).card : ℝ) * (N * (T * N / Q) ^ 2) := by
        simp only [sum_const, nsmul_eq_mul, W, hcard]
      _ ≤ _ := mul_le_mul_of_nonneg_right hqCard (by positivity)
  have hamp (q : ℕ) (hq : q ∈ primitive a U) (r : ℕ) (hr : r ∈ primitive a V) (h : ℤ) :
      ‖leftAmplitude M ψhat lambda q r h‖ ≤ P / ((Q : ℝ) * R) := by
    have hqL : (Q : ℝ) ≤ q := by exact_mod_cast (mem_Ico.mp (mem_filter.mp hq).1).1
    have hrL : (R : ℝ) ≤ r := by exact_mod_cast (mem_Ico.mp (mem_filter.mp hr).1).1
    have hprod : (Q : ℝ) * R ≤ q * (r : ℝ) :=
      mul_le_mul hqL hrL hR0.le (Nat.cast_nonneg q)
    unfold leftAmplitude
    simp only [norm_div, norm_mul, Complex.norm_natCast, Nat.cast_mul]
    calc
      _ ≤ P / (q * (r : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (mul_le_mul (hlambda q hq r hr) (hpsi _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ ≤ _ := div_le_div_of_nonneg_left hP hQR0 hprod
  have hpositive : 0 ≤ ∑ q ∈ primitive a U, ∑ n ∈ S, w n * ‖leftRow V H a M ψhat lambda q n‖ ^ 2 :=
    sum_nonneg (fun _ _ => sum_nonneg (fun n hn => mul_nonneg (hw n hn) (sq_nonneg _)))
  have hinner := leftRows_weighted_sq_le U V S H a M ψhat lambda w (P / ((Q : ℝ) * R))
    (div_nonneg hP hQR0.le) (fun q hq r hr h _ => hamp q hq r hr h)
  calc
    _ ≤ _ := source_norm_sq_le_weighted U V W S H a M ψhat lambda alpha w hNS hw hmajorant
    _ ≤ (Q * (N * (T * N / Q) ^ 2)) * ((P / ((Q : ℝ) * R)) ^ 2 * completedMass U V S H a w) :=
      mul_le_mul houter hinner hpositive (by positivity)
    _ = _ := by field_simp; ring

end E1Finite

end

end ImbalancedChen.Part3
