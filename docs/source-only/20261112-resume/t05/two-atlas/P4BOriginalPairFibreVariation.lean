import ImbalancedChen.P4BOriginalFiniteSignedTrim
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import ImbalancedChen.P4BPositiveUpperPrimeBV

/-! Finite Abel coefficients for one free coordinate of the original trimmed
ordered prime pair. The complete product cutoff, all four physical walls and
the disjoint choice of the smaller coordinate are present in the profile. -/
namespace ImbalancedChen.P4BOriginalPairFibreVariation
noncomputable section
open scoped BigOperators
open P4B
open P5Z.ActualEtaPsiOccurrenceBudget (eta)
open P4BPositiveUpperPrimeBV (prefixProfile)

def variation (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range X, |f i-f (i+1)|

structure Control (X : ℕ) (f : ℕ → ℝ) (B : ℝ) : Prop where
  unit : ∀ i, 0≤f i ∧ f i≤1
  bound : variation X f≤B

private theorem monotone_control (X : ℕ) (f : ℕ → ℝ)
    (hu : ∀ i,0≤f i ∧ f i≤1) (hm : Monotone f ∨ Antitone f) : Control X f 1 := by
  refine ⟨hu,?_⟩
  rcases hm with h|h
  · have H (i : ℕ) : |f i-f (i+1)| = f (i+1)-f i := by
      rw [abs_of_nonpos (sub_nonpos.mpr (h (Nat.le_succ i)))]
      ring
    simp only [variation,H,Finset.sum_range_sub]
    linarith [(hu X).2,(hu 0).1]
  · have H (i : ℕ) : |f i-f (i+1)| = f i-f (i+1) :=
      abs_of_nonneg (sub_nonneg.mpr (h (Nat.le_succ i)))
    simp only [variation,H,Finset.sum_range_sub']
    linarith [(hu 0).2,(hu X).1]

private theorem mul_control {X : ℕ} {f g : ℕ → ℝ} {A B : ℝ}
    (hf : Control X f A) (hg : Control X g B) :
    Control X (fun i => f i*g i) (A+B) := by
  refine ⟨fun i => ⟨mul_nonneg (hf.unit i).1 (hg.unit i).1,
    (mul_le_mul (hf.unit i).2 (hg.unit i).2 (hg.unit i).1 zero_le_one).trans_eq (one_mul _)⟩,?_⟩
  apply le_trans _ (add_le_add hf.bound hg.bound)
  simp only [variation,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = |(f i-f (i+1))*g i+f (i+1)*(g i-g (i+1))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ |f i-f (i+1)|+|g i-g (i+1)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (hg.unit i).1,abs_of_nonneg (hf.unit (i+1)).1]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (hg.unit i).2)
        (mul_le_of_le_one_left (abs_nonneg _) (hf.unit (i+1)).2)

def coord (N j : ℕ) : ℝ := Real.log (max 1 (j:ℝ))/Real.log (N:ℝ)

private theorem coord_mono {N : ℕ} (hN : (1:ℝ)<N) : Monotone (coord N) := by
  intro i j hij
  apply div_le_div_of_nonneg_right _ (Real.log_pos hN).le
  exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (max_le_max_left 1 (Nat.cast_le.mpr hij))

def offset (swap : Bool) (N p : ℕ) : Fin 2 → ℝ :=
  if swap then ![0,coord N p] else ![coord N p,0]

def direction (swap : Bool) : Fin 2 → ℝ :=
  if swap then ![1,0] else ![0,1]

def owner (swap : Bool) (p j : ℕ) : ℝ :=
  if swap then (if p<j then 1 else 0) else (if p≤j then 1 else 0)

def fibre (swap : Bool) (b kappa s kappa0 : ℝ) (N p j : ℕ) : ℝ :=
  owner swap p j *
    (eta (((p:ℝ)*(j:ℝ))/(N:ℝ)^(1-kappa0)) *
      smoothPhysicalProfileLine b N (manuscriptHalfProductCutoff kappa N) s
        (offset swap N p) (direction swap) (coord N j))

theorem fibre_control (swap : Bool) (b kappa s kappa0 : ℝ) (N X p : ℕ)
    (hN : (1:ℝ)<N) (hs : 0<s) : Control X (fibre swap b kappa s kappa0 N p) 6 := by
  let gate (i : Fin 4) (j : ℕ) := smoothGateUpperStep s
    (smoothPhysicalProfileMargin b N (manuscriptHalfProductCutoff kappa N) (offset swap N p) i+
      smoothPhysicalWallRow b N i (direction swap)*coord N j)
  have HG (i : Fin 4) : Control X (gate i) 1 := by
    apply monotone_control _ _ (fun j => smoothGateUpperStep_bounds _ _)
    by_cases hi : 0≤smoothPhysicalWallRow b N i (direction swap)
    · exact Or.inl (fun j l h => monotone_smoothGateUpperStep hs
        (add_le_add_left (mul_le_mul_of_nonneg_left (coord_mono hN h) hi) _))
    · exact Or.inr (fun j l h => monotone_smoothGateUpperStep hs
        (add_le_add_left (mul_le_mul_of_nonpos_left (coord_mono hN h) (lt_of_not_ge hi).le) _))
  have HP : Control X (fun j => ∏ i : Fin 4, gate i j) 4 := by
    have H := mul_control (mul_control (mul_control (HG 0) (HG 1)) (HG 2)) (HG 3)
    simpa only [Fin.prod_univ_four, mul_assoc,show (1+1+1+1:ℝ)=4 by norm_num] using H
  have HE : Control X (fun j : ℕ => eta (((p:ℝ)*(j:ℝ))/(N:ℝ)^(1-kappa0))) 1 := by
    apply monotone_control _ _ (fun _ => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
    exact Or.inl (fun j l h => Real.smoothTransition.monotone
      (sub_le_sub_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (Nat.cast_nonneg p))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)) _))
  have HO : Control X (owner swap p) 1 := by
    apply monotone_control
    · intro j
      cases swap <;> simp only [owner,Bool.false_eq_true,ite_false,ite_true] <;>
        split_ifs <;> norm_num
    · left
      intro i j hij
      cases swap <;> simp only [owner,Bool.false_eq_true,ite_false,ite_true] <;>
        split_ifs <;> norm_num <;> omega
  have H := mul_control HO (mul_control HE HP)
  simpa only [fibre,smoothPhysicalProfileLine_eq_affine_gate_product,gate,
    show (1+(1+4):ℝ)=6 by norm_num] using H

def abelCoefficient (f : ℕ → ℝ) (X i : ℕ) : ℝ := if i=X then f X else f i-f (i+1)

/-- The last endpoint has coefficient f(X), including when X=0. -/
theorem abel_on (f : ℕ → ℝ) {X j : ℕ} (hj : j≤X) :
    prefixProfile (Finset.univ : Finset (Fin (X+1)))
      (fun i => abelCoefficient f X i.val) Fin.val j = f j := by
  classical
  let g (i : ℕ) := if i<j then f j else if i≤X then f i else 0
  have hstep (i : ℕ) (hi : i<X+1) :
      abelCoefficient f X i*(if j≤i then (1:ℝ) else 0) = g i-g (i+1) := by
    by_cases hij : i<j
    · have hiX : i≠X := by omega
      by_cases hnext : i+1<j
      · simp [abelCoefficient,hiX,g,hij,hnext,not_le.mpr hij]
      · have he : i+1=j := by omega
        simp [abelCoefficient,hiX,g,hij,not_le.mpr hij,he,hj]
    · have hji : j≤i := by omega
      have hj' : ¬i+1<j := by omega
      by_cases he : i=X
      · subst i
        simp [abelCoefficient,g,hij,hj',hji]
      · have h1 : i≤X := by omega
        have h2 : i+1≤X := by omega
        simp [abelCoefficient,g,he,hij,hj',hji,h1,h2]
  unfold prefixProfile
  rw [Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i∈Finset.range (X+1),(g i-g (i+1)) :=
      Finset.sum_congr rfl (fun i hi => hstep i (Finset.mem_range.mp hi))
    _ = g 0-g (X+1) := Finset.sum_range_sub' g (X+1)
    _ = f j := by
      have hlate : ¬X+1<j := by omega
      by_cases h : 0<j
      · simp [g,h,hlate]
      · have hj0 : j=0 := by omega
        simp [g,hj0]

theorem abel_mass {X : ℕ} {f : ℕ → ℝ} {B : ℝ} (h : Control X f B) :
    (∑ i : Fin (X+1), |abelCoefficient f X i.val|) ≤ B+1 := by
  rw [Fin.sum_univ_eq_sum_range,Finset.sum_range_succ]
  have hsum : (∑ i∈Finset.range X,|abelCoefficient f X i|)=variation X f :=
    Finset.sum_congr rfl (fun i hi => by
      rw [abelCoefficient,if_neg (Finset.mem_range.mp hi).ne])
  rw [hsum,abelCoefficient,if_pos rfl,abs_of_nonneg (h.unit X).1]
  exact add_le_add h.bound (h.unit X).2

end
end ImbalancedChen.P4BOriginalPairFibreVariation
