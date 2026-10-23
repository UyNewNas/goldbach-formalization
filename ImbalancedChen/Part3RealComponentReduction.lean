import ImbalancedChen.Part3ComplexDispersion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Real components of the actual five complex coefficient functions

Each component keeps the same atom geometry, interval, physical factors,
moving residue and primitive-coprime mean. The five original coefficient
functions are projected independently, so their factor structure remains
available. The exact 32-term expansion is proved before taking a norm.

The admissibility gates and family-uniform auxiliary SW constants are
preserved by real/imaginary projection. No real distribution theorem,
completion identity, fibre bound or analytic estimate is assumed here.
The component sums and their finite Cauchy cost do not assert the missing
RestrictedMediumObligation.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical

def complexRealComponent (b : Bool) (z : ℂ) : ℂ :=
  if b then (z.im : ℂ) else (z.re : ℂ)

def complexRealComponentPhase (b : Bool) : ℂ := if b then Complex.I else 1

@[simp] theorem complexRealComponent_zero (b : Bool) : complexRealComponent b 0 = 0 := by
  cases b <;> simp [complexRealComponent]

theorem complexRealComponent_norm_le (b : Bool) (z : ℂ) :
    ‖complexRealComponent b z‖ ≤ ‖z‖ := by
  cases b
  · simpa [complexRealComponent] using Complex.abs_re_le_norm z
  · simpa [complexRealComponent] using Complex.abs_im_le_norm z

theorem complexRealComponent_original_ne_zero (b : Bool) {z : ℂ}
    (h : complexRealComponent b z ≠ 0) : z ≠ 0 := by
  intro hz
  apply h
  rw [hz, complexRealComponent_zero]

@[simp] theorem complexRealComponent_im (b : Bool) (z : ℂ) :
    (complexRealComponent b z).im = 0 := by
  cases b <;> simp [complexRealComponent]

theorem complexRealComponent_sub (b : Bool) (z w : ℂ) :
    complexRealComponent b (z - w) = complexRealComponent b z - complexRealComponent b w := by
  cases b <;> simp [complexRealComponent]

theorem complexRealComponent_sum {ι : Type*} (b : Bool) (S : Finset ι) (f : ι → ℂ) :
    complexRealComponent b (∑ i ∈ S, f i) = ∑ i ∈ S, complexRealComponent b (f i) := by
  cases b <;> simp [complexRealComponent, Complex.ofReal_sum]

theorem complexRealComponent_div_natCast (b : Bool) (z : ℂ) (q : ℕ) :
    complexRealComponent b (z / (q : ℂ)) = complexRealComponent b z / (q : ℂ) := by
  cases b <;> simp [complexRealComponent, Complex.div_natCast, Complex.ofReal_div]

theorem complexRealComponent_ite (b : Bool) (P : Prop) [Decidable P] (z : ℂ) :
    complexRealComponent b (if P then z else 0) = if P then complexRealComponent b z else 0 := by
  by_cases h : P <;> simp [h]

theorem complexRealComponent_reconstruct (z : ℂ) :
    (∑ b : Bool, complexRealComponentPhase b * complexRealComponent b z) = z := by
  simpa [complexRealComponentPhase, complexRealComponent, mul_comm, add_comm] using
    Complex.re_add_im z

@[simp] theorem complexRealComponentPhase_norm (b : Bool) :
    ‖complexRealComponentPhase b‖ = 1 := by
  cases b <;> simp [complexRealComponentPhase]

abbrev MediumRealChoice := Fin 5 → Bool

def mediumRealChoicePhase (eta : MediumRealChoice) : ℂ :=
  ∏ i : Fin 5, complexRealComponentPhase (eta i)

@[simp] theorem mediumRealChoicePhase_norm (eta : MediumRealChoice) :
    ‖mediumRealChoicePhase eta‖ = 1 := by
  simp [mediumRealChoicePhase, norm_prod]

theorem mediumRealChoice_card : Fintype.card MediumRealChoice = 32 := by decide

theorem complexFiveProduct_eq_realChoiceSum (z : Fin 5 → ℂ) :
    (∏ i, z i) = ∑ eta : MediumRealChoice,
      mediumRealChoicePhase eta * ∏ i, complexRealComponent (eta i) (z i) := by
  calc
    _ = ∏ i : Fin 5, ∑ b : Bool,
        complexRealComponentPhase b * complexRealComponent b (z i) := by
      simp_rw [complexRealComponent_reconstruct]
    _ = ∑ eta : MediumRealChoice, ∏ i : Fin 5,
        complexRealComponentPhase (eta i) * complexRealComponent (eta i) (z i) :=
      Fintype.prod_sum _
    _ = _ := by simp only [Finset.prod_mul_distrib, mediumRealChoicePhase]

def MediumAtom.realComponentAtom (d : MediumAtom) (eta : MediumRealChoice) : MediumAtom :=
  { d with
    alpha := fun n => complexRealComponent (eta 0) (d.alpha n)
    beta := fun n => complexRealComponent (eta 1) (d.beta n)
    gamma1 := fun q => complexRealComponent (eta 2) (d.gamma1 q)
    gamma2 := fun q => complexRealComponent (eta 3) (d.gamma2 q)
    gamma3 := fun q => complexRealComponent (eta 4) (d.gamma3 q) }

@[simp] theorem MediumAtom.realComponentAtom_scale (d : MediumAtom) (eta : MediumRealChoice) :
    (d.realComponentAtom eta).scale = d.scale := rfl

@[simp] theorem MediumAtom.realComponentAtom_residue (d : MediumAtom) (eta : MediumRealChoice) :
    (d.realComponentAtom eta).residue = d.residue := rfl

@[simp] theorem MediumAtom.realComponentAtom_alphaCarrier (d : MediumAtom) (eta : MediumRealChoice) :
    (d.realComponentAtom eta).alphaCarrier = d.alphaCarrier := rfl

@[simp] theorem MediumAtom.realComponentAtom_betaCarrier (d : MediumAtom) (eta : MediumRealChoice) :
    (d.realComponentAtom eta).betaCarrier = d.betaCarrier := rfl

@[simp] theorem MediumAtom.realComponentAtom_complexRowLabels
    (d : MediumAtom) (eta : MediumRealChoice) :
    (d.realComponentAtom eta).complexRowLabels = d.complexRowLabels := rfl

/-- All scale, roughness, divisor and primitive-residue gates are inherited
by actual coefficient projection; no separate hypothesis is added. -/
theorem mediumAdmissible_realComponentAtom
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (eta : MediumRealChoice) :
    MediumAdmissible B sigma kappa c0 (d.realComponentAtom eta) := by
  obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
    hAlpha, hRough, hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
  refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact (complexRealComponent_norm_le (eta 0) (d.alpha n)).trans (hAlpha n hn)
  · intro n hn hne p hp hpn
    exact hRough n hn (complexRealComponent_original_ne_zero (eta 0) hne) p hp hpn
  · intro n hn
    exact (complexRealComponent_norm_le (eta 1) (d.beta n)).trans (hBeta n hn)
  · intro q hq
    exact ⟨(complexRealComponent_norm_le (eta 2) (d.gamma1 q)).trans (hGamma1 q hq).1,
      fun hne => (hGamma1 q hq).2 (complexRealComponent_original_ne_zero (eta 2) hne)⟩
  · intro q hq
    exact ⟨(complexRealComponent_norm_le (eta 3) (d.gamma2 q)).trans (hGamma2 q hq).1,
      fun hne => (hGamma2 q hq).2 (complexRealComponent_original_ne_zero (eta 3) hne)⟩
  · intro q hq
    exact ⟨(complexRealComponent_norm_le (eta 4) (d.gamma3 q)).trans (hGamma3 q hq).1,
      fun hne => (hGamma3 q hq).2 (complexRealComponent_original_ne_zero (eta 4) hne)⟩

/-- The primitive auxiliary mean projects linearly even at totient zero;
the actual SW consumer has positive q as before. -/
theorem MediumAtom.realComponentAtom_auxSWError (d : MediumAtom)
    (eta : MediumRealChoice) (k q b : ℕ) :
    (d.realComponentAtom eta).auxSWError k q b =
      complexRealComponent (eta 0) (d.auxSWError k q b) := by
  unfold MediumAtom.auxSWError
  change ((∑ n ∈ d.alphaCarrier,
      if Nat.ModEq q n b ∧ Nat.Coprime n k then complexRealComponent (eta 0) (d.alpha n) else 0) -
    (∑ n ∈ d.alphaCarrier,
      if Nat.Coprime n (k * q) then complexRealComponent (eta 0) (d.alpha n) else 0) /
        (Nat.totient q : ℂ)) = _
  simp only [complexRealComponent_sub, complexRealComponent_div_natCast,
    complexRealComponent_sum, complexRealComponent_ite]

/-- The same C and x0 work for every atom AND all 32 components. -/
theorem uniformAuxiliarySW_realComponents {ι : Type*} (F : ι → MediumAtom) (C0 : ℕ)
    (h : UniformAuxiliarySW F C0) :
    UniformAuxiliarySW (fun j : ι × MediumRealChoice => (F j.1).realComponentAtom j.2) C0 := by
  intro A hA
  obtain ⟨C, hC, x0, hx0, hbound⟩ := h A hA
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro j hx k q b hk hq hb
  rw [MediumAtom.realComponentAtom_auxSWError]
  exact (complexRealComponent_norm_le (j.2 0) ((F j.1).auxSWError k q b)).trans
    (hbound j.1 hx k q b hk hq hb)

def MediumAtom.fiveCoefficients (d : MediumAtom) (n : ℕ)
    (l : (ℕ × ℕ × ℕ) × ℕ) : Fin 5 → ℂ :=
  ![d.alpha n, d.beta l.2, d.gamma1 l.1.1, d.gamma2 l.1.2.1, d.gamma3 l.1.2.2]

private theorem signedError_eq_fiveProducts (d : MediumAtom) :
    d.signedError = ∑ n ∈ d.alphaCarrier, ∑ l ∈ d.complexRowLabels,
      (∏ i, d.fiveCoefficients n l i) *
        complexPrimitiveKernel d.residue (complexFactorModulus l.1) n l.2 := by
  rw [MediumAtom.signedError_eq_complexCenteredRows]
  simp_rw [MediumAtom.complexCenteredRow_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro l _
  simp [MediumAtom.fiveCoefficients, Fin.prod_univ_five,
    MediumAtom.complexRowContribution, MediumAtom.complexFactorGamma,
    mul_assoc, mul_comm, mul_left_comm]

private theorem realComponentAtom_fiveCoefficients (d : MediumAtom) (eta : MediumRealChoice)
    (n : ℕ) (l : (ℕ × ℕ × ℕ) × ℕ) (i : Fin 5) :
    (d.realComponentAtom eta).fiveCoefficients n l i =
      complexRealComponent (eta i) (d.fiveCoefficients n l i) := by
  fin_cases i <;> rfl

/-- Exact 32-term decomposition before taking any norm. All factor labels
and their multiplicities, the actual residue and the primitive mean persist. -/
theorem MediumAtom.signedError_eq_realComponents (d : MediumAtom) :
    d.signedError = ∑ eta : MediumRealChoice,
      mediumRealChoicePhase eta * (d.realComponentAtom eta).signedError := by
  have hterm (n : ℕ) (l : (ℕ × ℕ × ℕ) × ℕ) :
      (∏ i, d.fiveCoefficients n l i) *
          complexPrimitiveKernel d.residue (complexFactorModulus l.1) n l.2 =
        ∑ eta : MediumRealChoice,
          (mediumRealChoicePhase eta *
            ∏ i, complexRealComponent (eta i) (d.fiveCoefficients n l i)) *
              complexPrimitiveKernel d.residue (complexFactorModulus l.1) n l.2 := by
    rw [complexFiveProduct_eq_realChoiceSum, Finset.sum_mul]
  rw [signedError_eq_fiveProducts]
  simp_rw [hterm]
  calc
    _ = ∑ n ∈ d.alphaCarrier, ∑ eta : MediumRealChoice, ∑ l ∈ d.complexRowLabels,
        (mediumRealChoicePhase eta *
          ∏ i, complexRealComponent (eta i) (d.fiveCoefficients n l i)) *
            complexPrimitiveKernel d.residue (complexFactorModulus l.1) n l.2 := by
      apply Finset.sum_congr rfl
      intro n _
      exact Finset.sum_comm
    _ = ∑ eta : MediumRealChoice, ∑ n ∈ d.alphaCarrier, ∑ l ∈ d.complexRowLabels,
        (mediumRealChoicePhase eta *
          ∏ i, complexRealComponent (eta i) (d.fiveCoefficients n l i)) *
            complexPrimitiveKernel d.residue (complexFactorModulus l.1) n l.2 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro eta _
      rw [signedError_eq_fiveProducts]
      simp only [MediumAtom.realComponentAtom_alphaCarrier,
        MediumAtom.realComponentAtom_complexRowLabels, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro l _
      simp only [realComponentAtom_fiveCoefficients, MediumAtom.realComponentAtom_residue,
        mul_assoc]

theorem MediumAtom.signedError_norm_le_realComponents (d : MediumAtom) :
    ‖d.signedError‖ ≤ ∑ eta : MediumRealChoice, ‖(d.realComponentAtom eta).signedError‖ := by
  rw [MediumAtom.signedError_eq_realComponents]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, mediumRealChoicePhase_norm, one_mul])

/-- The precise finite cost: 32 times the sum of the 32 squared errors.
If each real component later has bound M, this is 1024 M^2. -/
theorem MediumAtom.signedError_norm_sq_le_realComponents (d : MediumAtom) :
    ‖d.signedError‖ ^ 2 ≤
      32 * ∑ eta : MediumRealChoice, ‖(d.realComponentAtom eta).signedError‖ ^ 2 := by
  have h0 : 0 ≤ ∑ eta : MediumRealChoice, ‖(d.realComponentAtom eta).signedError‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (∑ eta : MediumRealChoice, ‖(d.realComponentAtom eta).signedError‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) h0).2 d.signedError_norm_le_realComponents
    _ ≤ (∑ _eta : MediumRealChoice, (1 : ℝ) ^ 2) *
        ∑ eta : MediumRealChoice, ‖(d.realComponentAtom eta).signedError‖ ^ 2 := by
      simpa only [one_mul] using Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset MediumRealChoice) (fun _ => (1 : ℝ))
        (fun eta => ‖(d.realComponentAtom eta).signedError‖)
    _ = _ := by simp

end

end ImbalancedChen.Part3
