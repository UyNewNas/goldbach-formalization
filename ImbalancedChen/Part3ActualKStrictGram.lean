import ImbalancedChen.Part3CrossKPlancherel
import ImbalancedChen.Part3EvenFourierHilbert
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
Distinct actual exponential-cosh profiles are strictly linearly independent.
The L2 upgrade uses continuity and the full support of Lebesgue measure.
The resulting actual K0(q+r) Gram kernel is strictly positive definite,
and the actual full-axis K-height L2 family is linearly independent.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualKStrictGramSourceOnly

open MeasureTheory FourierTransform
open scoped BigOperators ComplexInnerProductSpace ComplexConjugate
open ImaginaryOrderKBesselSourceOnly KFullLineFourierBridgeSourceOnly
open P3ActualKProfileLpSourceOnly HalfCosinePlancherelSourceOnly
open CrossKPlancherelSourceOnly EvenFourierHilbertSourceOnly

/-- The exponential profile in its genuine additive-semigroup character coordinates. -/
def laplaceCharacter (q : ℝ) : Multiplicative ℝ≥0 →* ℂ where
  toFun x := (Real.exp (-q * (Multiplicative.toAdd x : ℝ)) : ℂ)
  map_one' := by simp
  map_mul' x y := by simp [mul_add, Real.exp_add]

theorem laplaceCharacter_injective : Function.Injective laplaceCharacter := by
  intro q r h
  have he : Real.exp (-q) = Real.exp (-r) := by
    apply Complex.ofReal_injective
    simpa [laplaceCharacter] using
      congrArg (fun χ : Multiplicative ℝ≥0 →* ℂ => χ (Multiplicative.ofAdd 1)) h
  exact neg_injective (Real.exp_injective he)

/-- Dedekind independence of characters, transferred through cosh(arcosh(1+x)).
Positivity of q is unnecessary for this purely pointwise independence statement. -/
theorem kEvenProfile_linearIndependent : LinearIndependent ℂ kEvenProfile := by
  classical
  have hχ : LinearIndependent ℂ
      (fun q : ℝ => (laplaceCharacter q : Multiplicative ℝ≥0 → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℝ≥0) ℂ).comp
      laplaceCharacter laplaceCharacter_injective
  apply linearIndependent_iff'.2
  intro s c hc i hi
  have hχsum : ∑ q ∈ s, (c q * (Real.exp (-q) : ℂ)) •
      (laplaceCharacter q : Multiplicative ℝ≥0 → ℂ) = 0 := by
    funext x
    have hx : 1 ≤ 1 + (Multiplicative.toAdd x : ℝ) := by positivity
    have hprofile (q : ℝ) :
        kEvenProfile q (Real.arcosh (1 + (Multiplicative.toAdd x : ℝ))) =
          (Real.exp (-q) : ℂ) * laplaceCharacter q x := by
      simp [kEvenProfile, evenLaplaceProfile, laplaceCharacter,
        Real.cosh_arcosh hx, mul_add, Real.exp_add]
    have hev := congrFun hc (Real.arcosh (1 + (Multiplicative.toAdd x : ℝ)))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hprofile, mul_assoc] using hev
  have hz := (linearIndependent_iff'.1 hχ) s
    (fun q => c q * (Real.exp (-q) : ℂ)) hχsum i hi
  exact (mul_eq_zero.mp hz).resolve_right
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-- Continuous pointwise independence survives the actual a.e. quotient.
The use of full-support Lebesgue measure is explicit in ae_eq_iff_eq. -/
theorem linearIndependent_toLp_of_continuous {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, MemLp (f i) 2)
    (hc : ∀ i, Continuous (f i)) (hli : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun i => (hf i).toLp (f i)) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro c hsum i
  let w : ι → ComplexL2 := fun j => c j • (hf j).toLp (f j)
  have hterm (j : ι) : (w j : ℝ → ℂ) =ᵐ[volume]
      fun x => c j * f j x := by
    filter_upwards [Lp.coeFn_smul (c j) ((hf j).toLp (f j)),
      (hf j).coeFn_toLp] with x hx hfx
    simpa only [w, Pi.smul_apply, smul_eq_mul, hfx] using hx
  have hzero : ((∑ j, w j : ComplexL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
    change ((∑ j, c j • (hf j).toLp (f j) : ComplexL2) : ℝ → ℂ) =ᵐ[volume] 0
    rw [hsum]
    exact Lp.coeFn_zero ℂ 2 volume
  have hae : (fun x : ℝ => ∑ j, c j * f j x) =ᵐ[volume] 0 := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ w,
      hzero, ae_all_iff.2 hterm] with x hx hz hall
    calc
      _ = ∑ j, w j x := Finset.sum_congr rfl (fun j _ => (hall j).symm)
      _ = (∑ j, w j : ComplexL2) x := hx.symm
      _ = 0 := hz
  have hcont : Continuous (fun x : ℝ => ∑ j, c j * f j x) := by
    exact continuous_finset_sum _ (fun j _ => continuous_const.mul (hc j))
  have heq := (hcont.ae_eq_iff_eq volume continuous_zero).1 hae
  apply (Fintype.linearIndependent_iff.1 hli) c ?_ i
  funext x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
    congrFun heq x

section FiniteFamily

variable {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i)

theorem evenKProfile_L2_linearIndependent (hinj : Function.Injective q) :
    LinearIndependent ℂ (fun i => (evenKProfile (q i) (hq i) : ComplexL2)) := by
  exact linearIndependent_toLp_of_continuous (fun i => kEvenProfile (q i))
    (fun i => kEvenProfile_memLp_two (hq i))
    (fun i => evenLaplaceProfile_continuous (q i))
    (kEvenProfile_linearIndependent.comp q hinj)

/-- The spatial L2 Gram entries are twice the actual K0 sum kernel. -/
theorem evenKProfile_inner (i j : ι) :
    inner ℂ (evenKProfile (q i) (hq i) : ComplexL2)
      (evenKProfile (q j) (hq j) : ComplexL2) =
        (2 : ℂ) * (imaginaryOrderK 0 (q i + q j) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ u : ℝ, inner ℂ (kEvenProfile (q i) u) (kEvenProfile (q j) u) := by
      apply integral_congr_ae
      filter_upwards [(kEvenProfile_memLp_two (hq i)).coeFn_toLp,
        (kEvenProfile_memLp_two (hq j)).coeFn_toLp] with u hi hj
      change inner ℂ ((kEvenProfile_memLp_two (hq i)).toLp _ u)
        ((kEvenProfile_memLp_two (hq j)).toLp _ u) = _
      rw [hi, hj]
    _ = _ := integral_inner_kEvenProfile (hq i) (hq j)

/-- The height L2 Gram entries have the distinct, exact factor pi/2. -/
theorem evenKHeight_inner (i j : ι) :
    inner ℂ (evenKHeight (q i) (hq i) : ComplexL2)
      (evenKHeight (q j) (hq j) : ComplexL2) =
        ((Real.pi : ℂ) / 2) * (imaginaryOrderK 0 (q i + q j) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ t : ℝ, ((imaginaryOrderK t (q i) * imaginaryOrderK t (q j) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [evenKHeight_coe_ae (q i) (hq i),
        evenKHeight_coe_ae (q j) (hq j)] with t hi hj
      rw [hi, hj]
      simp [RCLike.inner_apply', Complex.ofReal_mul]
    _ = ((∫ t : ℝ, imaginaryOrderK t (q i) * imaginaryOrderK t (q j) : ℝ) : ℂ) :=
      integral_ofReal
    _ = _ := by
      rw [imaginaryOrderK_cross_plancherel (hq i) (hq j)]
      push_cast
      rfl

/-- The Hermitian form of the actual K0(q_i+q_j) kernel. -/
def kZeroGramForm (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (c i) * c j * (imaginaryOrderK 0 (q i + q j) : ℂ)

private theorem family_norm_sq {v : ι → ComplexL2} {a : ℝ}
    (hinner : ∀ i j, inner ℂ (v i) (v j) =
      (a : ℂ) * (imaginaryOrderK 0 (q i + q j) : ℂ)) (c : ι → ℂ) :
    ‖∑ i, c i • v i‖ ^ 2 = a * (kZeroGramForm q c).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have heq : inner ℂ (∑ i, c i • v i) (∑ j, c j • v j) =
      (a : ℂ) * kZeroGramForm q c := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hinner]
    unfold kZeroGramForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  simp

theorem evenKProfile_combination_norm_sq (c : ι → ℂ) :
    ‖∑ i, c i • (evenKProfile (q i) (hq i) : ComplexL2)‖ ^ 2 =
      2 * (kZeroGramForm q c).re := by
  exact family_norm_sq q (by intro i j; exact evenKProfile_inner q hq i j) c

theorem evenKHeight_combination_norm_sq (c : ι → ℂ) :
    ‖∑ i, c i • (evenKHeight (q i) (hq i) : ComplexL2)‖ ^ 2 =
      (Real.pi / 2) * (kZeroGramForm q c).re := by
  apply family_norm_sq q _ c
  intro i j
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using evenKHeight_inner q hq i j

/-- Strict positivity, not merely semidefiniteness: distinct positive q_i
give a positive Hermitian Gram form for every nonzero complex coefficient vector. -/
include hq in
theorem kZeroGramForm_pos (hinj : Function.Injective q)
    (c : ι → ℂ) (hc : c ≠ 0) : 0 < (kZeroGramForm q c).re := by
  have hne : (∑ i, c i • (evenKProfile (q i) (hq i) : ComplexL2)) ≠ 0 := by
    intro hz
    apply hc
    funext i
    exact (Fintype.linearIndependent_iff.1
      (evenKProfile_L2_linearIndependent q hq hinj)) c hz i
  have hpos : 0 < ‖∑ i, c i • (evenKProfile (q i) (hq i) : ComplexL2)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hne)
  rw [evenKProfile_combination_norm_sq q hq c] at hpos
  linarith

theorem evenKHeight_L2_linearIndependent (hinj : Function.Injective q) :
    LinearIndependent ℂ (fun i => (evenKHeight (q i) (hq i) : ComplexL2)) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro c hsum i
  by_cases hc : c = 0
  · simp [hc]
  · have hp := kZeroGramForm_pos q hq hinj c hc
    have hn := evenKHeight_combination_norm_sq q hq c
    rw [hsum, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
    have hπ : 0 < Real.pi / 2 := by positivity
    have hpos := mul_pos hπ hp
    linarith

/-- The real symmetric matrix (K0(q_i+q_j)) is strictly positive definite. -/
include hq in
theorem kZeroGram_real_pos (hinj : Function.Injective q)
    (c : ι → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * imaginaryOrderK 0 (q i + q j) := by
  have hc' : (fun i => (c i : ℂ)) ≠ 0 := by
    intro hz
    apply hc
    funext i
    exact Complex.ofReal_injective (congrFun hz i)
  have hp := kZeroGramForm_pos q hq hinj (fun i => (c i : ℂ)) hc'
  simpa [kZeroGramForm, Complex.mul_re] using hp


-- Explicit contract regressions: the restored positivity premise is mandatory.
-- User-approved restoration, 2026-10-26; no positivity claim is made for q ≤ 0.
example (q : ι → ℝ) (hq : ∀ i, 0 < q i) (hinj : Function.Injective q)
    (c : ι → ℂ) (hc : c ≠ 0) :
    0 < (kZeroGramForm q c).re :=
  kZeroGramForm_pos q hq hinj c hc

example (q : ι → ℝ) (hq : ∀ i, 0 < q i) (hinj : Function.Injective q)
    (c : ι → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * imaginaryOrderK 0 (q i + q j) :=
  kZeroGram_real_pos q hq hinj c hc

end FiniteFamily

-- Whole-constant type checks include every binder (including implicit ones).
-- Unlike applying the theorem, these checks cannot silently supply extra premises.
example : ∀ {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hinj : Function.Injective q) (c : ι → ℂ),
    c ≠ 0 → 0 < (kZeroGramForm q c).re :=
  @kZeroGramForm_pos

example : ∀ {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hinj : Function.Injective q) (c : ι → ℝ),
    c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * imaginaryOrderK 0 (q i + q j) :=
  @kZeroGram_real_pos

end ImbalancedChen.Part3.ActualKStrictGramSourceOnly
