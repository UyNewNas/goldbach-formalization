import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! The logarithmic coordinates and derivative bounds for the slow phase in (21). -/

namespace ImbalancedChen.Part3

open scoped BigOperators ContDiff SchwartzMap

noncomputable section

private def circlePhase (v : ℝ) : ℂ := fourier (1 : ℤ) (v : UnitAddCircle)

private theorem circlePhase_contDiff : ContDiff ℝ ∞ circlePhase := by
  have he : circlePhase = fun v : ℝ ↦ Complex.exp
      ((2 * Real.pi * Complex.I) * (v : ℂ)) := by
    funext v
    simp only [circlePhase, fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
  rw [he]
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

private theorem circlePhase_deriv : deriv circlePhase = fun v ↦
    (2 * Real.pi * Complex.I) * circlePhase v := by
  funext v
  have hd : HasDerivAt circlePhase ((2 * Real.pi * Complex.I) * circlePhase v) v := by
    change HasDerivAt (fun y : ℝ ↦ fourier (1 : ℤ) (y : UnitAddCircle)) _ v
    simpa only [circlePhase, Int.cast_one, Complex.ofReal_one, mul_one, div_one] using
      hasDerivAt_fourier (1 : ℝ) (1 : ℤ) v
  exact hd.deriv

private theorem circlePhase_iteratedDeriv (j : ℕ) :
    iteratedDeriv j circlePhase = fun v ↦ (2 * Real.pi * Complex.I) ^ j * circlePhase v := by
  induction j with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext v
    rw [deriv_const_mul_field, circlePhase_deriv, pow_succ]
    exact (mul_assoc _ _ _).symm

private theorem norm_circlePhase_iteratedFDeriv (j : ℕ) (v : ℝ) :
    ‖iteratedFDeriv ℝ j circlePhase v‖ = (2 * Real.pi) ^ j := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, circlePhase_iteratedDeriv,
    norm_mul, norm_pow]
  have hphase : ‖circlePhase v‖ = 1 := by
    simp only [circlePhase, fourier_apply, Circle.norm_coe]
  rw [hphase, mul_one]
  congr 1
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_iteratedFDeriv_linear_le (T : E →L[ℝ] ℝ)
    (x : E) (hx : |T x| ≤ 1) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z ↦ T z) x‖ ≤ (1 + ‖T‖) ^ i := by
  change ‖iteratedFDeriv ℝ i (id ∘ T) x‖ ≤ _
  rw [T.iteratedFDeriv_comp_right (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)) x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hnorm : ‖iteratedFDeriv ℝ i (@id ℝ) (T x)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_id]
    split_ifs <;> simp_all [Real.norm_eq_abs]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ 1 * ‖T‖ ^ i := mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      rw [one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) i

private theorem norm_iteratedFDeriv_exp_neg_linear_le (S : E →L[ℝ] ℝ)
    (x : E) (B : ℝ) (hx : Real.exp (-S x) ≤ B) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z ↦ Real.exp (-S z)) x‖ ≤ B * (1 + ‖S‖) ^ i := by
  let f : ℝ → ℝ := fun t ↦ Real.exp (-1 * t)
  have hf : ContDiff ℝ ∞ f := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hcomp : (fun z ↦ Real.exp (-S z)) = f ∘ S := by
    funext z
    simp only [Function.comp_apply, f, neg_mul, one_mul]
  rw [hcomp, S.iteratedFDeriv_comp_right hf x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hnorm : ‖iteratedFDeriv ℝ i f (S x)‖ ≤ B := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    dsimp only [f]
    rw [iteratedDeriv_exp_const_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, neg_mul, one_mul]
    exact hx
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ B * ‖S‖ ^ i := mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i)
        ((Real.exp_pos _).le.trans hx)

private def logPhaseArgument (A : ℝ) (T S : E →L[ℝ] ℝ) (x : E) :=
  A * T x * Real.exp (-S x)

private theorem logPhaseArgument_contDiff (A : ℝ) (T S : E →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (logPhaseArgument A T S) :=
  (contDiff_const.mul T.contDiff).mul (Real.contDiff_exp.comp S.contDiff.neg)

private theorem norm_iteratedFDeriv_logPhaseArgument_le (A : ℝ) (T S : E →L[ℝ] ℝ)
    (x : E) (hT : |T x| ≤ 1) (hS : 0 ≤ S x) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (logPhaseArgument A T S) x‖ ≤
      |A| * (2 * (1 + ‖T‖) * (1 + ‖S‖)) ^ i := by
  have hlin (j : ℕ) :
      ‖iteratedFDeriv ℝ j (fun z ↦ A * T z) x‖ ≤ |A| * (1 + ‖T‖) ^ j := by
    change ‖iteratedFDeriv ℝ j (fun z ↦ A • T z) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (T.contDiff.contDiffAt : ContDiffAt ℝ j T x),
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_linear_le T x hT j) (abs_nonneg A)
  have hsum : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (fun z ↦ A * T z) x‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun z ↦ Real.exp (-S z)) x‖ :=
      norm_iteratedFDeriv_mul_le
        (contDiff_const.mul T.contDiff : ContDiff ℝ ∞ _) (Real.contDiff_exp.comp S.contDiff.neg)
        x (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
         (|A| * (1 + ‖T‖) ^ i * (1 + ‖S‖) ^ i) := by
      apply Finset.sum_le_sum
      intro j hj
      have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 : ‖iteratedFDeriv ℝ j (fun z ↦ A * T z) x‖ ≤ |A| * (1 + ‖T‖) ^ i :=
        (hlin j).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by linarith [norm_nonneg T]) hji) (abs_nonneg A))
      have h2 : ‖iteratedFDeriv ℝ (i - j) (fun z ↦ Real.exp (-S z)) x‖ ≤ (1 + ‖S‖) ^ i :=
        (by
          simpa only [one_mul] using norm_iteratedFDeriv_exp_neg_linear_le S x 1
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hS)) (i - j) :
          ‖iteratedFDeriv ℝ (i - j) (fun z ↦ Real.exp (-S z)) x‖ ≤ (1 + ‖S‖) ^ (i - j)).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg S]) (Nat.sub_le _ _))
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul, hsum]
      simp only [mul_pow]
      ring

private theorem norm_iteratedFDeriv_comp_logArgument_le {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i : ℕ, i ≤ 5 → ∀ v, ‖iteratedFDeriv ℝ i g v‖ ≤ M)
    (A : ℝ) (T S : E →L[ℝ] ℝ)
    (x : E) (hT : |T x| ≤ 1) (hS : 0 ≤ S x) (j : ℕ) (hj : j ≤ 5) :
    ‖iteratedFDeriv ℝ j (g ∘ logPhaseArgument A T S) x‖ ≤
      ((5 : ℕ).factorial : ℝ) * M *
        (2 * (1 + ‖T‖) * (1 + ‖S‖)) ^ 5 * (1 + |A|) ^ j := by
  let K := 2 * (1 + ‖T‖) * (1 + ‖S‖)
  have hK : 1 ≤ K := by
    dsimp [K]
    have hT' : (1 : ℝ) ≤ 1 + ‖T‖ := by linarith [norm_nonneg T]
    have hS' : (1 : ℝ) ≤ 1 + ‖S‖ := by linarith [norm_nonneg S]
    calc
      1 ≤ 2 * (1 : ℝ) * 1 := by norm_num
      _ ≤ _ := by gcongr
  have h1A : 1 ≤ 1 + |A| := by linarith [abs_nonneg A]
  have hC (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i g (logPhaseArgument A T S x)‖ ≤ M :=
    hbound i (hi.trans hj) _
  have hD (i : ℕ) (hi : 1 ≤ i) (_ : i ≤ j) :
      ‖iteratedFDeriv ℝ i (logPhaseArgument A T S) x‖ ≤ (K * (1 + |A|)) ^ i := by
    rw [mul_pow]
    refine (norm_iteratedFDeriv_logPhaseArgument_le A T S x hT hS i).trans ?_
    rw [mul_comm |A|]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (le_add_of_nonneg_left zero_le_one).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ h1A hi)
  refine (norm_iteratedFDeriv_comp_le hg (logPhaseArgument_contDiff A T S)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j) x hC hD).trans ?_
  rw [mul_pow, ← mul_assoc]
  have hjfact : (j.factorial : ℝ) ≤ (5 : ℕ).factorial := by
    exact_mod_cast Nat.factorial_le hj
  gcongr

private theorem e2LogPhase_generic_iteratedFDeriv_le (A : ℝ) (T S : E →L[ℝ] ℝ)
    (x : E) (hT : |T x| ≤ 1) (hS : 0 ≤ S x) (j : ℕ) (hj : j ≤ 5) :
    ‖iteratedFDeriv ℝ j (circlePhase ∘ logPhaseArgument A T S) x‖ ≤
      ((5 : ℕ).factorial : ℝ) * (1 + 2 * Real.pi) ^ 5 *
        (2 * (1 + ‖T‖) * (1 + ‖S‖)) ^ 5 * (1 + |A|) ^ j := by
  refine norm_iteratedFDeriv_comp_logArgument_le circlePhase_contDiff (by positivity)
    (fun i hi v ↦ ?_) A T S x hT hS j hj
  rw [norm_circlePhase_iteratedFDeriv]
  exact (pow_le_pow_left₀ (by positivity) (by linarith) i).trans
    (pow_le_pow_right₀ (by linarith [Real.pi_pos]) hi)

private def frequencyCoord : ((Fin 4 → ℝ) × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ (Fin 4 → ℝ) ℝ

private def logSumCoord : ((Fin 4 → ℝ) × ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin 4, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin 4 → ℝ) ℝ)

private theorem logSumCoord_apply (x : (Fin 4 → ℝ) × ℝ) :
    logSumCoord x = ∑ i : Fin 4, x.1 i := by
  simp [logSumCoord]

/-- The four logarithms of the positive dyadic coordinates and the signed frequency. -/
def e2LogPhase (A : ℝ) (x : (Fin 4 → ℝ) × ℝ) : ℂ :=
  fourier (1 : ℤ) (((A * x.2 * Real.exp (-(∑ i : Fin 4, x.1 i))) : ℝ) : UnitAddCircle)

private theorem e2LogPhase_eq_comp (A : ℝ) :
    e2LogPhase A = circlePhase ∘ logPhaseArgument A frequencyCoord logSumCoord := by
  funext x
  simp only [e2LogPhase, Function.comp_apply, circlePhase, logPhaseArgument, frequencyCoord,
    logSumCoord_apply]
  rfl

theorem e2LogPhase_contDiff (A : ℝ) : ContDiff ℝ ∞ (e2LogPhase A) := by
  rw [e2LogPhase_eq_comp]
  exact circlePhase_contDiff.comp (logPhaseArgument_contDiff A frequencyCoord logSumCoord)

/-- On the normalized rectangle, every derivative through order five costs
at most a fixed constant times one plus the amplitude raised to the derivative order. -/
theorem e2LogPhase_iteratedFDeriv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ) (x : (Fin 4 → ℝ) × ℝ) (j : ℕ),
      (∀ i, 0 ≤ x.1 i) → |x.2| ≤ 1 → j ≤ 5 →
      ‖iteratedFDeriv ℝ j (e2LogPhase A) x‖ ≤ C * (1 + |A|) ^ j := by
  refine ⟨((5 : ℕ).factorial : ℝ) * (1 + 2 * Real.pi) ^ 5 *
      (2 * (1 + ‖frequencyCoord‖) * (1 + ‖logSumCoord‖)) ^ 5, by positivity, ?_⟩
  intro A x j hx hfreq hj
  rw [e2LogPhase_eq_comp]
  refine e2LogPhase_generic_iteratedFDeriv_le A frequencyCoord logSumCoord x hfreq ?_ j hj
  rw [logSumCoord_apply]
  exact Finset.sum_nonneg fun i _ ↦ hx i

private def firstLogCoord : ((Fin 4 → ℝ) × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) 0).comp
    (ContinuousLinearMap.fst ℝ (Fin 4 → ℝ) ℝ)

private def firstThreeLogSumCoord : ((Fin 4 → ℝ) × ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin 3, ContinuousLinearMap.proj
    (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) (Fin.castSucc i)).comp
    (ContinuousLinearMap.fst ℝ (Fin 4 → ℝ) ℝ)

private theorem firstThreeLogSumCoord_apply (x : (Fin 4 → ℝ) × ℝ) :
    firstThreeLogSumCoord x = ∑ i : Fin 3, x.1 (Fin.castSucc i) := by
  simp [firstThreeLogSumCoord]

private def qWeightArgument (b : ℝ) (x : (Fin 4 → ℝ) × ℝ) : ℝ :=
  b * Real.exp (firstLogCoord x)

private theorem qWeightArgument_contDiff (b : ℝ) : ContDiff ℝ ∞ (qWeightArgument b) :=
  contDiff_const.mul (Real.contDiff_exp.comp firstLogCoord.contDiff)

private theorem norm_iteratedFDeriv_qWeightArgument_le (b : ℝ) (hb : |b| ≤ 2)
    (x : (Fin 4 → ℝ) × ℝ) (hx : x.1 0 ≤ Real.log 2) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (qWeightArgument b) x‖ ≤ (4 * (1 + ‖firstLogCoord‖)) ^ i := by
  have hexp : Real.exp (firstLogCoord x) ≤ 2 := by
    change Real.exp (x.1 0) ≤ 2
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hx
  have hbase := norm_iteratedFDeriv_exp_neg_linear_le (-firstLogCoord) x 2 (by simpa using hexp) i
  have hnorm : ‖iteratedFDeriv ℝ i (fun z ↦ Real.exp (firstLogCoord z)) x‖ ≤
      2 * (1 + ‖firstLogCoord‖) ^ i := by
    simpa only [neg_apply, neg_neg, norm_neg] using hbase
  change ‖iteratedFDeriv ℝ i (fun z ↦ b • Real.exp (firstLogCoord z)) x‖ ≤ _
  have hExpS : ContDiff ℝ i (fun z ↦ Real.exp (firstLogCoord z)) :=
    Real.contDiff_exp.comp firstLogCoord.contDiff
  rw [iteratedFDeriv_const_smul_apply' hExpS.contDiffAt, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 2 * (2 * (1 + ‖firstLogCoord‖) ^ i) :=
      mul_le_mul hb hnorm (norm_nonneg _) (by norm_num)
    _ = 4 * (1 + ‖firstLogCoord‖) ^ i := by ring
    _ ≤ (4 : ℝ) ^ i * (1 + ‖firstLogCoord‖) ^ i := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hi)
        (by positivity)
    _ = _ := by rw [mul_pow]

private def derivativeBound (f : 𝓢(ℝ, ℂ)) : ℝ :=
  1 + ∑ i ∈ Finset.range 6, SchwartzMap.seminorm ℝ 0 i f

private theorem derivativeBound_pos (f : 𝓢(ℝ, ℂ)) : 0 < derivativeBound f := by
  unfold derivativeBound
  exact add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun _ _ ↦ apply_nonneg _ _))

private theorem norm_iteratedFDeriv_le_derivativeBound (f : 𝓢(ℝ, ℂ))
    (i : ℕ) (hi : i ≤ 5) (x : ℝ) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ derivativeBound f := by
  have h := SchwartzMap.le_seminorm ℝ 0 i f x
  simp only [pow_zero, one_mul] at h
  have hs : SchwartzMap.seminorm ℝ 0 i f ≤
      ∑ j ∈ Finset.range 6, SchwartzMap.seminorm ℝ 0 j f :=
    Finset.single_le_sum (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
  exact h.trans (hs.trans (le_add_of_nonneg_left zero_le_one))

private theorem norm_iteratedFDeriv_mul_order_le {f g : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E)
    {Cf Cg B : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hB : 0 ≤ B) (j : ℕ) (hj : j ≤ 5)
    (h1 : ∀ i : ℕ, i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ Cf * B ^ i)
    (h2 : ∀ i : ℕ, i ≤ j → ‖iteratedFDeriv ℝ i g x‖ ≤ Cg * B ^ i) :
    ‖iteratedFDeriv ℝ j (fun z ↦ f z * g z) x‖ ≤ (2 ^ 5 * Cf * Cg) * B ^ j := by
  have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Cf * Cg * B ^ j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        _ ≤ (Cf * B ^ i) * (Cg * B ^ (j - i)) :=
          mul_le_mul (h1 i hij) (h2 (j - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
        _ = Cf * Cg * (B ^ i * B ^ (j - i)) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hij]
    _ = 2 ^ j * (Cf * Cg * B ^ j) := by rw [← Finset.sum_mul, hsum]
    _ ≤ (2 : ℝ) ^ 5 * (Cf * Cg * B ^ j) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) (by positivity)
    _ = _ := by ring

/-- The full smooth weight removed by summation by parts in (22). The cutoff
and its Fourier transform are evaluated on their respective original arguments. -/
def e2LogWeight (ψ ψhat : ℝ → ℂ) (b L A : ℝ) (x : (Fin 4 → ℝ) × ℝ) : ℂ :=
  ψ (qWeightArgument b x) *
    ψhat (logPhaseArgument L frequencyCoord firstThreeLogSumCoord x) * e2LogPhase A x

theorem e2LogWeight_contDiff (ψ ψhat : ℝ → ℂ) (b L A : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψhat : ContDiff ℝ ∞ ψhat) :
    ContDiff ℝ ∞ (e2LogWeight ψ ψhat b L A) :=
  ((hψ.comp (qWeightArgument_contDiff b)).mul
    (hψhat.comp (logPhaseArgument_contDiff L frequencyCoord firstThreeLogSumCoord))).mul
      (e2LogPhase_contDiff A)

/-- The derivative cost is polynomial in the two scaled Fourier arguments.
The degree is the derivative order, uniformly up to five. -/
theorem e2LogWeight_iteratedFDeriv_le (ψ ψhat : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b L A : ℝ) (x : (Fin 4 → ℝ) × ℝ) (j : ℕ),
      |b| ≤ 2 → (∀ i, 0 ≤ x.1 i) → x.1 0 ≤ Real.log 2 → |x.2| ≤ 1 → j ≤ 5 →
      ‖iteratedFDeriv ℝ j (e2LogWeight ψ ψhat b L A) x‖ ≤ C * (1 + |L| + |A|) ^ j := by
  let Cq := ((5 : ℕ).factorial : ℝ) * derivativeBound ψ * (4 * (1 + ‖firstLogCoord‖)) ^ 5
  let CL := ((5 : ℕ).factorial : ℝ) * derivativeBound ψhat *
    (2 * (1 + ‖frequencyCoord‖) * (1 + ‖firstThreeLogSumCoord‖)) ^ 5
  obtain ⟨CA, hCA, hphase⟩ := e2LogPhase_iteratedFDeriv_le
  have hCq : 0 < Cq := by unfold Cq; positivity [derivativeBound_pos ψ]
  have hCL : 0 < CL := by unfold CL; positivity [derivativeBound_pos ψhat]
  refine ⟨2 ^ 5 * (2 ^ 5 * Cq * CL) * CA, by positivity, ?_⟩
  intro b L A x j hb hlog hfirst hfreq hj
  let B := 1 + |L| + |A|
  have hB : 1 ≤ B := by
    dsimp only [B]
    linarith [abs_nonneg L, abs_nonneg A]
  have hLB : 1 + |L| ≤ B := le_add_of_nonneg_right (abs_nonneg A)
  have hAB : 1 + |A| ≤ B := by
    dsimp only [B]
    linarith [abs_nonneg L]
  let f : ((Fin 4 → ℝ) × ℝ) → ℂ := ψ ∘ qWeightArgument b
  let g : ((Fin 4 → ℝ) × ℝ) → ℂ := ψhat ∘ logPhaseArgument L frequencyCoord firstThreeLogSumCoord
  have hf : ContDiff ℝ ∞ f := (ψ.smooth _).comp (qWeightArgument_contDiff b)
  have hg : ContDiff ℝ ∞ g :=
    (ψhat.smooth _).comp (logPhaseArgument_contDiff L frequencyCoord firstThreeLogSumCoord)
  have hfD (i : ℕ) (hi : i ≤ 5) : ‖iteratedFDeriv ℝ i f x‖ ≤ Cq * B ^ i := by
    have hcomp := norm_iteratedFDeriv_comp_le (ψ.smooth (⊤ : ℕ∞)) (qWeightArgument_contDiff b)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i) x
      (fun k hk ↦ norm_iteratedFDeriv_le_derivativeBound ψ k (hk.trans hi) _)
      (fun k hk _ ↦ norm_iteratedFDeriv_qWeightArgument_le b hb x hfirst k hk)
    change ‖iteratedFDeriv ℝ i f x‖ ≤ _ at hcomp
    refine hcomp.trans (le_trans ?_ (le_mul_of_one_le_right hCq.le (one_le_pow₀ hB)))
    dsimp only [Cq]
    have hfact : (i.factorial : ℝ) ≤ (5 : ℕ).factorial := by exact_mod_cast Nat.factorial_le hi
    have hbase : 1 ≤ 4 * (1 + ‖firstLogCoord‖) := by linarith [norm_nonneg firstLogCoord]
    gcongr <;> positivity [derivativeBound_pos ψ]
  have hgD (i : ℕ) (hi : i ≤ 5) : ‖iteratedFDeriv ℝ i g x‖ ≤ CL * B ^ i := by
    have hs : 0 ≤ firstThreeLogSumCoord x := by
      rw [firstThreeLogSumCoord_apply]
      exact Finset.sum_nonneg fun k _ ↦ hlog (Fin.castSucc k)
    exact (norm_iteratedFDeriv_comp_logArgument_le (ψhat.smooth _) (derivativeBound_pos ψhat).le
      (norm_iteratedFDeriv_le_derivativeBound ψhat) L frequencyCoord firstThreeLogSumCoord x
      hfreq hs i hi).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLB i) hCL.le)
  change ‖iteratedFDeriv ℝ j (fun z ↦ (f z * g z) * e2LogPhase A z) x‖ ≤ _
  exact norm_iteratedFDeriv_mul_order_le (hf.mul hg) (e2LogPhase_contDiff A) x
    (by positivity) hCA.le (zero_le_one.trans hB) j hj
    (fun i hi ↦ norm_iteratedFDeriv_mul_order_le hf hg x hCq.le hCL.le (zero_le_one.trans hB)
      i (hi.trans hj) (fun k hk ↦ hfD k (hk.trans (hi.trans hj)))
      (fun k hk ↦ hgD k (hk.trans (hi.trans hj))))
    (fun i hi ↦ (hphase A x i hlog hfreq (hi.trans hj)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hAB i) hCA.le))

/-- Writing the normalized physical coordinates without logarithms gives the
cutoff, Fourier cutoff, and retained phase of the frozen E2 weight. -/
theorem e2LogWeight_at_normalized (ψ ψhat : ℝ → ℂ) (b L A t : ℝ)
    (v : Fin 4 → ℝ) (hv : ∀ i, 0 < v i) :
    e2LogWeight ψ ψhat b L A ((fun i ↦ Real.log (v i)), t) =
      ψ (b * v 0) * ψhat (L * t / (v 0 * v 1 * v 2)) *
        fourier (1 : ℤ) (((A * t / (v 0 * v 1 * v 2 * v 3)) : ℝ) : UnitAddCircle) := by
  have hq : qWeightArgument b ((fun i ↦ Real.log (v i)), t) = b * v 0 := by
    change b * Real.exp (Real.log (v 0)) = b * v 0
    rw [Real.exp_log (hv 0)]
  have hthree :
      Real.exp (-(∑ i : Fin 3, Real.log (v (Fin.castSucc i)))) = (v 0 * v 1 * v 2)⁻¹ := by
    rw [Fin.sum_univ_three]
    change Real.exp (-(Real.log (v 0) + Real.log (v 1) + Real.log (v 2))) = _
    rw [Real.exp_neg, Real.exp_add, Real.exp_add]
    simp only [Real.exp_log (hv 0), Real.exp_log (hv 1), Real.exp_log (hv 2)]
  have hfour : Real.exp (-(∑ i : Fin 4, Real.log (v i))) = (v 0 * v 1 * v 2 * v 3)⁻¹ := by
    rw [Fin.sum_univ_four, Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_add]
    simp only [Real.exp_log (hv 0), Real.exp_log (hv 1), Real.exp_log (hv 2), Real.exp_log (hv 3)]
  simp only [e2LogWeight, hq, e2LogPhase, logPhaseArgument, frequencyCoord,
    firstThreeLogSumCoord_apply, ContinuousLinearMap.coe_snd', hthree, hfour, div_eq_mul_inv]

/-- The logged weight equals the original weight with its physical modulus,
Fourier scale, and exact retained slow phase. The frequency and residue stay signed. -/
theorem e2LogWeight_at_physical (ψ ψhat : ℝ → ℂ)
    (q₀ Q R N H M a d q w₁ w₂ n₁ h : ℝ)
    (hq₀ : 0 < q₀) (hQ : 0 < Q) (hR : 0 < R) (hN : 0 < N) (hH : 0 < H)
    (hd : 0 < d) (hq : 0 < q) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hn₁ : 0 < n₁) :
    e2LogWeight ψ ψhat (q₀ / Q) (H * M / (q₀ * d * R ^ 2))
        (a * H / (q₀ * d * R ^ 2 * N))
        ((fun i : Fin 4 ↦ Real.log (![q / q₀, w₁ / R, w₂ / R, n₁ / N] i)), h / H) =
      ψ (q / Q) * ψhat (h * M / (q * d * w₁ * w₂)) *
        fourier (1 : ℤ) (((a * h / (q * d * w₁ * w₂ * n₁)) : ℝ) : UnitAddCircle) := by
  let v : Fin 4 → ℝ := ![q / q₀, w₁ / R, w₂ / R, n₁ / N]
  have hv : ∀ i, 0 < v i := by
    intro i
    fin_cases i <;> dsimp [v] <;> positivity
  rw [e2LogWeight_at_normalized ψ ψhat _ _ _ _ v hv]
  change ψ (q₀ / Q * (q / q₀)) *
      ψhat (H * M / (q₀ * d * R ^ 2) * (h / H) / (q / q₀ * (w₁ / R) * (w₂ / R))) *
      fourier (1 : ℤ) (((a * H / (q₀ * d * R ^ 2 * N) * (h / H) /
        (q / q₀ * (w₁ / R) * (w₂ / R) * (n₁ / N))) : ℝ) : UnitAddCircle) = _
  have hqarg : q₀ / Q * (q / q₀) = q / Q := by
    field_simp [hq₀.ne', hQ.ne']
  have hL : H * M / (q₀ * d * R ^ 2) * (h / H) / (q / q₀ * (w₁ / R) * (w₂ / R)) =
      h * M / (q * d * w₁ * w₂) := by
    field_simp [hq₀.ne', hd.ne', hR.ne', hH.ne', hq.ne', hw₁.ne', hw₂.ne']
  have hA : a * H / (q₀ * d * R ^ 2 * N) * (h / H) /
      (q / q₀ * (w₁ / R) * (w₂ / R) * (n₁ / N)) = a * h / (q * d * w₁ * w₂ * n₁) := by
    field_simp [hq₀.ne', hd.ne', hR.ne', hN.ne', hH.ne', hq.ne', hw₁.ne', hw₂.ne', hn₁.ne']
  rw [hqarg, hL, hA]

/-- A fixed logarithmic cutoff consumes an arbitrary positive slack in the
exponent. The fifth power of the moving-residue growth stays in the bound. -/
theorem e2LogWeight_amplitude_budget {X κ ε C₀ L A : ℝ}
    (hX : 1 ≤ X) (hκ : 0 ≤ κ) (hε : 0 < ε) (hC₀ : 0 ≤ C₀)
    (hL : |L| ≤ C₀ * (Real.log X) ^ 5)
    (hA : |A| ≤ C₀ * X ^ κ * (Real.log X) ^ 5) :
    (1 + |L| + |A|) ^ 5 ≤ (1 + 2 * C₀ * (25 / ε) ^ 5) ^ 5 * X ^ (5 * κ + ε) := by
  have hX0 := zero_lt_one.trans_le hX
  have hlog := Real.log_le_rpow_div hX0.le (show 0 < ε / 25 by positivity)
  have hlog' : Real.log X ≤ (25 / ε) * X ^ (ε / 25) := by
    convert hlog using 1
    field_simp
  have hlog5 : (Real.log X) ^ 5 ≤ (25 / ε) ^ 5 * X ^ (ε / 5) := by
    calc
      _ ≤ ((25 / ε) * X ^ (ε / 25)) ^ 5 :=
        pow_le_pow_left₀ (Real.log_nonneg hX) hlog' 5
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hX0.le, Nat.cast_ofNat,
          show ε / 25 * 5 = ε / 5 by ring]
  let U := X ^ (κ + ε / 5)
  let D := C₀ * (25 / ε) ^ 5
  have hD : 0 ≤ D := by unfold D; positivity
  have hU1 : 1 ≤ U := Real.one_le_rpow hX (by positivity)
  have hLU : |L| ≤ D * U := by
    refine hL.trans ((mul_le_mul_of_nonneg_left hlog5 hC₀).trans ?_)
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hD
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hAU : |A| ≤ D * U := by
    refine hA.trans ((mul_le_mul_of_nonneg_left hlog5 (by positivity)).trans_eq ?_)
    dsimp only [D, U]
    rw [Real.rpow_add hX0]
    ring
  have hs : 1 + |L| + |A| ≤ (1 + 2 * D) * U := by
    nlinarith only [hLU, hAU, hU1]
  refine (pow_le_pow_left₀ (by positivity) hs 5).trans_eq ?_
  dsimp only [D, U]
  rw [mul_pow, ← Real.rpow_mul_natCast hX0.le, Nat.cast_ofNat,
    show (κ + ε / 5) * 5 = 5 * κ + ε by ring]
  ring

/-- The original frequency cutoff gives the two dimensionless Fourier
parameters on one positive dyadic box. -/
theorem e2LogWeight_physicalParameters_le {X M N Q D R q₀ d H a κ Cq Cd : ℝ}
    (hX : 1 ≤ X) (hscale : X = N * M)
    (hM : 0 < M) (hN : 0 < N) (hq₀ : 0 < q₀) (hd : 0 < d) (hR : 0 < R)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hCq : 0 ≤ Cq)
    (hqRatio : Q / q₀ ≤ Cq) (hdRatio : D / d ≤ Cd)
    (hHcut : H ≤ Q * D * R ^ 2 * (Real.log X) ^ 5 / M) (ha : |a| ≤ X ^ (1 + κ)) :
    |H * M / (q₀ * d * R ^ 2)| ≤ Cq * Cd * (Real.log X) ^ 5 ∧
      |a * H / (q₀ * d * R ^ 2 * N)| ≤ Cq * Cd * X ^ κ * (Real.log X) ^ 5 := by
  let L := H * M / (q₀ * d * R ^ 2)
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hlog : 0 ≤ (Real.log X) ^ 5 := pow_nonneg (Real.log_nonneg hX) _
  have hL : L ≤ Cq * Cd * (Real.log X) ^ 5 := by
    dsimp only [L]
    calc
      _ ≤ Q * D * R ^ 2 * (Real.log X) ^ 5 / (q₀ * d * R ^ 2) :=
        div_le_div_of_nonneg_right ((le_div_iff₀ hM).mp hHcut) (by positivity)
      _ = (Q / q₀) * (D / d) * (Real.log X) ^ 5 := by
        field_simp [hq₀.ne', hd.ne', hR.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hqRatio hdRatio (div_nonneg hD hd.le) hCq) hlog
  have hX0 := zero_lt_one.trans_le hX
  have haX : |a| / X ≤ X ^ κ := by
    apply (div_le_iff₀ hX0).mpr
    rwa [Real.rpow_add hX0, Real.rpow_one, mul_comm] at ha
  have hA : |a * H / (q₀ * d * R ^ 2 * N)| = (|a| / X) * L := by
    simp only [abs_div, abs_mul, abs_of_nonneg hH,
      abs_of_pos (show 0 < q₀ * d * R ^ 2 * N by positivity)]
    rw [hscale]
    dsimp only [L]
    field_simp [hN.ne', hM.ne', hq₀.ne', hd.ne', hR.ne']
  refine ⟨(abs_of_nonneg hL0).trans_le hL, ?_⟩
  rw [hA]
  exact (mul_le_mul haX hL hL0 (by positivity)).trans_eq (by ring)

end

end ImbalancedChen.Part3
