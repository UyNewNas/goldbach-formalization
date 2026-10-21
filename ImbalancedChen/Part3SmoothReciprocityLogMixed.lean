import ImbalancedChen.Part3SmoothReciprocityProfile
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Mixed logarithmic derivatives of the literal smooth profile

All vectors and the compact smooth localizer are fixed before the constant is
chosen. The atom parameters and the cutoff scale are quantified afterwards.
The estimate is for the operator norm of the genuine iterated Fréchet
derivative. In particular it controls every coordinate word of the same length.

The proof uses pointwise composition estimates, not a temperate-growth claim
for an exponential monomial. Schwartz decay pays every power of its signed
argument introduced by the chain rule, including the powers from the phase.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators SchwartzMap FourierTransform ContDiff
open CommonSmoothCutoff

/-- The actual profile in fixed logarithmic monomial coordinates. -/
def CommonSmoothCutoff.smoothReciprocityLogWeight {d : ℕ}
    (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ) (Z u₀ rho₀ : ℝ)
    (t : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Q t * (Real.exp (inner ℝ c t) : ℂ) *
    smoothReciprocityProfile Z (rho₀ * Real.exp (inner ℝ b t))
      (u₀ * Real.exp (inner ℝ a t))

namespace SmoothReciprocityLogMixedProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def monomial (A : E →L[ℝ] ℝ) (u₀ : ℝ) (t : E) : ℝ :=
  u₀ * Real.exp (A t)

private theorem monomial_smooth (A : E →L[ℝ] ℝ) (u₀ : ℝ) :
    ContDiff ℝ ∞ (monomial A u₀) :=
  contDiff_const.mul (Real.contDiff_exp.comp A.contDiff)

private theorem monomial_deriv_le (A : E →L[ℝ] ℝ) (u₀ : ℝ)
    (i : ℕ) (t : E) :
    ‖iteratedFDeriv ℝ i (monomial A u₀) t‖ ≤
      |monomial A u₀ t| * ‖A‖ ^ i := by
  let f : ℝ → ℝ := fun s ↦ u₀ * Real.exp s
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul Real.contDiff_exp
  have he (s : ℝ) : iteratedDeriv i Real.exp s = Real.exp s := by
    simpa only [one_mul, one_pow] using
      congrFun (iteratedDeriv_exp_const_mul i 1) s
  have hn : ‖iteratedFDeriv ℝ i f (A t)‖ = |monomial A u₀ t| := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp only [f, iteratedDeriv_const_mul_field, he, Real.norm_eq_abs, monomial]
  change ‖iteratedFDeriv ℝ i (f ∘ A) t‖ ≤ _
  rw [A.iteratedFDeriv_comp_right hf t
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)]
  calc
    ‖(iteratedFDeriv ℝ i f (A t)).compContinuousLinearMap (fun _ ↦ A)‖ ≤
        ‖iteratedFDeriv ℝ i f (A t)‖ * ∏ _ : Fin i, ‖A‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = |monomial A u₀ t| * ‖A‖ ^ i := by simp only [hn, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]

private theorem monomial_deriv_power (A : E →L[ℝ] ℝ) (u₀ : ℝ)
    (i : ℕ) (hi : 1 ≤ i) (t : E) :
    ‖iteratedFDeriv ℝ i (monomial A u₀) t‖ ≤
      ((1 + ‖A‖) * (1 + |monomial A u₀ t|)) ^ i := by
  have hpow : |monomial A u₀ t| ≤ (1 + |monomial A u₀ t|) ^ i := by
    calc
      |monomial A u₀ t| ≤ 1 + |monomial A u₀ t| := by linarith
      _ = (1 + |monomial A u₀ t|) ^ 1 := (pow_one _).symm
      _ ≤ (1 + |monomial A u₀ t|) ^ i :=
        pow_le_pow_right₀ (by linarith [abs_nonneg (monomial A u₀ t)]) hi
  calc
    ‖iteratedFDeriv ℝ i (monomial A u₀) t‖ ≤
        |monomial A u₀ t| * ‖A‖ ^ i := monomial_deriv_le A u₀ i t
    _ ≤ (1 + |monomial A u₀ t|) ^ i * (1 + ‖A‖) ^ i :=
      mul_le_mul hpow (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i)
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = ((1 + ‖A‖) * (1 + |monomial A u₀ t|)) ^ i := by
      rw [mul_pow, mul_comm]

private def schwartzBound (f : 𝓢(ℝ, ℂ)) (r J : ℕ) : ℝ :=
  2 ^ r * (Finset.Iic (r, J)).sup
    (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f

private theorem schwartzBound_nonneg (f : 𝓢(ℝ, ℂ)) (r J : ℕ) :
    0 ≤ schwartzBound f r J := by
  unfold schwartzBound
  positivity

private def compositionBound (f : 𝓢(ℝ, ℂ)) (A : E →L[ℝ] ℝ)
    (r J : ℕ) : ℝ :=
  J.factorial * schwartzBound f (r + J) J * (1 + ‖A‖) ^ J

private theorem compositionBound_nonneg (f : 𝓢(ℝ, ℂ))
    (A : E →L[ℝ] ℝ) (r J : ℕ) : 0 ≤ compositionBound f A r J := by
  unfold compositionBound
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (schwartzBound_nonneg _ _ _)) (by positivity)

/-- The extra outer Schwartz weight pays the full pointwise chain-rule cost. -/
private theorem schwartz_monomial_deriv_weighted (f : 𝓢(ℝ, ℂ))
    (A : E →L[ℝ] ℝ) (u₀ : ℝ) (r J j : ℕ) (hj : j ≤ J) (t : E) :
    (1 + |monomial A u₀ t|) ^ r *
        ‖iteratedFDeriv ℝ j (fun s ↦ f (monomial A u₀ s)) t‖ ≤
      compositionBound f A r J := by
  let w : ℝ := 1 + |monomial A u₀ t|
  let B : ℝ := schwartzBound f (r + J) J
  have hw : 0 < w := by dsimp [w]; positivity
  have hB : 0 ≤ B := schwartzBound_nonneg _ _ _
  have houter (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i f (monomial A u₀ t)‖ ≤ B / w ^ (r + j) := by
    apply (le_div_iff₀ (pow_pos hw _)).2
    rw [mul_comm]
    simpa only [w, B, schwartzBound, Real.norm_eq_abs] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (r + J, J)) (Nat.add_le_add_left hj r) (hi.trans hj)
        f (monomial A u₀ t))
  have hcomp := norm_iteratedFDeriv_comp_le (f.smooth (⊤ : ℕ∞))
    (monomial_smooth A u₀) (ENat.natCast_le_of_coe_top_le_withTop le_rfl j) t houter
    (fun i hi _ ↦ monomial_deriv_power A u₀ i hi t)
  calc
    w ^ r * ‖iteratedFDeriv ℝ j (fun s ↦ f (monomial A u₀ s)) t‖ ≤
        w ^ r * (j.factorial * (B / w ^ (r + j)) *
          ((1 + ‖A‖) * w) ^ j) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = (j.factorial * B * (1 + ‖A‖) ^ j) *
        (w ^ r * w ^ j / w ^ (r + j)) := by rw [mul_pow]; ring
    _ = j.factorial * B * (1 + ‖A‖) ^ j := by
      rw [← pow_add, div_self (pow_ne_zero _ hw.ne'), mul_one]
    _ ≤ J.factorial * B * (1 + ‖A‖) ^ J := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.factorial_le hj) hB
      · exact pow_le_pow_right₀ (by linarith [norm_nonneg A]) hj
      · positivity
      · positivity
    _ = compositionBound f A r J := rfl

private def cutoffAffine (x : ℝ) : ℝ := 3 / 2 + x / 2

private theorem cutoffAffine_growth : cutoffAffine.HasTemperateGrowth := by
  unfold cutoffAffine
  simp only [div_eq_mul_inv]
  fun_prop

private theorem cutoffAffine_proper :
    ∃ k : ℕ, ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖cutoffAffine x‖) ^ k := by
  refine ⟨1, 4, fun x ↦ ?_⟩
  have he : x = 2 * cutoffAffine x - 3 := by unfold cutoffAffine; ring
  have hx : |x| ≤ 2 * |cutoffAffine x| + 3 := by
    calc
      |x| = |2 * cutoffAffine x - 3| := congrArg abs he
      _ ≤ |2 * cutoffAffine x| + |(3 : ℝ)| := abs_sub _ _
      _ = 2 * |cutoffAffine x| + 3 := by rw [abs_mul]; norm_num
  simp only [Real.norm_eq_abs, pow_one]
  linarith [abs_nonneg (cutoffAffine x)]

private def cutoffSchwartz : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ cutoffAffine_growth cutoffAffine_proper dyadicCutoffSchwartz

private theorem cutoffSchwartz_apply (x : ℝ) :
    cutoffSchwartz x = (poissonSmoothLowPass x : ℂ) := by
  simp only [cutoffSchwartz, SchwartzMap.compCLM_apply, Function.comp_apply,
    dyadicCutoffSchwartz_apply, cutoffAffine, dyadicCutoff, poissonSmoothLowPass]

private def phase (v : ℝ) : ℂ := fourier (1 : ℤ) (v : UnitAddCircle)

private theorem phase_smooth : ContDiff ℝ ∞ phase := by
  have he : phase = fun v : ℝ ↦ Complex.exp
      ((2 * Real.pi * Complex.I) * (v : ℂ)) := by
    funext v
    simp only [phase, fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
  rw [he]
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)

private theorem phase_hasDerivAt (v : ℝ) :
    HasDerivAt phase ((2 * Real.pi * Complex.I) * phase v) v := by
  change HasDerivAt
    (fun y : Real => fourier (1 : Int) (y : UnitAddCircle))
    ((2 * Real.pi * Complex.I) * fourier (1 : Int) (v : UnitAddCircle)) v
  simpa only [Int.cast_one, Complex.ofReal_one, mul_one, div_one] using
    hasDerivAt_fourier (1 : Real) (1 : Int) v

private theorem phase_deriv : deriv phase = fun v ↦
    (2 * Real.pi * Complex.I) * phase v := by
  funext v
  exact (phase_hasDerivAt v).deriv

private theorem phase_iteratedDeriv (j : ℕ) :
    iteratedDeriv j phase = fun v ↦ (2 * Real.pi * Complex.I) ^ j * phase v := by
  induction j with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext v
      rw [deriv_const_mul_field, phase_deriv, pow_succ]
      exact (mul_assoc _ _ _).symm

private theorem phase_deriv_norm (j : ℕ) (v : ℝ) :
    ‖iteratedFDeriv ℝ j phase v‖ = (2 * Real.pi) ^ j := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, phase_iteratedDeriv,
    norm_mul, norm_pow]
  have hphase : ‖phase v‖ = 1 := by
    simp only [phase, fourier_apply, Circle.norm_coe]
  rw [hphase, mul_one]
  congr 1
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

private def phaseBound (A : E →L[ℝ] ℝ) (J : ℕ) : ℝ :=
  J.factorial * (1 + 2 * Real.pi) ^ J * (1 + ‖A‖) ^ J

private theorem phaseBound_nonneg (A : E →L[ℝ] ℝ) (J : ℕ) :
    0 ≤ phaseBound A J := by unfold phaseBound; positivity

private theorem phase_monomial_deriv (A : E →L[ℝ] ℝ) (v₀ : ℝ)
    (J j : ℕ) (hj : j ≤ J) (t : E) :
    ‖iteratedFDeriv ℝ j (fun s ↦ phase (monomial A v₀ s)) t‖ ≤
      phaseBound A J * (1 + |monomial A v₀ t|) ^ j := by
  have houter (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i phase (monomial A v₀ t)‖ ≤ (1 + 2 * Real.pi) ^ J := by
    rw [phase_deriv_norm]
    exact (pow_le_pow_left₀ (by positivity) (by linarith) i).trans
      (pow_le_pow_right₀ (by linarith [Real.pi_pos]) (hi.trans hj))
  have hcomp := norm_iteratedFDeriv_comp_le phase_smooth
    (monomial_smooth A v₀) (ENat.natCast_le_of_coe_top_le_withTop le_rfl j) t houter
    (fun i hi _ ↦ monomial_deriv_power A v₀ i hi t)
  calc
    ‖iteratedFDeriv ℝ j (fun s ↦ phase (monomial A v₀ s)) t‖ ≤
        j.factorial * (1 + 2 * Real.pi) ^ J *
          ((1 + ‖A‖) * (1 + |monomial A v₀ t|)) ^ j := hcomp
    _ = (j.factorial * (1 + 2 * Real.pi) ^ J * (1 + ‖A‖) ^ j) *
        (1 + |monomial A v₀ t|) ^ j := by rw [mul_pow]; ring
    _ ≤ phaseBound A J * (1 + |monomial A v₀ t|) ^ j := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold phaseBound
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.factorial_le hj) (by positivity)
      · exact pow_le_pow_right₀ (by linarith [norm_nonneg A]) hj
      · positivity
      · positivity

/-- A bounded smooth multiplier preserves the weighted bound at every order. -/
private theorem weighted_mul_bound {f g : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (J r : ℕ) (w Cf Cg : ℝ) (hw : 0 ≤ w) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (t : E) (hleft : ∀ i ≤ J, ‖iteratedFDeriv ℝ i f t‖ ≤ Cf)
    (hright : ∀ i ≤ J, w ^ r * ‖iteratedFDeriv ℝ i g t‖ ≤ Cg)
    (j : ℕ) (hj : j ≤ J) :
    w ^ r * ‖iteratedFDeriv ℝ j (fun s ↦ f s * g s) t‖ ≤
      2 ^ J * Cf * Cg := by
  have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    w ^ r * ‖iteratedFDeriv ℝ j (fun s ↦ f s * g s) t‖ ≤
        w ^ r * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f t‖ * ‖iteratedFDeriv ℝ (j - i) g t‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hf hg t
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
        (pow_nonneg hw _)
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f t‖ * (w ^ r * ‖iteratedFDeriv ℝ (j - i) g t‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cf * Cg := by
      apply Finset.sum_le_sum
      intro i hi
      have hiJ : i ≤ J := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hleft i hiJ) (Nat.cast_nonneg _))
        (hright (j - i) ((Nat.sub_le j i).trans hj)) (by positivity)
        (mul_nonneg (Nat.cast_nonneg _) hCf)
    _ = 2 ^ j * Cf * Cg := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ ≤ 2 ^ J * Cf * Cg := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCf) hCg

private theorem phase_monomial_product_bound (A B : E →L[ℝ] ℝ)
    (u₀ rho₀ R : ℝ) (hR : 0 ≤ R) (J j : ℕ) (hj : j ≤ J) (t : E)
    (hrho : |monomial B rho₀ t| ≤ R) :
    ‖iteratedFDeriv ℝ j (fun s ↦ phase
      (monomial (A + B) (rho₀ * u₀) s)) t‖ ≤
      phaseBound (A + B) J * (1 + R) ^ j *
        (1 + |monomial A u₀ t|) ^ j := by
  have he : monomial (A + B) (rho₀ * u₀) t =
      monomial B rho₀ t * monomial A u₀ t := by
    simp only [monomial, _root_.add_apply, Real.exp_add]
    ring
  have hv : 1 + |monomial (A + B) (rho₀ * u₀) t| ≤
      (1 + R) * (1 + |monomial A u₀ t|) := by
    rw [he, abs_mul]
    have hm := mul_le_mul_of_nonneg_right hrho (abs_nonneg (monomial A u₀ t))
    nlinarith [abs_nonneg (monomial A u₀ t)]
  calc
    ‖iteratedFDeriv ℝ j (fun s ↦ phase
        (monomial (A + B) (rho₀ * u₀) s)) t‖ ≤
        phaseBound (A + B) J *
          (1 + |monomial (A + B) (rho₀ * u₀) t|) ^ j :=
      phase_monomial_deriv (A + B) (rho₀ * u₀) J j hj t
    _ ≤ phaseBound (A + B) J *
        ((1 + R) * (1 + |monomial A u₀ t|)) ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hv j)
        (phaseBound_nonneg _ _)
    _ = phaseBound (A + B) J * (1 + R) ^ j *
        (1 + |monomial A u₀ t|) ^ j := by rw [mul_pow, mul_assoc]

private def localizerBound (L : 𝓢(E, ℂ)) (J : ℕ) : ℝ :=
  (Finset.Iic (0, J)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) L

private theorem localizerBound_nonneg (L : 𝓢(E, ℂ)) (J : ℕ) :
    0 ≤ localizerBound L J := by unfold localizerBound; positivity

private theorem localizer_deriv_le (L : 𝓢(E, ℂ)) (J i : ℕ) (hi : i ≤ J) (t : E) :
    ‖iteratedFDeriv ℝ i L t‖ ≤ localizerBound L J := by
  simpa only [pow_zero, one_mul, localizerBound] using
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (0, J)) (k := 0) le_rfl hi L t)

end SmoothReciprocityLogMixedProof

open SmoothReciprocityLogMixedProof in
/-- Uniform all-order mixed logarithmic derivatives, with the constant chosen
before every varying atom parameter. The sign and size of `u₀` and `rho₀`
are unrestricted. Only the actual phase parameter on the fixed localizer
support is bounded by `R`. -/
theorem CommonSmoothCutoff.smoothReciprocityProfile_logMonomial_mixed_uniform
    {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hQc : HasCompactSupport Q) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z u₀ rho₀ R : ℝ, 1 ≤ Z → 0 ≤ R →
        (∀ t ∈ tsupport Q, |rho₀ * Real.exp (inner ℝ b t)| ≤ R) →
        ∀ j : ℕ, j ≤ J → ∀ t : EuclideanSpace ℝ (Fin d),
          ‖iteratedFDeriv ℝ j
            (smoothReciprocityLogWeight a b c Q Z u₀ rho₀) t‖ ≤
            C * (1 + R) ^ j := by
  let A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ a
  let B : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ b
  let G : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ c
  let q : EuclideanSpace ℝ (Fin d) → ℂ := fun t ↦
    Q t * (Real.exp (G t) : ℂ)
  have hq : ContDiff ℝ ∞ q := hQ.mul
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp G.contDiff))
  have hqc : HasCompactSupport q := hQc.mul_right
  let L : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := hqc.toSchwartzMap hq
  let F : 𝓢(ℝ, ℂ) := 𝓕 dyadicCutoffSchwartz
  let Cl : ℝ := localizerBound L J
  let Cx : ℝ := compositionBound cutoffSchwartz A 0 J
  let Cf : ℝ := compositionBound F A J J
  let Clx : ℝ := 2 ^ J * Cl * Cx
  let Ca : ℝ := 2 ^ J * Clx * Cf
  let Cp : ℝ := phaseBound (A + B) J
  let K : ℝ := 2 ^ J * Ca * Cp
  have hCl : 0 ≤ Cl := localizerBound_nonneg _ _
  have hCx : 0 ≤ Cx := compositionBound_nonneg _ _ _ _
  have hCf : 0 ≤ Cf := compositionBound_nonneg _ _ _ _
  have hClx : 0 ≤ Clx := mul_nonneg (mul_nonneg (by positivity) hCl) hCx
  have hCa : 0 ≤ Ca := mul_nonneg (mul_nonneg (by positivity) hClx) hCf
  have hCp : 0 ≤ Cp := phaseBound_nonneg _ _
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by positivity) hCa) hCp
  refine ⟨1 + K, by linarith, ?_⟩
  intro Z u₀ rho₀ R _hZ hR hrho j hj t
  let x : EuclideanSpace ℝ (Fin d) → ℝ := monomial A (u₀ / Z)
  let u : EuclideanSpace ℝ (Fin d) → ℝ := monomial A u₀
  let v : EuclideanSpace ℝ (Fin d) → ℝ := monomial (A + B) (rho₀ * u₀)
  let amplitude : EuclideanSpace ℝ (Fin d) → ℂ := fun s ↦
    (L s * cutoffSchwartz (x s)) * F (u s)
  let phasePullback : EuclideanSpace ℝ (Fin d) → ℂ := fun s ↦ phase (v s)
  let W : EuclideanSpace ℝ (Fin d) → ℂ :=
    smoothReciprocityLogWeight a b c Q Z u₀ rho₀
  have hx (s : EuclideanSpace ℝ (Fin d)) :
      x s = (u₀ * Real.exp (inner ℝ a s)) / Z := by
    change (u₀ / Z) * Real.exp (inner ℝ a s) = _
    ring
  have hv (s : EuclideanSpace ℝ (Fin d)) :
      v s = (rho₀ * Real.exp (inner ℝ b s)) *
        (u₀ * Real.exp (inner ℝ a s)) := by
    change (rho₀ * u₀) * Real.exp (inner ℝ a s + inner ℝ b s) = _
    rw [Real.exp_add]
    ring
  have hW : W = fun s ↦ amplitude s * phasePullback s := by
    funext s
    simp only [W, smoothReciprocityLogWeight, smoothReciprocityProfile,
      amplitude, phasePullback, cutoffSchwartz_apply, hx, hv, phase]
    change (Q s * (Real.exp (inner ℝ c s) : ℂ)) *
        ((poissonSmoothLowPass ((u₀ * Real.exp (inner ℝ a s)) / Z) : ℂ) *
          F (u s) * fourier (1 : ℤ)
            (((rho₀ * Real.exp (inner ℝ b s)) *
              (u₀ * Real.exp (inner ℝ a s)) : ℝ) : UnitAddCircle)) = _
    change _ = (((Q s * (Real.exp (inner ℝ c s) : ℂ)) *
        (poissonSmoothLowPass ((u₀ * Real.exp (inner ℝ a s)) / Z) : ℂ)) *
          F (u s)) * fourier (1 : ℤ)
            (((rho₀ * Real.exp (inner ℝ b s)) *
              (u₀ * Real.exp (inner ℝ a s)) : ℝ) : UnitAddCircle)
    ring
  have hxs : ContDiff ℝ ∞ (fun s ↦ cutoffSchwartz (x s)) :=
    (cutoffSchwartz.smooth (⊤ : ℕ∞)).comp (monomial_smooth A (u₀ / Z))
  have hus : ContDiff ℝ ∞ (fun s ↦ F (u s)) :=
    (F.smooth (⊤ : ℕ∞)).comp (monomial_smooth A u₀)
  have has : ContDiff ℝ ∞ amplitude := ((L.smooth (⊤ : ℕ∞)).mul hxs).mul hus
  have hps : ContDiff ℝ ∞ phasePullback :=
    phase_smooth.comp (monomial_smooth (A + B) (rho₀ * u₀))
  have hsupport : tsupport W ⊆ tsupport Q := by
    apply closure_mono
    intro s hs
    change Q s ≠ 0
    intro hQs
    exact hs (by simp only [W, smoothReciprocityLogWeight, hQs, zero_mul])
  by_cases ht : t ∈ tsupport Q
  · let w : ℝ := 1 + |u t|
    let p : ℝ := 1 + R
    have hw : 1 ≤ w := by dsimp [w]; linarith [abs_nonneg (u t)]
    have hp : 1 ≤ p := by dsimp [p]; linarith
    have hw0 : 0 <= w := zero_le_one.trans hw
    have hp0 : 0 <= p := zero_le_one.trans hp
    have hL (i : ℕ) (hi : i ≤ J) : ‖iteratedFDeriv ℝ i L t‖ ≤ Cl :=
      localizer_deriv_le L J i hi t
    have hcut (i : ℕ) (hi : i ≤ J) :
        ‖iteratedFDeriv ℝ i (fun s ↦ cutoffSchwartz (x s)) t‖ ≤ Cx := by
      simpa only [pow_zero, one_mul] using
        schwartz_monomial_deriv_weighted cutoffSchwartz A (u₀ / Z) 0 J i hi t
    have hLC (i : ℕ) (hi : i ≤ J) :
        ‖iteratedFDeriv ℝ i (fun s ↦ L s * cutoffSchwartz (x s)) t‖ ≤ Clx := by
      simpa only [pow_zero, one_mul] using
        weighted_mul_bound (L.smooth (⊤ : ℕ∞)) hxs J 0 1 Cl Cx (by norm_num)
          hCl hCx t hL (fun k hk ↦ by simpa only [pow_zero, one_mul] using hcut k hk)
          i hi
    have hF (i : ℕ) (hi : i ≤ J) :
        w ^ J * ‖iteratedFDeriv ℝ i (fun s ↦ F (u s)) t‖ ≤ Cf :=
      schwartz_monomial_deriv_weighted F A u₀ J J i hi t
    have hAmplitude (i : ℕ) (hi : i ≤ J) :
        w ^ J * ‖iteratedFDeriv ℝ i amplitude t‖ ≤ Ca :=
      weighted_mul_bound ((L.smooth (⊤ : ℕ∞)).mul hxs) hus J J w Clx Cf
        (by linarith) hClx hCf t hLC hF i hi
    have hPhase (i : ℕ) (hi : i ≤ J) :
        ‖iteratedFDeriv ℝ i phasePullback t‖ ≤ Cp * p ^ i * w ^ i :=
      phase_monomial_product_bound A B u₀ rho₀ R hR J i hi t (hrho t ht)
    have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    have hmain : ‖iteratedFDeriv ℝ j W t‖ ≤ K * p ^ j := by
      rw [hW]
      calc
        ‖iteratedFDeriv ℝ j (fun s ↦ amplitude s * phasePullback s) t‖ ≤
            ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i amplitude t‖ *
                ‖iteratedFDeriv ℝ (j - i) phasePullback t‖ :=
          norm_iteratedFDeriv_mul_le has hps t
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
        _ ≤ ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * Ca * Cp * p ^ j := by
          apply Finset.sum_le_sum
          intro i hi
          have hiJ : i ≤ J := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hj
          have hmJ : j - i ≤ J := (Nat.sub_le j i).trans hj
          calc
            (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i amplitude t‖ *
                ‖iteratedFDeriv ℝ (j - i) phasePullback t‖ ≤
                (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i amplitude t‖ *
                  (Cp * p ^ (j - i) * w ^ (j - i)) := by
              exact mul_le_mul_of_nonneg_left (hPhase (j - i) hmJ) (by positivity)
            _ = (j.choose i : ℝ) *
                (w ^ (j - i) * ‖iteratedFDeriv ℝ i amplitude t‖) * Cp *
                  p ^ (j - i) := by ring
            _ ≤ (j.choose i : ℝ) *
                (w ^ J * ‖iteratedFDeriv ℝ i amplitude t‖) * Cp * p ^ j := by
              have hwp : w ^ (j - i) <= w ^ J := pow_le_pow_right₀ hw hmJ
              have hpp : p ^ (j - i) <= p ^ j :=
                pow_le_pow_right₀ hp (Nat.sub_le j i)
              exact mul_le_mul
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hwp (norm_nonneg _))
                    (Nat.cast_nonneg _)) hCp)
                hpp (pow_nonneg hp0 _)
                (mul_nonneg
                  (mul_nonneg (Nat.cast_nonneg _)
                    (mul_nonneg (pow_nonneg hw0 _) (norm_nonneg _))) hCp)
            _ ≤ (j.choose i : ℝ) * Ca * Cp * p ^ j := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hAmplitude i hiJ)
                    (Nat.cast_nonneg _)) hCp)
                (pow_nonneg hp0 _)
        _ = 2 ^ j * Ca * Cp * p ^ j := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hsum]
        _ ≤ K * p ^ j := by
          have htwo : (2 : Real) ^ j <= (2 : Real) ^ J :=
            pow_le_pow_right₀ (by norm_num) hj
          change (2 : Real) ^ j * Ca * Cp * p ^ j <=
            (2 : Real) ^ J * Ca * Cp * p ^ j
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right htwo hCa) hCp)
            (pow_nonneg hp0 _)
    exact hmain.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · have hzero : iteratedFDeriv ℝ j W t = 0 := by
      by_contra hn
      exact ht (hsupport (support_iteratedFDeriv_subset j hn))
    rw [hzero, norm_zero]
    positivity

end

end ImbalancedChen.Part3
