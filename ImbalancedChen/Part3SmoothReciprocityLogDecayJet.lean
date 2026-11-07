import ImbalancedChen.Part3SmoothReciprocityLogRegularity

/-!
One retained power of the actual profile's Schwartz decay, for the physical
constant-rho logarithmic row b=0. All localizer and linear-form data are fixed
before the scale and signed atom parameters. This is a jet estimate only.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators SchwartzMap FourierTransform ContDiff
open CommonSmoothCutoff

namespace SmoothReciprocityLogDecayJetProof

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

private theorem profile_smooth (Z rho : ℝ) :
    ContDiff ℝ ∞ (smoothReciprocityProfile Z rho) := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 dyadicCutoffSchwartz
  have hlow : ContDiff ℝ ∞ poissonSmoothLowPass :=
    dyadicBump.contDiff.comp (contDiff_const.add (contDiff_id.div_const 2))
  have hcut : ContDiff ℝ ∞ (fun u : ℝ ↦ (poissonSmoothLowPass (u / Z) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hlow.comp (contDiff_id.div_const Z))
  have hcharacter : ContDiff ℝ ∞
      (fun v : ℝ ↦ fourier (1 : ℤ) (v : UnitAddCircle)) := by
    have heq : (fun v : ℝ ↦ fourier (1 : ℤ) (v : UnitAddCircle)) =
        (fun v : ℝ ↦ Complex.exp ((2 * Real.pi * Complex.I) * (v : ℂ))) := by
      funext v
      simp only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
    rw [heq]
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hphase : ContDiff ℝ ∞
      (fun u : ℝ ↦ fourier (1 : ℤ) ((rho * u : ℝ) : UnitAddCircle)) :=
    hcharacter.comp (contDiff_const.mul contDiff_id)
  exact (hcut.mul (F.smooth (⊤ : ℕ∞))).mul hphase

private theorem profile_outer_uniform :
    ∃ B : ℝ, 0 < B ∧ ∀ Z rho R : ℝ, 1 ≤ Z → 0 ≤ R → |rho| ≤ R →
      ∀ k : ℕ, k ≤ 4 → ∀ u : ℝ,
        (1 + |u|) ^ 5 * ‖iteratedDeriv k (smoothReciprocityProfile Z rho) u‖ ≤
          B * (1 + R) ^ 4 := by
  choose C hC hbound using fun k : ℕ ↦ smoothReciprocityProfile_iteratedDeriv_uniform 5 k
  let B : ℝ := 1 + ∑ k ∈ Finset.range 5, C k
  have hsum : 0 ≤ ∑ k ∈ Finset.range 5, C k :=
    Finset.sum_nonneg (fun k _ ↦ (hC k).le)
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro Z rho R hZ hR hrho k hk u
  have hCk : C k ≤ B := by
    have hle := Finset.single_le_sum (fun i _ ↦ (hC i).le)
      (Finset.mem_range.mpr (show k < 5 by omega))
    dsimp [B]
    linarith
  have hpow : (1 + |rho|) ^ k ≤ (1 + R) ^ 4 :=
    (pow_le_pow_left₀ (by positivity) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith) hk)
  exact (hbound k Z rho hZ u).trans
    ((mul_le_mul_of_nonneg_left hpow (hC k).le).trans
      (mul_le_mul_of_nonneg_right hCk (by positivity)))

private theorem profile_monomial_weighted (A : E →L[ℝ] ℝ)
    (B : ℝ) (hB : 0 ≤ B) (Z rho u₀ R : ℝ) (hR : 0 ≤ R)
    (houter : ∀ k : ℕ, k ≤ 4 → ∀ u : ℝ,
      (1 + |u|) ^ 5 * ‖iteratedDeriv k (smoothReciprocityProfile Z rho) u‖ ≤
        B * (1 + R) ^ 4)
    (j : ℕ) (hj : j ≤ 4) (t : E) :
    (1 + |monomial A u₀ t|) *
      ‖iteratedFDeriv ℝ j (fun s ↦ smoothReciprocityProfile Z rho (monomial A u₀ s)) t‖ ≤
        (4 : ℕ).factorial * B * (1 + ‖A‖) ^ 4 * (1 + R) ^ 4 := by
  let w : ℝ := 1 + |monomial A u₀ t|
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : 1 ≤ w := by dsimp [w]; linarith [abs_nonneg (monomial A u₀ t)]
  have hout (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (smoothReciprocityProfile Z rho) (monomial A u₀ t)‖ ≤
        (B * (1 + R) ^ 4) / w ^ (1 + j) := by
    apply (le_div_iff₀ (pow_pos hw _)).2
    rw [mul_comm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hw1 (show 1 + j ≤ 5 by omega)) (norm_nonneg _)).trans
        (houter i (hi.trans hj) (monomial A u₀ t))
  have hcomp := norm_iteratedFDeriv_comp_le (profile_smooth Z rho)
    (monomial_smooth A u₀) (ENat.natCast_le_of_coe_top_le_withTop le_rfl j) t hout
    (fun i hi _ ↦ monomial_deriv_power A u₀ i hi t)
  calc
    w * ‖iteratedFDeriv ℝ j (fun s ↦ smoothReciprocityProfile Z rho (monomial A u₀ s)) t‖ ≤
        w * (j.factorial * ((B * (1 + R) ^ 4) / w ^ (1 + j)) *
          ((1 + ‖A‖) * w) ^ j) := mul_le_mul_of_nonneg_left hcomp hw.le
    _ = (j.factorial * B * (1 + ‖A‖) ^ j) * (1 + R) ^ 4 *
        (w ^ 1 * w ^ j / w ^ (1 + j)) := by rw [mul_pow]; ring
    _ = (j.factorial * B * (1 + ‖A‖) ^ j) * (1 + R) ^ 4 := by
      rw [← pow_add, div_self (pow_ne_zero _ hw.ne'), mul_one]
    _ ≤ (4 : ℕ).factorial * B * (1 + ‖A‖) ^ 4 * (1 + R) ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hB)
        (pow_le_pow_right₀ (by linarith [norm_nonneg A]) hj) (by positivity) (by positivity)

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

private def localizerBound (L : 𝓢(E, ℂ)) (J : ℕ) : ℝ :=
  (Finset.Iic (0, J)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) L

private theorem localizerBound_nonneg (L : 𝓢(E, ℂ)) (J : ℕ) :
    0 ≤ localizerBound L J := by unfold localizerBound; positivity

private theorem localizer_deriv_le (L : 𝓢(E, ℂ)) (J i : ℕ) (hi : i ≤ J) (t : E) :
    ‖iteratedFDeriv ℝ i L t‖ ≤ localizerBound L J := by
  simpa only [pow_zero, one_mul, localizerBound] using
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (0, J)) (k := 0) le_rfl hi L t)

end SmoothReciprocityLogDecayJetProof

open SmoothReciprocityLogDecayJetProof in
/-- The actual b=0 row retains one full power of signed u0 decay in every jet
through order four. The constant precedes all varying atom parameters. -/
theorem CommonSmoothCutoff.smoothReciprocityLogWeight_zeroSlope_decayJet_uniform
    {d : ℕ} (a c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hQc : HasCompactSupport Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z u₀ rho₀ R : ℝ, 1 ≤ Z → 0 ≤ R → |rho₀| ≤ R →
        ∀ j : ℕ, j ≤ 4 → ∀ t : EuclideanSpace ℝ (Fin d),
          (1 + |u₀|) *
            ‖iteratedFDeriv ℝ j (smoothReciprocityLogWeight a 0 c Q Z u₀ rho₀) t‖ ≤
              C * (1 + R) ^ 4 := by
  let A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ a
  let G : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := innerSL ℝ c
  let q : EuclideanSpace ℝ (Fin d) → ℂ := fun t ↦ Q t * (Real.exp (G t) : ℂ)
  have hq : ContDiff ℝ ∞ q := hQ.mul
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp G.contDiff))
  have hqc : HasCompactSupport q := hQc.mul_right
  let L : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := hqc.toSchwartzMap hq
  let Cl : ℝ := localizerBound L 4
  have hCl : 0 ≤ Cl := localizerBound_nonneg L 4
  obtain ⟨B, hB, houter⟩ := profile_outer_uniform
  let Cg : ℝ := (4 : ℕ).factorial * B * (1 + ‖A‖) ^ 4
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  obtain ⟨T, hT⟩ := hQc.bddAbove_image
    (Real.continuous_exp.comp A.continuous.neg).continuousOn
  let H : ℝ := 1 + |T|
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg T]
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hcompare (u₀ : ℝ) (t : EuclideanSpace ℝ (Fin d)) (ht : t ∈ tsupport Q) :
      1 + |u₀| ≤ H * (1 + |monomial A u₀ t|) := by
    have he : Real.exp (-A t) ≤ H := by
      have hTt : Real.exp (-A t) ≤ T := hT (Set.mem_image_of_mem _ ht)
      exact hTt.trans ((le_abs_self T).trans (by dsimp [H]; linarith))
    have hid : |monomial A u₀ t| * Real.exp (-A t) = |u₀| := by
      rw [monomial, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc,
        ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hmul := mul_le_mul_of_nonneg_left he (abs_nonneg (monomial A u₀ t))
    rw [hid] at hmul
    nlinarith only [hH, hmul]
  have hconstant : 0 ≤ H * (2 : ℝ) ^ 4 * Cl * Cg := by positivity
  refine ⟨1 + H * (2 : ℝ) ^ 4 * Cl * Cg, by positivity, ?_⟩
  intro Z u₀ rho₀ R hZ hR hrho j hj t
  let W := smoothReciprocityLogWeight a 0 c Q Z u₀ rho₀
  let P : EuclideanSpace ℝ (Fin d) → ℂ := fun s ↦
    smoothReciprocityProfile Z rho₀ (monomial A u₀ s)
  have hP : ContDiff ℝ ∞ P := (profile_smooth Z rho₀).comp (monomial_smooth A u₀)
  have hW : W = fun s ↦ L s * P s := by
    funext s
    simp only [W, smoothReciprocityLogWeight, inner_zero_left, Real.exp_zero, mul_one]
    rfl
  have hsupport : tsupport W ⊆ tsupport Q :=
    smoothReciprocityLogWeight_tsupport_subset a 0 c Q Z u₀ rho₀
  by_cases ht : t ∈ tsupport Q
  · let w : ℝ := 1 + |monomial A u₀ t|
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have hprofile (i : ℕ) (hi : i ≤ 4) :
        w ^ 1 * ‖iteratedFDeriv ℝ i P t‖ ≤ Cg * (1 + R) ^ 4 := by
      simpa only [pow_one, P, w, Cg] using
        profile_monomial_weighted A B hB.le Z rho₀ u₀ R hR
          (houter Z rho₀ R hZ hR hrho) i hi t
    have hproduct : w * ‖iteratedFDeriv ℝ j W t‖ ≤
        ((2 : ℝ) ^ 4 * Cl * Cg) * (1 + R) ^ 4 := by
      rw [hW]
      have h := weighted_mul_bound (L.smooth (⊤ : ℕ∞)) hP 4 1 w Cl
        (Cg * (1 + R) ^ 4) hw hCl (by positivity) t
        (fun i hi ↦ localizer_deriv_le L 4 i hi t) hprofile j hj
      simpa only [pow_one, mul_assoc] using h
    calc
      (1 + |u₀|) * ‖iteratedFDeriv ℝ j W t‖ ≤ H * w * ‖iteratedFDeriv ℝ j W t‖ :=
        mul_le_mul_of_nonneg_right (hcompare u₀ t ht) (norm_nonneg _)
      _ = H * (w * ‖iteratedFDeriv ℝ j W t‖) := by ring
      _ ≤ H * (((2 : ℝ) ^ 4 * Cl * Cg) * (1 + R) ^ 4) :=
        mul_le_mul_of_nonneg_left hproduct hH0
      _ = (H * (2 : ℝ) ^ 4 * Cl * Cg) * (1 + R) ^ 4 := by ring
      _ ≤ (1 + H * (2 : ℝ) ^ 4 * Cl * Cg) * (1 + R) ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hzero : iteratedFDeriv ℝ j W t = 0 := by
      by_contra hn
      exact ht (hsupport (support_iteratedFDeriv_subset j hn))
    change (1 + |u₀|) * ‖iteratedFDeriv ℝ j W t‖ ≤ _
    rw [hzero, norm_zero, mul_zero]
    positivity

end

end ImbalancedChen.Part3
