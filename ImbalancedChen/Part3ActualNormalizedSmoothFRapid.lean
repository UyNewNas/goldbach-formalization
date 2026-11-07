import ImbalancedChen.Part3ActualNormalizedSmoothF

/- STANDALONE COMPANION DRAFT, uncompiled. Physical signs ONLY.
Parent actualF61023c is strict-PASS; this companion has no kernel receipt.
All parent references are public declarations reached by the sole import.
No same-file private declaration or copied parent block is needed. Constants are
chosen before rho/sigma. No desired derivative mass, spectral estimate, or
unknown Fourier decay is a final premise. Actual normalizedF is unchanged.
Native norm_iteratedFDerivWithin_comp_le needs Phi jet bounds only at f(x),
so the true Schwartz weight at sigma*rho*fixedGeometry(x) is retained. -/

namespace ImbalancedChen.Part3.ActualNormalizedSmoothFRapid
noncomputable section
open Set MeasureTheory CommonSmoothCutoff ActualNormalizedSmoothF
open scoped BigOperators ContDiff FourierTransform SchwartzMap

theorem fixedGeometry_lower {x : E4} (hx : x ∈ fixedBox) :
    (1 : ℝ)/25 ≤ fixedGeometry x := by
  have ht : Real.sqrt 10 / 25 ≤ x 0 := by
    simpa [boxLo] using (hx 0).1
  have hv : (1 : ℝ)/2 ≤ x 1 := by simpa [boxLo] using (hx 1).1
  have hw : x 2 ≤ (5 : ℝ)/2 := by simpa [boxHi] using (hx 2).2
  have hz : (1 : ℝ)/2 ≤ x 3 := by simpa [boxLo] using (hx 3).1
  have hp := fixedBox_positive hx
  have hvz : (1 : ℝ)/4 ≤ x 1*x 3 := by
    have hh := mul_le_mul hv hz (by norm_num : (0 : ℝ) ≤ 1/2) hp.2.1.le
    norm_num at hh
    exact hh
  have hratio : (1 : ℝ)/10 ≤ x 1*x 3/x 2 :=
    (le_div_iff₀ hp.2.2.1).mpr (by nlinarith)
  have hsqrt := Real.sqrt_le_sqrt hratio
  have hroot : Real.sqrt (10 : ℝ)*Real.sqrt (1/10 : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num
  have hconst : (Real.sqrt (10 : ℝ)/25)*Real.sqrt (1/10 : ℝ) = 1/25 := by
    calc
      _ = (Real.sqrt (10 : ℝ)*Real.sqrt (1/10 : ℝ))/25 := by ring
      _ = _ := by rw [hroot]
  rw [← hconst]
  exact mul_le_mul ht hsqrt (Real.sqrt_nonneg _) hp.1.le

def jetMajorant (N i : ℕ) : ℝ :=
  (2 : ℝ)^N * |SchwartzMap.seminorm ℝ 0 i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)))| +
    (50 : ℝ)^N * |SchwartzMap.seminorm ℝ N i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)))|

theorem jetMajorant_nonneg (N i : ℕ) : 0 ≤ jetMajorant N i := by
  unfold jetMajorant
  positivity

/-- Uses the original large/small-rho split, including rho=0. -/
theorem actualPhi_point_weight (N i : ℕ) {rho sigma : ℝ}
    (hrho : 0 ≤ rho) (hsigma : |sigma| = 1) {x : E4} (hx : x ∈ fixedBox) :
    (1+rho)^N *
      ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
        (sigma*rho*fixedGeometry x)‖ ≤ jetMajorant N i := by
  let y := sigma*rho*fixedGeometry x
  have h0 : ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ ≤
      |SchwartzMap.seminorm ℝ 0 i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)))| := by
    have h := SchwartzMap.le_seminorm ℝ 0 i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) y
    simp only [pow_zero, one_mul] at h
    exact h.trans (le_abs_self _)
  have hN : |y|^N * ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ ≤
      |SchwartzMap.seminorm ℝ N i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)))| := by
    have h := SchwartzMap.le_seminorm ℝ N i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) y
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_abs_self _)
  by_cases hsmall : rho ≤ 1
  · have hp : (1+rho)^N ≤ (2 : ℝ)^N :=
      pow_le_pow_left₀ (by linarith) (by linarith) N
    calc
      _ ≤ (2 : ℝ)^N * |SchwartzMap.seminorm ℝ 0 i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)))| :=
        mul_le_mul hp h0 (norm_nonneg _) (by positivity)
      _ ≤ jetMajorant N i := by
        unfold jetMajorant
        exact le_add_of_nonneg_right (by positivity)
  · have hg := fixedGeometry_lower hx
    have hg0 : 0 ≤ fixedGeometry x := by linarith
    have hy : |y| = rho*fixedGeometry x := by
      dsimp [y]
      rw [abs_mul, abs_mul, hsigma, abs_of_nonneg hrho, abs_of_nonneg hg0, one_mul]
    have hlarge : 1 ≤ rho := le_of_lt (lt_of_not_ge hsmall)
    have hmul := mul_le_mul_of_nonneg_left hg hrho
    have hbase : 1+rho ≤ 50*|y| := by rw [hy]; nlinarith
    have hp : (1+rho)^N ≤ (50*|y|)^N :=
      pow_le_pow_left₀ (by linarith) hbase N
    calc
      _ ≤ (50*|y|)^N *
          ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = (50 : ℝ)^N * (|y|^N *
          ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖) := by rw [mul_pow]; ring
      _ ≤ (50 : ℝ)^N * |SchwartzMap.seminorm ℝ N i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)))| :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ ≤ jetMajorant N i := by
        unfold jetMajorant
        exact le_add_of_nonneg_left (by positivity)

theorem actualPhi_finite_weighted_bound (r N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| = 1 →
      ∀ x ∈ fixedBox, ∀ i ≤ r,
        ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
          (sigma*rho*fixedGeometry x)‖ ≤ K/(1+rho)^N := by
  let K : ℝ := 1 + ∑ i ∈ Finset.range (r+1), jetMajorant N i
  have hsum : 0 ≤ ∑ i ∈ Finset.range (r+1), jetMajorant N i :=
    Finset.sum_nonneg (fun i _ => jetMajorant_nonneg N i)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro rho hrho sigma hsigma x hx i hi
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+rho) N)).mpr
  calc
    _ = (1+rho)^N *
        ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
          (sigma*rho*fixedGeometry x)‖ := by ring
    _ ≤ jetMajorant N i := actualPhi_point_weight N i hrho hsigma hx
    _ ≤ ∑ k ∈ Finset.range (r+1), jetMajorant N k :=
      Finset.single_le_sum (fun k _ => jetMajorant_nonneg N k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    _ ≤ K := by dsimp [K]; linarith

theorem composition_at_actual_point
    (r : ℕ) (C D : ℝ) (hC0 : 0 ≤ C) (hD1 : 1 ≤ D)
    (hGeom : ∀ i ≤ r, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i fixedGeometry x‖ ≤ D)
    {rho sigma : ℝ} (hrho : 0 ≤ rho) (hsigma : |sigma| ≤ 1)
    {j : ℕ} (hj : j ≤ r) {x : E4} (hx : x ∈ fixedBox)
    (hPhi : ∀ i ≤ r,
      ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
        (sigma*rho*fixedGeometry x)‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ j
        (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y))
        {y : E4 | positive y} x‖ ≤
      ((j.factorial : ℝ) * C * D ^ j) * (1 + rho) ^ r := by
  let O : Set E4 := {y | positive y}
  have hxO : x ∈ O := fixedBox_positive hx
  have hO : IsOpen O := positive_isOpen
  have hG : ContDiffOn ℝ ∞ fixedGeometry O :=
    fun y hy => (fixedGeometry_contDiffAt hy).contDiffWithinAt
  have hf : ContDiffOn ℝ ∞ (fun y => sigma * rho * fixedGeometry y) O :=
    contDiffOn_const.mul hG
  have hP1 : 1 ≤ 1 + rho := by linarith
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  have hPD1 : 1 ≤ (1 + rho) * D := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (1 + rho) * D := mul_le_mul hP1 hD1 zero_le_one (by linarith)
  have hnorm (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (fun y => sigma * rho * fixedGeometry y) O x‖ ≤
        ((1 + rho) * D) ^ i := by
    have hscale :
        iteratedFDerivWithin ℝ i (fun y => sigma * rho * fixedGeometry y) O x =
          (sigma * rho) • iteratedFDerivWithin ℝ i fixedGeometry O x := by
      have hfun : (fun y : E4 => sigma * rho * fixedGeometry y) =
          (sigma * rho) • fixedGeometry := by
        funext y
        rfl
      rw [hfun]
      exact (iteratedFDerivWithin_const_smul_apply (a := sigma * rho)
          ((fixedGeometry_contDiffAt hxO).of_le
            (show (i : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
          hO.uniqueDiffOn hxO)
    have hGb : ‖iteratedFDerivWithin ℝ i fixedGeometry O x‖ ≤ D := by
      rw [iteratedFDerivWithin_of_isOpen i hO hxO]
      exact hGeom i (le_trans hij hj) x hx
    have hs : |sigma| * rho ≤ rho := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsigma hrho
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hrho]
    calc
      |sigma| * rho * ‖iteratedFDerivWithin ℝ i fixedGeometry O x‖ ≤ rho * D :=
        mul_le_mul hs hGb (norm_nonneg _) hrho
      _ ≤ (1 + rho) * D := mul_le_mul_of_nonneg_right (by linarith) hD0
      _ = ((1 + rho) * D) ^ 1 := by rw [pow_one]
      _ ≤ ((1 + rho) * D) ^ i := pow_le_pow_right₀ hPD1 hi
  have hbound := norm_iteratedFDerivWithin_comp_le
    (g := ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
    (f := fun y : E4 => sigma * rho * fixedGeometry y)
    (s := O) (t := Set.univ) (n := j)
    ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)).smooth ⊤).contDiffOn hf
    (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    uniqueDiffOn_univ hO.uniqueDiffOn (fun _ _ => mem_univ _) hxO
    (C := C) (D := (1 + rho) * D)
    (fun i hi => by
      rw [iteratedFDerivWithin_univ]
      exact hPhi i (le_trans hi hj)) hnorm
  calc
    ‖iteratedFDerivWithin ℝ j
        (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O x‖
      ≤ (j.factorial : ℝ) * C * ((1 + rho) * D) ^ j := by
        simpa only [Function.comp_def] using hbound
    _ = ((j.factorial : ℝ) * C * D ^ j) * (1 + rho) ^ j := by
      rw [mul_pow]
      ring
    _ ≤ ((j.factorial : ℝ) * C * D ^ j) * (1 + rho) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP1 hj) (by positivity)

theorem normalizedF_derivative_at_actual_point
    (r : ℕ) (A C D : ℝ) (hA1 : 1 ≤ A) (hC0 : 0 ≤ C) (hD1 : 1 ≤ D)
    (hAmp : ∀ i ≤ r, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i fixedAmplitude x‖ ≤ A)
    (hGeom : ∀ i ≤ r, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i fixedGeometry x‖ ≤ D)
    {rho sigma : ℝ} (hrho : 0 ≤ rho) (hsigma : |sigma| ≤ 1)
    {j : ℕ} (hj : j ≤ r) {x : E4} (hx : x ∈ fixedBox)
    (hPhi : ∀ i ≤ r,
      ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
        (sigma*rho*fixedGeometry x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖ ≤
      derivativeCost A C D j * (1 + rho) ^ r := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  let O : Set E4 := {y | positive y}
  have hxO : x ∈ O := fixedBox_positive hx
  have hO : IsOpen O := positive_isOpen
  have hA : ContDiffOn ℝ ∞ fixedAmplitude O :=
    fun y hy => (fixedAmplitude_contDiffAt hy).contDiffWithinAt
  have hG : ContDiffOn ℝ ∞ fixedGeometry O :=
    fun y hy => (fixedGeometry_contDiffAt hy).contDiffWithinAt
  have hcomp : ContDiffOn ℝ ∞
      (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O :=
    ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)).smooth ⊤).comp_contDiffOn (contDiffOn_const.mul hG)
  have heq : EqOn (normalizedF rho sigma)
      (fun y => fixedAmplitude y *
        ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O := by
    intro y hy
    change positive y at hy
    simp only [normalizedF, if_pos hy, rawF, fixedAmplitude, fixedGeometry, mul_assoc]
  rw [← iteratedFDerivWithin_of_isOpen j hO hxO,
    iteratedFDerivWithin_congr heq hxO j]
  calc
    ‖iteratedFDerivWithin ℝ j
        (fun y => fixedAmplitude y *
          ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i fixedAmplitude O x‖ *
          ‖iteratedFDerivWithin ℝ (j - i)
            (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O x‖ :=
      norm_iteratedFDerivWithin_mul_le hA hcomp hO.uniqueDiffOn hxO
        (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℝ) * A * ((j - i).factorial : ℝ) * C * D ^ (j - i)) *
          (1 + rho) ^ r := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hj
      have hAb : ‖iteratedFDerivWithin ℝ i fixedAmplitude O x‖ ≤ A := by
        rw [iteratedFDerivWithin_of_isOpen i hO hxO]
        exact hAmp i hir x hx
      have hCb := composition_at_actual_point r C D hC0 hD1 hGeom
        hrho hsigma (le_trans (Nat.sub_le j i) hj) hx hPhi
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left hAb (Nat.cast_nonneg (j.choose i))) hCb
        (norm_nonneg _) (by positivity : 0 ≤ (j.choose i : ℝ) * A)
      exact hmul.trans_eq (by ring)
    _ = derivativeCost A C D j * (1 + rho) ^ r := by
      rw [derivativeCost, Finset.sum_mul]

theorem derivativeCost_div (A K D P : ℝ) (j : ℕ) :
    derivativeCost A (K/P) D j = derivativeCost A K D j/P := by
  simp only [derivativeCost, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [div_eq_mul_inv]
  ring

theorem derivativeCost_cancel (A K D P : ℝ) (j r a : ℕ) (hP : 0 < P) :
    derivativeCost A (K/P^(r+a)) D j * P^r = derivativeCost A K D j/P^a := by
  rw [derivativeCost_div, pow_add]
  field_simp [hP.ne']

/-- All constants precede rho and the physical sign. This is the ACTUAL
finite derivative-integral sum, with all orders j<=r and no mass premise. -/
theorem actual_physical_sign_rapid_derivative_mass (r a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| = 1 →
      (∑ j ∈ Finset.range (r+1), ∫ x : E4,
        ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖) ≤ C/(1+rho)^a := by
  obtain ⟨A, hA1, hAmp⟩ := fixedBox_finite_derivative_bound fixedAmplitude
    (fun x hx => fixedAmplitude_contDiffAt (fixedBox_positive hx)) r
  obtain ⟨D, hD1, hGeom⟩ := fixedBox_finite_derivative_bound fixedGeometry
    (fun x hx => fixedGeometry_contDiffAt (fixedBox_positive hx)) r
  obtain ⟨K, hK, hPhi⟩ := actualPhi_finite_weighted_bound r (r+a)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  let S : ℝ := ∑ j ∈ Finset.range (r+1), derivativeCost A K D j
  have hS : 0 ≤ S := Finset.sum_nonneg
    (fun j _ => derivativeCost_nonneg hA0 hK.le hD0 j)
  have hvol : 0 ≤ volume.real fixedBox := ENNReal.toReal_nonneg
  let C : ℝ := 1 + S*volume.real fixedBox
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro rho hrho sigma hsigma
  have hP : 0 < 1+rho := by linarith
  have hpoint (j : ℕ) (hj : j ≤ r) (x : E4) (hx : x ∈ fixedBox) :
      ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖ ≤
        derivativeCost A K D j/(1+rho)^a := by
    have hjet := hPhi rho hrho sigma hsigma x hx
    have hraw := normalizedF_derivative_at_actual_point r A (K/(1+rho)^(r+a)) D
      hA1 (by positivity) hD1 hAmp hGeom hrho hsigma.le hj hx hjet
    rw [derivativeCost_cancel A K D (1+rho) j r a hP] at hraw
    exact hraw
  calc
    (∑ j ∈ Finset.range (r+1), ∫ x : E4,
        ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖)
      ≤ ∑ j ∈ Finset.range (r+1),
          (derivativeCost A K D j/(1+rho)^a)*volume.real fixedBox := by
        apply Finset.sum_le_sum
        intro j hj
        apply actual_derivative_integral_bound
        intro x hx
        exact hpoint j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x hx
    _ = (S*volume.real fixedBox)/(1+rho)^a := by
      dsimp [S]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ C/(1+rho)^a := by
      apply (div_le_div_iff_of_pos_right (pow_pos hP a)).mpr
      dsimp [C]
      linarith

/-- The original two signed branches, without enlarging to sigma=0. -/
theorem actual_two_sign_rapid_derivative_mass (r a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ,
      (sigma = 1 ∨ sigma = -1) →
      (∑ j ∈ Finset.range (r+1), ∫ x : E4,
        ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖) ≤ C/(1+rho)^a := by
  obtain ⟨C,hC,hb⟩ := actual_physical_sign_rapid_derivative_mass r a
  refine ⟨C,hC,fun rho hrho sigma hsigma => hb rho hrho sigma ?_⟩
  rcases hsigma with rfl | rfl <;> norm_num

end
end ImbalancedChen.Part3.ActualNormalizedSmoothFRapid
