import ImbalancedChen.Part3TwoLongTransitionMellinN2
import ImbalancedChen.P5ActualLowerNormalizedHBSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual HB one/log roles and the three existing transition labels consume
the internally proved natural P2. The full normalized atlas reindex and
rough E1/E3 mean payment are NOT asserted by this local source module.
-/
namespace ImbalancedChen.Part3.TwoLongHBMellinBrunProfiles
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b (phase)
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongActualThreeBrunP2Receiver
open ImbalancedChen.Part3.TwoLongInternalP2Modes
open ImbalancedChen.Part3.TwoLongNaturalInternalP2
open ImbalancedChen.Part3.TwoLongTransitionMellinN2
open ImbalancedChen.P5Z.HBRightClosedDyadicRoles
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

def leftMellin (delta U t : ℝ) (label : Fin 3) (isLog : Bool) : ℝ → ℂ :=
  profile (decide (label = 1)) isLog delta U t

def rightMellin (delta V t : ℝ) (label : Fin 3) (isLog : Bool) : ℝ → ℂ :=
  profile (decide (label = 2)) isLog delta V t

theorem leftMellin_exact (delta U t x : ℝ) (label : Fin 3) (isLog : Bool) :
    leftMellin delta U t label isLog x =
      leftProfile delta label x * (logFactor isLog U x : ℂ) * phase t x := by
  by_cases h : label = 1 <;>
    simp [leftMellin, profile, twisted, amplitude, transition, leftProfile, h]

theorem rightMellin_exact (delta V t x : ℝ) (label : Fin 3) (isLog : Bool) :
    rightMellin delta V t label isLog x =
      rightProfile delta label x * (logFactor isLog V x : ℂ) * phase t x := by
  by_cases h : label = 2 <;>
    simp [rightMellin, profile, twisted, amplitude, transition, rightProfile, h]

/-- Literal source equality at a positive Brun divisor. In particular,
the logarithm remains log(d*u); it is never replaced by log u. -/
theorem logFactor_brun {U : ℝ} (hU : 0 < U) {d u : ℕ}
    (hd : 0 < d) (hu : 0 < u) :
    logFactor true U ((u : ℝ)/(U/d)) = Real.log ((d*u : ℕ) : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hz : (u : ℝ)/(U/d) ≠ 0 := (div_pos huR (div_pos hU hdR)).ne'
  have he : U*((u : ℝ)/(U/d)) = ((d*u : ℕ) : ℝ) := by
    push_cast
    field_simp [hU.ne', hdR.ne']
    ring
  change Real.log U + Real.log ((u : ℝ)/(U/d)) = _
  rw [← Real.log_mul hU.ne' hz, he]

/-- Actual original long roles, retaining the same strict rough mask.
The Mobius role is deliberately excluded; its long-slot exclusion is a
different original HB classification obligation. -/
theorem owned_long_role_profile {b : Block} {d u : ℕ}
    (hd : 0 < d) (hOwn : Owns b (d*u)) (z y t : ℝ)
    (role : Role) (hrole : role = .one ∨ role = .logarithm) :
    actual z y role (d*u) * phase t
      ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) =
    (logFactor (decide (role = .logarithm))
      (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b)
      ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) : ℂ) *
      phase t ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) *
      ImbalancedChen.Part3.roughOneSlot z (d*u) := by
  have hU : (0 : ℝ) < ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b := by
    exact_mod_cast ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower_pos b
  have hdu : 0 < d*u := lt_of_lt_of_le
    (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower_pos b)
    (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.owns_bounds hOwn).1
  have hu : 0 < u := (Nat.mul_pos_iff.mp hdu).2
  rcases hrole with rfl | rfl
  · simp [actual, logFactor, mul_comm]
  · rw [show decide (Role.logarithm = .logarithm) = true from by simp,
      logFactor_brun hU hd hu]
    simp only [actual, roughLog]
    ring

/-- On the existing upper long rectangle the ACTUAL transition is one.
This attaches the smoothed Mellin/log weight to the right-closed HB
ownership convention, rather than to an invented mode family. -/
theorem owned_upper_profile {b : Block} {d u : ℕ} {delta : ℝ}
    (hd : 0 < d) (hOwn : Owns b (d*u)) (hdelta : 0 < delta)
    (isLog : Bool) (t : ℝ) :
    profile false isLog delta
      (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b) t
      ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) =
    (logFactor isLog (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b)
      ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) : ℂ) *
    phase t ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) := by
  have hx := owned_brun_ratio_mem hd hOwn
  simp only [profile, twisted, amplitude, transition, Bool.false_eq_true, if_false,
    ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles.upper,
    ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles.doubleStep_one hdelta hx,
    one_mul]

def mellinBrunCore (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (m d₁ d₂ a q : ℕ) : ℂ :=
  fixedMCore (wideWindow (U/d₁)) (wideWindow (V/d₂)) (m*d₁*d₂) a q alpha
    (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂) (U/d₁) (V/d₂)

theorem mellinBrunCore_exact (delta U V t₁ t₂ : ℝ) (label : Fin 3)
    (log₁ log₂ : Bool) (alpha : ℂ) (m d₁ d₂ a q : ℕ) :
    mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d₁ d₂ a q =
      (∑ u ∈ wideWindow (U/d₁), ∑ v ∈ wideWindow (V/d₂),
        if (m*d₁*d₂)*u*v % q = a % q then
          alpha * leftMellin delta U t₁ label log₁ ((u : ℝ)/(U/d₁)) *
            rightMellin delta V t₂ label log₂ ((v : ℝ)/(V/d₂)) else 0) -
      (((Nat.totient q : ℝ)⁻¹ : ℂ) *
        ∑ u ∈ wideWindow (U/d₁), ∑ v ∈ wideWindow (V/d₂),
          if Nat.Coprime ((m*d₁*d₂)*u*v) q then
            alpha * leftMellin delta U t₁ label log₁ ((u : ℝ)/(U/d₁)) *
              rightMellin delta V t₂ label log₂ ((v : ℝ)/(V/d₂)) else 0) :=
  fixedMCore_exact _ _ _ _ _ _ _ _ _ _

def pairCost (delta U V H : ℝ) : ℝ :=
  internalP2Constant*profileConstant^2*logSize U*logSize V*(1+H)^4/delta^4

theorem pairCost_nonneg (delta U V H : ℝ) : 0 ≤ pairCost delta U V H := by
  have hU := zero_le_one.trans (logSize_one_le U)
  have hV := zero_le_one.trans (logSize_one_le V)
  have hP := internalP2Constant_pos.le
  unfold pairCost
  positivity

/-- Actual smooth count minus its unchanged exact coprime mean, for all
three old Brun labels, with a fixed polynomial in the retained frequency.
There is no hP2 premise and no condition on the expanded short product. -/
theorem mellinBrunCore_internalP2 (hWeil : CompositeWeilInput)
    {delta U V H t₁ t₂ : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (label : Fin 3) (log₁ log₂ : Bool) (alpha : ℂ) (m d₁ d₂ a q : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d₁ d₂ a q‖ ≤
      pairCost delta U V H * ‖alpha‖ * modulusBudget q := by
  have hD₁ : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hD₂ : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hp := naturalCore_P2 hWeil
    (profileSchwartz (decide (label=1)) log₁ hd hs U t₁)
    (profileSchwartz (decide (label=2)) log₂ hd hs V t₂)
    (profile_support _ _ hd hs _ _) (profile_support _ _ hd hs _ _)
    (div_pos hU hD₁) (div_pos hV hD₂) (m*d₁*d₂) a q hq ha alpha
  have hNL := N2_nonneg (leftMellin delta U t₁ label log₁)
  have hNR := N2_nonneg (rightMellin delta V t₂ label log₂)
  have hP := internalP2Constant_pos.le
  have hB := modulusBudget_nonneg q
  have hL := zero_le_one.trans (logSize_one_le U)
  have hR := zero_le_one.trans (logSize_one_le V)
  have hC := costs_nonneg.2.2
  calc
    _ ≤ internalP2Constant*‖alpha‖*N2 (leftMellin delta U t₁ label log₁)*
        N2 (rightMellin delta V t₂ label log₂)*modulusBudget q := hp
    _ ≤ internalP2Constant*‖alpha‖*(profileConstant*logSize U*(1+H)^2/delta^2)*
        (profileConstant*logSize V*(1+H)^2/delta^2)*modulusBudget q := by
      gcongr
      · exact profile_N2_cube _ _ hd hs hH ht₁ U
      · exact profile_N2_cube _ _ hd hs hH ht₂ V
    _ = _ := by unfold pairCost; field_simp [hd.ne']; ring

theorem mellinBrunCore_q1 (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (m d₁ d₂ a : ℕ) :
    mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d₁ d₂ a 1 = 0 :=
  naturalCore_q1 _ _ _ _ _ _ _ _ _

/-- Same Q, signed rho, Brun coefficients and short amplitude on BOTH
sides of each original count/mean. The physical modulus moment is left
visible; assuming it paid would be an unproved E4 assembly step. -/
theorem finite_sameRho_mellinBrun (hWeil : CompositeWeilInput)
    {delta U V H t₁ t₂ : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (label : Fin 3) (log₁ log₂ : Bool) (m a : ℕ) (Q : Finset ℕ) (R : Finset (ℕ×ℕ))
    (rho : ℕ → ℂ) (alpha c : (ℕ×ℕ) → ℂ)
    (hQ : ∀ q ∈ Q, 0 < q ∧ Nat.Coprime a q)
    (hR : ∀ d ∈ R, 0 < d.1 ∧ 0 < d.2) :
    ‖∑ q ∈ Q, rho q * ∑ d ∈ R, c d *
      mellinBrunCore delta U V t₁ t₂ label log₁ log₂ (alpha d) m d.1 d.2 a q‖ ≤
    pairCost delta U V H * (∑ d ∈ R, ‖c d‖*‖alpha d‖) *
      (∑ q ∈ Q, ‖rho q‖*modulusBudget q) := by
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ d ∈ R, c d *
        mellinBrunCore delta U V t₁ t₂ label log₁ log₂ (alpha d) m d.1 d.2 a q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ∑ d ∈ R, ‖c d‖ *
        ‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ (alpha d) m d.1 d.2 a q‖ := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ∑ d ∈ R, ‖c d‖ *
        (pairCost delta U V H*‖alpha d‖*modulusBudget q) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro d hdr
      exact mul_le_mul_of_nonneg_left
        (mellinBrunCore_internalP2 hWeil hd hs hU hV hH ht₁ ht₂ label log₁ log₂
          (alpha d) m d.1 d.2 a q (hR d hdr).1 (hR d hdr).2 (hQ q hq).1 (hQ q hq).2)
        (norm_nonneg _)
    _ = ∑ q ∈ Q,
        (pairCost delta U V H * ∑ d ∈ R, ‖c d‖*‖alpha d‖)*
          (‖rho q‖*modulusBudget q) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [Finset.mul_sum]

/- The original normalized geometric Fourier coefficient, from H's
genuine lower caller. Its whole-group reciprocal logs remain inside A. -/
def normalizedCoefficient {r : ℕ} (kappa : ℝ) (B N : ℕ) (owner : Fin r → Fin 1)
    (U : Fin r → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ) (xi : Fin r → ℝ) : ℂ :=
  ImbalancedChen.P5Z.ActualEuclideanPhysicalFourier.physicalFourier r
    (ImbalancedChen.P5Z.ActualLowerNormalizedHBSource.euclideanChart
      kappa B N owner U R kappa0) xi

/-- Pointwise P2 for the REAL normalized lower-chart coefficient.
All fixed short phases have unit norm. No Family supplier and no equality
of this Fourier coefficient with an unnormalized chart is assumed. -/
theorem normalized_selected_mode_P2 (hWeil : CompositeWeilInput)
    {r : ℕ} (kappa : ℝ) (B N : ℕ) (owner : Fin r → Fin 1)
    (U : Fin r → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ)
    (xi z : Fin r → ℝ) (i j : Fin r) {delta H : ℝ}
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : ∀ a, 0 < U a)
    (hH : 0 ≤ H) (hxi : ∀ a, |xi a| ≤ H)
    (label : Fin 3) (log₁ log₂ : Bool) (m d₁ d₂ a q : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ‖mellinBrunCore delta (U i) (U j) (xi i) (xi j) label log₁ log₂
      (selectedAmplitude (normalizedCoefficient kappa B N owner U R kappa0) xi z i j)
      m d₁ d₂ a q‖ ≤ pairCost delta (U i) (U j) H *
      ‖normalizedCoefficient kappa B N owner U R kappa0 xi‖ * modulusBudget q := by
  simpa only [selectedAmplitude_norm] using mellinBrunCore_internalP2 hWeil hd hs
    (hU i) (hU j) hH (hxi i) (hxi j) label log₁ log₂
    (selectedAmplitude (normalizedCoefficient kappa B N owner U R kappa0) xi z i j)
    m d₁ d₂ a q hd₁ hd₂ hq ha

end
end ImbalancedChen.Part3.TwoLongHBMellinBrunProfiles
