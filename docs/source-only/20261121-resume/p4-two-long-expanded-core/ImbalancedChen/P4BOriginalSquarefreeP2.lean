import ImbalancedChen.P4BOriginalSquarefreeWeil
import ImbalancedChen.Part3TwoLongHBMellinBrunProfiles

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.
Localize the existing P2 proof to the CURRENT squarefree modulus.
The old complete CompositeWeilInput is neither assumed nor manufactured.
The original centered kernel, both zero axes, UV/q^2, full natural source,
Mellin/log profiles, exact coprime mean and P2 constants are unchanged.
The source receipt records the existing proof blocks reused below.
-/
namespace ImbalancedChen.P4BOriginalSquarefreeP2
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
open Part3.TwoLongLiteralMellinModes
open Part3.TwoLongFixedMRectangularCore
open Part3.TwoLongNaturalPeriodization
open Part3.TwoLongNaturalP1
open Part3.TwoLongP1AxisCancellation
open Part3.TwoLongInternalP2FrequencySums
open Part3.TwoLongFilteredIntegerFrequency
open Part3.TwoLongP2DivisorEnvelope
open Part3.TwoLongN2FourierDecay
open Part3.TwoLongInternalP2Modes
open Part3.TwoLongNaturalInternalP2
open Part3.TwoLongActualThreeBrunP2Receiver
open Part3.TwoLongTransitionMellinN2
open Part3.TwoLongHBMellinBrunProfiles
open Part3.OriginalSmoothPoissonTail
open Part3.OriginalSmoothPoissonTail.Physical
open Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open P4BOriginalSquarefreeWeil
theorem centeredKernel_norm_le {q : ℕ} (hsq : Squarefree q)
    (hq : 0 < q) (b j k : ℤ) (hb : IsUnit (b : ZMod q)) :
    ‖centeredKernel q b j k‖ ≤
      (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*
        Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ) +
      ‖ramanujan q j‖*‖ramanujan q k‖/(Nat.totient q : ℝ) := by
  have hw := squarefree_weil q hsq (b*j) k
  dsimp only [budget] at hw
  rw [primitive_center_gcd hq b j k hb] at hw
  calc
    _ ≤ ‖kloosterman q (b*j) k‖ +
        ‖ramanujan q j * ramanujan q k / (Nat.totient q : ℂ)‖ := norm_sub_le _ _
    _ = ‖kloosterman q (b*j) k‖ +
        ‖ramanujan q j‖*‖ramanujan q k‖/(Nat.totient q : ℝ) := by
      simp only [norm_div,norm_mul,Complex.norm_natCast]
    _ ≤ _ := add_le_add_right hw _

/-- Both actual divisor filters, including the exact 1/phi(q) mean.
This is a pointwise bound on the original kernel, not an invented series. -/
theorem weighted_centeredKernel_le {q : ℕ} (hsq : Squarefree q)
    (H K : ℝ) (hq : 0 < q) (b j k : ℤ) (hb : IsUnit (b : ZMod q)) :
    baseDecay H j*baseDecay K k*‖centeredKernel q b j k‖ ≤
      centeredEnvelope H K q (j,k) := by
  have hH := multipleDecay_nonneg H 1 j
  have hK := multipleDecay_nonneg K 1 k
  have hR := mul_le_mul (weighted_ramanujan_le H q hq j)
    (weighted_ramanujan_le K q hq k)
    (mul_nonneg hK (norm_nonneg _)) (ramanujanEnvelope_nonneg H q j)
  calc
    _ ≤ baseDecay H j*baseDecay K k*
        ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*
          Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ) +
          ‖ramanujan q j‖*‖ramanujan q k‖/(Nat.totient q : ℝ)) :=
      mul_le_mul_of_nonneg_left (centeredKernel_norm_le hsq hq b j k hb)
        (mul_nonneg hH hK)
    _ = (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*
        (baseDecay H j*baseDecay K k*
          Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ)) +
        (Nat.totient q : ℝ)⁻¹*
          ((baseDecay H j*‖ramanujan q j‖)*(baseDecay K k*‖ramanujan q k‖)) := by ring
    _ ≤ (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilEnvelope H K q (j,k) +
        (Nat.totient q : ℝ)⁻¹*(ramanujanEnvelope H q j*ramanujanEnvelope K q k) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (weighted_sqrt_gcd_le H K q hq j k) (by positivity))
        (mul_le_mul_of_nonneg_left hR (by positivity))
    _ = _ := rfl


theorem centeredMode_norm_le {q : ℕ} (hsq : Squarefree q)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hq : 0 < q) (b : ℤ) (hb : IsUnit (b : ZMod q)) (p : ℤ × ℤ) :
    ‖centeredMode F G U V q b p‖ ≤
      ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ))) *
        centeredEnvelope ((q : ℝ)/U) ((q : ℝ)/V) q p := by
  have hA : 0 ≤ fourierDecayConstant*N2 (F : ℝ → ℂ) :=
    mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _)
  have hB : 0 ≤ fourierDecayConstant*N2 (G : ℝ → ℂ) :=
    mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _)
  by_cases hj : p.1=0
  · simp only [centeredMode,hj,centeredKernel_left_axis hq,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg hA hB) (centeredEnvelope_nonneg _ _ _ _)
  by_cases hk : p.2=0
  · simp only [centeredMode,hk,centeredKernel_right_axis hq b p.1 hb,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg hA hB) (centeredEnvelope_nonneg _ _ _ _)
  have hf := fourier_nonzero_le F hq hU p.1 hj
  have hg := fourier_nonzero_le G hq hV p.2 hk
  calc
    _ = ‖(𝓕 F) ((U/q)*(p.1 : ℝ))‖*‖(𝓕 G) ((V/q)*(p.2 : ℝ))‖*
        ‖centeredKernel q b p.1 p.2‖ := by simp only [centeredMode,norm_mul]
    _ ≤ ((fourierDecayConstant*N2 (F : ℝ → ℂ))*baseDecay ((q : ℝ)/U) p.1)*
        ((fourierDecayConstant*N2 (G : ℝ → ℂ))*baseDecay ((q : ℝ)/V) p.2)*
        ‖centeredKernel q b p.1 p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hf hg (norm_nonneg _)
          (mul_nonneg hA (multipleDecay_nonneg _ 1 _))) (norm_nonneg _)
    _ = ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))*
        (baseDecay ((q : ℝ)/U) p.1*baseDecay ((q : ℝ)/V) p.2*
          ‖centeredKernel q b p.1 p.2‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_centeredKernel_le hsq _ _ hq b p.1 p.2 hb) (mul_nonneg hA hB)

/-- Actual product-index absolute convergence follows from the proved
divisor envelope. In particular the nested P1 sum can be commuted. -/
theorem centeredMode_norm_summable {q : ℕ} (hsq : Squarefree q)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hq : 0 < q) (b : ℤ) (hb : IsUnit (b : ZMod q)) :
    Summable (fun p : ℤ × ℤ => ‖centeredMode F G U V q b p‖) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hs := (centeredEnvelope_summable (div_pos hqR hU) (div_pos hqR hV) q).mul_left
    ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _)
    (centeredMode_norm_le hsq F G hU hV hq b hb)

theorem centeredMode_tsum_le {q : ℕ} (hsq : Squarefree q)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hq : 0 < q) (b : ℤ) (hb : IsUnit (b : ZMod q)) :
    ‖∑' j : ℤ, ∑' k : ℤ, centeredMode F G U V q b (j,k)‖ ≤
      ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))*
      (4*((q : ℝ)/U)*((q : ℝ)/V)*
        ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
          (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ))) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let A := (fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ))
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _))
    (mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _))
  have hs := (centeredEnvelope_summable (div_pos hqR hU) (div_pos hqR hV) q).mul_left A
  have hm := centeredMode_norm_summable hsq F G hU hV hq b hb
  rw [← hm.of_norm.tsum_prod]
  calc
    _ ≤ ∑' p : ℤ × ℤ, A*centeredEnvelope ((q : ℝ)/U) ((q : ℝ)/V) q p :=
      tsum_of_norm_bounded hs.hasSum (centeredMode_norm_le hsq F G hU hV hq b hb)
    _ = A * ∑' p : ℤ × ℤ, centeredEnvelope ((q : ℝ)/U) ((q : ℝ)/V) q p := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (centeredEnvelope_tsum_le (div_pos hqR hU) (div_pos hqR hV) q) hA

theorem naturalCore_P2_refined {q : ℕ} (hsq : Squarefree q)
    (F G : 𝓢(ℝ, ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    (hG : Function.support (G : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (m a : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) (alpha : ℂ) :
    ‖fixedMCore (wideWindow U) (wideWindow V) m a q alpha F G U V‖ ≤
      4*fourierDecayConstant^2*‖alpha‖*N2 (F : ℝ → ℂ)*N2 (G : ℝ → ℂ)*
        ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
          (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hFN := N2_nonneg (F : ℝ → ℂ)
  have hGN := N2_nonneg (G : ℝ → ℂ)
  have hW := weilConstant_nonneg
  by_cases hm : Nat.Coprime m q
  · have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hphi : (Nat.totient q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    have haU : IsUnit ((a : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast,ZMod.isUnit_iff_coprime] using ha
    have hmU : IsUnit ((m : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast,ZMod.isUnit_iff_coprime] using hm
    have hb := actual_center_unit (a : ℤ) (m : ℤ) haU hmU
    have hs := centeredMode_tsum_le hsq F G hU hV hq
      ((a : ℤ)*inverseResidue q (m : ℤ)) hb
    rw [naturalCore_P1 F G (compact_of_window F hF) (compact_of_window G hG)
      hF hG hU hV m a hm ha alpha]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (div_pos (mul_pos hU hV) (sq_pos_of_pos hqR))]
    change ‖alpha‖*(U*V/(q : ℝ)^2)*
      ‖∑' j : ℤ, ∑' k : ℤ,
        centeredMode F G U V q ((a : ℤ)*inverseResidue q (m : ℤ)) (j,k)‖ ≤ _
    calc
      _ ≤ ‖alpha‖*(U*V/(q : ℝ)^2)*
          (((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))*
          (4*((q : ℝ)/U)*((q : ℝ)/V)*
            ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
              (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ)))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp [hqR.ne',hU.ne',hV.ne',hphi]; ring
  · rw [naturalCore_zero_of_nonprimitive _ _ m a hm ha alpha F G U V,norm_zero]
    positivity


theorem naturalCore_P2 {q : ℕ} (hsq : Squarefree q)
    (F G : 𝓢(ℝ, ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    (hG : Function.support (G : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (m a : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) (alpha : ℂ) :
    ‖fixedMCore (wideWindow U) (wideWindow V) m a q alpha F G U V‖ ≤
      internalP2Constant*‖alpha‖*N2 (F : ℝ → ℂ)*N2 (G : ℝ → ℂ)*modulusBudget q := by
  have hFN := N2_nonneg (F : ℝ → ℂ)
  have hGN := N2_nonneg (G : ℝ → ℂ)
  apply (naturalCore_P2_refined hsq F G hF hG hU hV m a hq ha alpha).trans
  calc
    _ ≤ (4*fourierDecayConstant^2*‖alpha‖*N2 (F : ℝ → ℂ)*N2 (G : ℝ → ℂ))*
        ((weilConstant+1)*modulusBudget q) :=
      mul_le_mul_of_nonneg_left (arithmetic_budget_le q) (by positivity)
    _ = _ := by unfold internalP2Constant; ring


theorem mellinBrunCore_internalP2 {q : ℕ} (hsq : Squarefree q)
    {delta U V H t₁ t₂ : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (label : Fin 3) (log₁ log₂ : Bool) (alpha : ℂ) (m d₁ d₂ a : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d₁ d₂ a q‖ ≤
      pairCost delta U V H * ‖alpha‖ * modulusBudget q := by
  have hD₁ : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hD₂ : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hp := naturalCore_P2 hsq
    (profileSchwartz (decide (label=1)) log₁ hd hs U t₁)
    (profileSchwartz (decide (label=2)) log₂ hd hs V t₂)
    (profile_support _ _ hd hs _ _) (profile_support _ _ hd hs _ _)
    (div_pos hU hD₁) (div_pos hV hD₂) (m*d₁*d₂) a hq ha alpha
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


end
end ImbalancedChen.P4BOriginalSquarefreeP2
