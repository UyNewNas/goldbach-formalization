import ImbalancedChen.Part3ActualOriginalLContourBounds
import ImbalancedChen.Part3RoughEulerEnvelopePayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pointwise bounds for the ACTUAL original-character rough Perron integrand.
Both roughOne L and roughMobius reciprocal L are paid from24, actual
thin-left Euler ratios from20, and the proved primary Mertens envelope.
The Smooth1 Mellin transform is paid by its genuine C1 decay. Constants
precede original characters, cutoffs, frequencies, heights and scales.
No hleftnorm, hzero, hContour, mass bound or desired saving is assumed.
-/

namespace ImbalancedChen.Part3.ActualRoughContourIntegrandBounds20261026b
noncomputable section
open Classical Complex Set
open RoughQuadraticLowRectangle20261026b ActualRoughContourHolomorphic20261026b
open ActualOriginalLContourBounds20261026b
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open RoughSlotMellinSeries20261026b RoughSlotSmoothedPerron20261026b
open PrimeMellinProfileVariation20261026b RoughFiniteEulerBounds20261026b
open RoughThinEulerUniformComparison20261026b RoughEulerEnvelopePayment20261026b

def contourAmplitude (E C : ℝ) (q : ℕ) (H δ κ z ε : ℝ) : ℝ :=
  (32*rectangleLog q H+originalReciprocalCost q H δ)*
    (thinComparison κ*E*(1+Real.log (max 2 z)))*(C/ε)

theorem originalReciprocalCost_eq_power (q : ℕ) [NeZero q]
    (H : ℝ) {δ : ℝ} (hδ : 0<δ) :
    originalReciprocalCost q H δ=(4/δ)*(128*rectangleLog q H/δ)^40 := by
  have hD : 0<rectangleLog q H:=lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q H)
  have hr : 0<128*rectangleLog q H/δ:=by positivity
  have hb : 0<δ/4:=by positivity
  have hp : Real.exp (40*Real.log (128*rectangleLog q H/δ))=
      (128*rectangleLog q H/δ)^40 := by
    rw [mul_comm (40 : ℝ),Real.exp_mul,Real.exp_log hr]
    norm_num [Real.rpow_natCast]
  rw [originalReciprocalCost,Real.exp_sub,hp,Real.exp_log hb]
  field_simp [hδ.ne']
  ring

theorem thinComparison_ge_one {κ : ℝ} (hκ : 0≤κ) : 1≤thinComparison κ := by
  unfold thinComparison
  exact Real.one_le_exp_iff.mpr
    (mul_nonneg (mul_nonneg universalEulerCost_pos.le hκ) (Real.exp_pos κ).le)

private theorem actual_Euler_bound {E : ℝ} (hE : 0<E)
    (hEnv : ∀ z : ℝ,plusEnvelope z≤E*(1+Real.log (max 2 z)) ∧
      inverseEnvelope z≤E*(1+Real.log (max 2 z)))
    {q : ℕ} (χ : DirichletCharacter ℂ q) {z δ κ : ℝ}
    (hz : 0≤z) (hδ : 0≤δ) (hδ1 : δ≤1/4) (hκ : 0≤κ)
    (hcap : δ*Real.log (max 2 z)≤κ) {s : ℂ} (hs : 1-δ/2≤s.re) :
    ‖finiteCorrection χ z s‖≤thinComparison κ*E*(1+Real.log (max 2 z)) ∧
      ‖(finiteCorrection χ z s)⁻¹‖≤thinComparison κ*E*(1+Real.log (max 2 z)) := by
  have hlog : 0≤Real.log (max 2 z):=Real.log_nonneg
    (le_trans (by norm_num : (1 : ℝ)≤2) (le_max_left _ _))
  have hrepr : (s.re : ℂ)+I*s.im=s:=by simpa only [mul_comm I] using s.re_add_im
  by_cases hs1 : s.re≤1
  · have he:=finiteCorrection_uniform_thin_envelopes χ hz hδ hδ1 hcap
      (by linarith : 1-δ≤s.re) hs1 s.im
    rw [hrepr] at he
    exact ⟨he.1.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hEnv z).1 (thinComparison_pos κ).le),
      he.2.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hEnv z).2 (thinComparison_pos κ).le)⟩
  · have he:=finiteCorrection_bounds χ z (le_of_lt (lt_of_not_ge hs1))
    have hpay : E*(1+Real.log (max 2 z))≤thinComparison κ*E*(1+Real.log (max 2 z)):=by
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right
        (thinComparison_ge_one hκ) (mul_nonneg hE.le (by linarith))
    exact ⟨he.2.1.trans ((hEnv z).1.trans hpay),he.2.2.trans ((hEnv z).2.trans hpay)⟩

/-- D uses ORIGINAL q and the actual moving frequency height H=T+abs tau.
The reciprocal polynomial is displayed explicitly above, and the Euler
envelope has exponent1 in log(max2z). -/
theorem exists_actual_rough_integrand_bounds (η : ℝ) (hη : 0<η) :
    ∃ c A E : ℝ,0<c ∧ 0<A ∧ 0<E ∧ ∀ (ν : ℝ → ℝ),
      ContDiff ℝ 1 ν → Function.support ν⊆Icc (1/2) 2 → ∃ C : ℝ,0<C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ (useMu : Bool) (z τ U T X ε δ κ : ℝ),
      0≤z → 0≤T → 0<X → 0<ε → ε<1 → 0<δ → 0≤κ →
      δ≤conductorWidth c A η χ (T+|τ|) → δ≤1/rectangleLog q (T+|τ|) →
      δ*Real.log (max 2 z)≤κ → ∀ s : ℂ,
      1-δ/2≤s.re → s.re≤1+δ → |s.im|≤T →
      ‖roughPerronIntegrand useMu χ z τ U ν ε X s‖≤
        contourAmplitude E C q (T+|τ|) δ κ z ε*X^s.re/‖s‖^2 := by
  obtain ⟨c,A,hc,hA,hL⟩:=exists_actual_original_L_contour_bounds η hη
  obtain ⟨E,hE,hEnv⟩:=exists_euler_envelopes_le_log
  refine ⟨c,A,E,hc,hA,hE,?_⟩
  intro ν hν hsupp
  obtain ⟨C,hC,hM⟩:=MellinOfSmooth1b hν hsupp
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ useMu z τ U T X ε δ κ hz hT hX hε hε1 hδ hκ hwidth hsmall hcap s hslo hshi hst
  let H:=T+|τ|
  let B:=32*rectangleLog q H+originalReciprocalCost q H δ
  let F:=thinComparison κ*E*(1+Real.log (max 2 z))
  have hδ1 : δ≤1/4:=hwidth.trans (conductorWidth_le_quarter c A η χ H)
  have hshiftH : |(shiftedExponent s τ).im|≤H:=by
    simp only [shiftedExponent,sub_im,mul_im,I_re,ofReal_im,zero_mul,I_im,ofReal_re,
      one_mul,zero_add]
    exact (abs_sub _ _).trans (add_le_add_right hst _)
  have hLs:=hL q χ hχ H δ s.re (shiftedExponent s τ).im (by positivity)
    hδ hwidth hsmall hshiftH hslo hshi
  have hrepr : (s.re : ℂ)+I*(shiftedExponent s τ).im=shiftedExponent s τ:=by
    rw [← shiftedExponent_re s τ]
    simpa only [mul_comm I] using (shiftedExponent s τ).re_add_im
  rw [hrepr] at hLs
  have hD : 0<rectangleLog q H:=lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q H)
  have hB : 0≤B:=by dsimp [B,originalReciprocalCost]; positivity
  have hF : 0≤F:=by
    dsimp [F]
    have hlog : 0≤Real.log (max 2 z):=Real.log_nonneg
      (le_trans (by norm_num : (1 : ℝ)≤2) (le_max_left _ _))
    positivity
  have hLc : ‖χ.LFunction (shiftedExponent s τ)‖≤B:=
    hLs.1.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  have hLi : ‖(χ.LFunction (shiftedExponent s τ))⁻¹‖≤B:=
    hLs.2.trans (le_add_of_nonneg_left (by positivity))
  have hEuler:=actual_Euler_bound hE hEnv χ hz hδ.le hδ1 hκ hcap
    (by simpa only [shiftedExponent_re] using hslo : 1-δ/2≤(shiftedExponent s τ).re)
  have htransform : ‖roughTransform useMu χ z τ U s‖≤B*F:=by
    cases useMu
    · simpa only [roughTransform,Bool.false_eq_true,if_false,norm_mul,phase_norm,one_mul] using
        mul_le_mul hLc hEuler.1 (norm_nonneg _) hB
    · have hprod : (∏ p∈smallPrimes z,(1-χ p*(p : ℂ)^(-shiftedExponent s τ))⁻¹)=
          (finiteCorrection χ z (shiftedExponent s τ))⁻¹:=by
        simp only [finiteCorrection,Finset.prod_inv_distrib]
      simpa only [roughTransform,Bool.true_eq_true,if_true,hprod,norm_mul,phase_norm,one_mul] using
        mul_le_mul hLi hEuler.2 (norm_nonneg _) hB
  have hRe : 0<s.re:=by linarith
  have hMellin:=hM (1/2) (by norm_num) s (by linarith) (by linarith) ε hε hε1
  dsimp only [roughPerronIntegrand]
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX]
  calc
    _ ≤ (B*F)*(C*(ε*‖s‖^2)⁻¹)*X^s.re:=
      mul_le_mul_of_nonneg_right (mul_le_mul htransform hMellin (norm_nonneg _) (mul_nonneg hB hF))
        (Real.rpow_nonneg hX.le _)
    _ = _:=by
      dsimp [B,F,contourAmplitude,H]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end
end ImbalancedChen.Part3.ActualRoughContourIntegrandBounds20261026b
