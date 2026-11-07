import ImbalancedChen.P2GammaPrimitiveScaleThreshold

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.

The original target T and complete local product scale x remain distinct.
These are the elementary transports required by the source note, lines
134-138. They do not assert that a particular Gamma chart has the required
lower scale bound or a post-loss below-half gap.
-/

namespace ImbalancedChen.P2GammaOriginalScaleTransport
noncomputable section
open Filter

/-- A fixed chart constant in c0*T^beta is absorbed by a strictly smaller
positive exponent before the original-target threshold is selected. -/
theorem eventually_power_le_fixed_multiple_power (betaLower beta c0 : ℝ)
    (hgap : betaLower<beta) (hc0 : 0<c0) :
    ∀ᶠ T : ℝ in atTop,1≤T ∧ T^betaLower≤c0*T^beta := by
  have hlarge : ∀ᶠ T : ℝ in atTop,1/c0≤T^(beta-betaLower) :=
    (tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually_ge_atTop _
  filter_upwards [hlarge,eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hTpos : 0<T := zero_lt_one.trans_le hT1
  have hcost : 1≤c0*T^(beta-betaLower) := by
    have h := (div_le_iff₀ hc0).mp hT
    simpa only [mul_comm] using h
  have hpower : T^betaLower*T^(beta-betaLower)=T^beta := by
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  refine ⟨hT1,?_⟩
  calc
    T^betaLower = T^betaLower*1 := by ring
    _ ≤ T^betaLower*(c0*T^(beta-betaLower)) :=
      mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hTpos.le _)
    _ = c0*(T^betaLower*T^(beta-betaLower)) := by ring
    _ = c0*T^beta := by rw [hpower]

/-- One original-target threshold works for every later complete scale
above T^beta. The threshold depends only on the already fixed local
threshold and beta, and precedes every chart and all of its arithmetic data. -/
theorem exists_original_scale_common_threshold (x0 beta : ℝ) (hbeta : 0<beta) :
    ∃ T0 : ℝ,1<T0 ∧ ∀ T : ℝ,T0≤T → ∀ x : ℝ,T^beta≤x → x0≤x := by
  have hlarge : ∀ᶠ T : ℝ in atTop,x0≤T^beta :=
    (tendsto_rpow_atTop hbeta).eventually_ge_atTop x0
  obtain ⟨T1,hT1⟩ := eventually_atTop.mp hlarge
  refine ⟨max 2 T1,by linarith [le_max_left (2 : ℝ) T1],?_⟩
  intro T hT x hx
  exact (hT1 T ((le_max_right _ _).trans hT)).trans hx

/-- The actual local logarithmic error unit transports to the original
target with an explicit fixed coefficient. Only the physical upper/lower
scale comparisons are premises; no discrepancy estimate is assumed. -/
theorem local_log_unit_le_original (A beta c T x : ℝ)
    (hA : 0≤A) (hbeta : 0<beta) (hc : 0≤c) (hT : 1<T)
    (hlower : T^beta≤x) (hupper : x≤c*T) :
    x/(Real.log x)^A≤(c/beta^A)*T/(Real.log T)^A := by
  have hTpos : 0<T := zero_lt_one.trans hT
  have hxpos : 0<x := (Real.rpow_pos_of_pos hTpos beta).trans_le hlower
  have hlogT : 0<Real.log T := Real.log_pos hT
  have hlogs : beta*Real.log T≤Real.log x := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hTpos beta) hlower
    simpa only [Real.log_rpow hTpos] using h
  have hlogx : 0<Real.log x := (mul_pos hbeta hlogT).trans_le hlogs
  have hden : beta^A*(Real.log T)^A≤(Real.log x)^A := by
    rw [← Real.mul_rpow hbeta.le hlogT.le]
    exact Real.rpow_le_rpow (mul_nonneg hbeta.le hlogT.le) hlogs hA
  calc
    _ ≤ (c*T)/(Real.log x)^A :=
      div_le_div_of_nonneg_right hupper (Real.rpow_nonneg hlogx.le A)
    _ ≤ (c*T)/(beta^A*(Real.log T)^A) :=
      div_le_div_of_nonneg_left (mul_nonneg hc hTpos.le)
        (mul_pos (Real.rpow_pos_of_pos hbeta A) (Real.rpow_pos_of_pos hlogT A)) hden
    _ = _ := by ring

end
end ImbalancedChen.P2GammaOriginalScaleTransport
