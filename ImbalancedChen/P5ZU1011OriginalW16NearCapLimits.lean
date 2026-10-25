import ImbalancedChen.P5ZU1011OriginalW16NearCapNative

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Actual right limits of the near-cap W native parameters. The physical
callers use eta>0; eta=0 is only the boundary value of the rational
parameter functions. This supplies no zero-rho Rosser estimate and no
H248 density limit. The residual exponent and actual lowered cutoff
exponent have their explicit ORIGINAL fixed-box boundary values.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NearCapLimits
noncomputable section
open Filter Topology
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalW16NearCapNative
open U1011OriginalW16FixedCellNative (G G_lt_capLower Tplus)

theorem nu_at_zero (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true) :
    nu B 0=capLower wPolicy B := by
  have hg := G_lt_capLower B htest
  unfold nu NearCapRationalParameters.level NearCapRationalParameters.capLoss
  rw [min_eq_left (by linarith)]
  ring

theorem delta_at_zero (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true) : delta B 0=0 := by
  have hg := G_lt_capLower B htest
  change min (3/4096:ℚ) (min ((nu B 0-G B)/64) ((capLower wPolicy B-nu B 0)/64))=0
  rw [nu_at_zero B htest,sub_self,zero_div,min_eq_right (by linarith),min_eq_right (by norm_num)]

theorem xi_at_zero (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true) (hw : 0<B.lo 3) :
    xi B 0=0 := by
  change min (B.lo 3/2) (delta B 0)=0
  rw [delta_at_zero B htest,min_eq_right (by linarith)]

theorem continuous_nu (B : Box) : Continuous (nu B) := by
  unfold nu NearCapRationalParameters.level NearCapRationalParameters.capLoss
  fun_prop
theorem continuous_delta (B : Box) : Continuous (delta B) := by
  unfold delta NearCapRationalParameters.delta NearCapRationalParameters.level NearCapRationalParameters.capLoss
  fun_prop
theorem continuous_xi (B : Box) : Continuous (xi B) := by
  unfold xi NearCapRationalParameters.xi NearCapRationalParameters.delta
    NearCapRationalParameters.level NearCapRationalParameters.capLoss
  fun_prop
theorem continuous_rho (B : Box) : Continuous (rho B) := continuous_delta B

/-- Genuine right limits at fixed actual W box, not a midpoint family.
The error statements in the native module also give an explicit modulus. -/
theorem tendsto_precision_parameters (B : Box)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hw : 0<B.lo 3) :
    Tendsto (nu B) (𝓝[>] (0:ℚ)) (𝓝 (capLower wPolicy B)) ∧
      Tendsto (delta B) (𝓝[>] (0:ℚ)) (𝓝 0) ∧
      Tendsto (xi B) (𝓝[>] (0:ℚ)) (𝓝 0) ∧ Tendsto (rho B) (𝓝[>] (0:ℚ)) (𝓝 0) := by
  have hn : Tendsto (nu B) (𝓝 (0:ℚ)) (𝓝 (nu B 0)) := (continuous_nu B).continuousAt
  have hd : Tendsto (delta B) (𝓝 (0:ℚ)) (𝓝 (delta B 0)) := (continuous_delta B).continuousAt
  have hx : Tendsto (xi B) (𝓝 (0:ℚ)) (𝓝 (xi B 0)) := (continuous_xi B).continuousAt
  rw [nu_at_zero B htest] at hn
  rw [delta_at_zero B htest] at hd
  rw [xi_at_zero B htest hw] at hx
  exact ⟨hn.mono_left nhdsWithin_le_nhds,hd.mono_left nhdsWithin_le_nhds,
    hx.mono_left nhdsWithin_le_nhds,hd.mono_left nhdsWithin_le_nhds⟩

theorem residual_at_zero (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true) :
    residualExponent B 0=capLower wPolicy B-Tplus B := by
  simp only [residualExponent,nu_at_zero B htest,delta_at_zero B htest,mul_zero,sub_zero]

theorem cutoff_at_zero (B : Box) (htest : wholeBoxEligibleTest wPolicy B=true) (hw : 0<B.lo 3) :
    cutoffExponent B 0=min (B.lo 3) ((capLower wPolicy B-Tplus B)/2) := by
  have hr : rho B 0=0 := delta_at_zero B htest
  simp only [cutoffExponent,xi_at_zero B htest hw,residual_at_zero B htest,hr,sub_zero,add_zero]

theorem tendsto_native_exponents (B : Box)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hw : 0<B.lo 3) :
    Tendsto (residualExponent B) (𝓝[>] (0:ℚ)) (𝓝 (capLower wPolicy B-Tplus B)) ∧
      Tendsto (cutoffExponent B) (𝓝[>] (0:ℚ))
        (𝓝 (min (B.lo 3) ((capLower wPolicy B-Tplus B)/2))) := by
  have hn := (continuous_nu B).continuousAt (x:= (0:ℚ))
  have hd := (continuous_delta B).continuousAt (x:= (0:ℚ))
  have hx := (continuous_xi B).continuousAt (x:= (0:ℚ))
  have hr := (continuous_rho B).continuousAt (x:= (0:ℚ))
  have hre : ContinuousAt (residualExponent B) 0 := by
    unfold residualExponent
    fun_prop
  have hden : (2:ℚ)+rho B 0≠0 := by
    change (2:ℚ)+delta B 0≠0
    rw [delta_at_zero B htest]
    norm_num
  have hcut : ContinuousAt (cutoffExponent B) 0 := by
    unfold cutoffExponent
    fun_prop
  have hrelim : Tendsto (residualExponent B) (𝓝 (0:ℚ)) (𝓝 (residualExponent B 0)) := hre
  have hcutlim : Tendsto (cutoffExponent B) (𝓝 (0:ℚ)) (𝓝 (cutoffExponent B 0)) := hcut
  rw [residual_at_zero B htest] at hrelim
  rw [cutoff_at_zero B htest hw] at hcutlim
  exact ⟨hrelim.mono_left nhdsWithin_le_nhds,hcutlim.mono_left nhdsWithin_le_nhds⟩

end
end ImbalancedChen.P5Z.U1011OriginalW16NearCapLimits
