import ImbalancedChen.Part5OriginalH430ClassicalPowerTransport

/-! The unchanged Fine selection for the full classical clamp, with the
signed prime discrepancy replaced at arbitrary physical relative accuracy
by the actual all-group HB atlas on the same coefficient. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalFineRoughAtlas
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve)
open P4AOriginalFiniteAll22FineDensity (modulusFamily coefficientFamily)
open P2SeedOmegaLiteralFunctional (switchCost)
open Part5OriginalH430RootIntervalTheta (clampLevel clampMass)
open Part5OriginalH430ClassicalFixedClampMarks (count)
open Part5OriginalH430ClassicalSmoothPositiveSieve (whole signedPart)
open Part5OriginalH430ClassicalSmoothFineSelected (selected_signed_only)
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open Part5OriginalH430ClassicalSmoothNativeSignedSum (nativeResidual selected_fine_residual)
open Part5OriginalH430ClassicalPowerTransport (roughAtlas fine_clamp)
open scoped Classical Topology BigOperators

theorem selected_rough_atlas {root : ℕ} {t₀ κ ε : ℝ} (ht : 0≤t₀) (ht' : t₀≤1/12)
    (hroot : 1/((root:ℝ)+1)≤11/384) (hk : 0<κ) (hk' : κ≤1/112) (he : 0<ε)
    (κ₀ : ℝ) (hκ₀ : 0<κ₀) (hκ₁ : κ₀<1) (eMax : ℝ) (heMax : 0<eMax) :
    let μ := clampLevel root t₀
    ∃ h δ c : ℝ,∃ hh : 0<h,∃ hh' : h≤1/8,∃ hd : 0<δ,∃ hc : 0<c,∃ hc' : c≤1/8,
    ∃ m0 : ℕ,∀ m≥m0,∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,
    ∃ E : ℝ,0<E ∧ E≤eMax ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E →
    ∀ a : ℝ,0<a → a≤1/800 → ∀ qMin mMin : ℕ,
    ∃ q : ℕ,qMin≤q ∧ 0<q ∧ 256∣q ∧ mMin≤refinedMesh q ∧
    ∀ etaPP : ℝ,0<etaPP → etaPP≤P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a) →
    ∀ nu v betaMax extra : ℝ,0<nu → 0<v → nu*v=19/96 → 0<betaMax → 0<extra →
    ∀ fineTolerance : ℝ→ℝ,(∀ beta : ℝ,0<beta → 0<fineTolerance beta) →
    ∃ beta : ℝ,0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2<v ∧
      nu*beta^2<a ∧ nu*beta<1/1000 ∧ nu*beta<etaPP/32 ∧ nu*beta<extra/32 ∧
    ∃ k : ℕ,
      alignedWidth (jointIndex (bank m) (data e q a).m) k≤fineTolerance beta ∧
      alignedWidth (jointIndex (bank m) (data e q a).m) k*
        ((P4AHeldTaggedCompilerSupport.J0 (nu*beta^2):ℝ)+1)≤etaPP ∧
      alignedWidth (jointIndex (bank m) (data e q a).m) k*
        ((P4AHeldTaggedCompilerSupport.J0 (nu*beta^2):ℝ)+1)≤extra ∧
      ∀ᶠ N : ℕ in atTop,Even N →
        let ω := nu*beta^2
        let τ := alignedWidth (jointIndex (bank m) (data e q a).m) k
        let D := modulusFamily nu beta 0 N
        let R := coefficientFamily m r n e q a nu beta k 0 N
        P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms
          m n N (width r) ω τ (nu*beta) etaPP (data e q a) ∧
        ((N:ℝ)/log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense
          (F (bank m) (width r) n (data e q a) ω N) (fun _ => []) N N
          ((N:ℝ)^ω) (cutoff N) τ ((N:ℝ)^(nu*beta))<compilerReserve*singularNormalization N ∧
        (∀ d : ℕ,R d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
        physicalDensitySum D R≤currentK*(singularSeries N/log (N:ℝ)) ∧
        count true 1 N μ κ≤switchCost*clampMass N root t₀+ε*clampMass N root t₀+
          (roughAtlas (family μ hd hh hh' hc hc') N κ₀ D R).re := by
  let μ := clampLevel root t₀
  obtain ⟨h,δ,c,hh,hh',hd,hc,hc',m0,H⟩ :=
    selected_signed_only ht ht' hroot hk hk' (half_pos he) eMax heMax
  refine ⟨h,δ,c,hh,hh',hd,hc,hc',m0,?_⟩
  intro m hm
  obtain ⟨r0,H⟩ := H m hm
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,H⟩ := H r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨E,hE,hEmax,H⟩ := H n hn
  refine ⟨E,hE,hEmax,?_⟩
  intro e he0 heE a ha ha' qMin mMin
  obtain ⟨q,hq,hqp,hqD,hmesh,H⟩ := H e he0 heE a ha ha' qMin mMin
  refine ⟨q,hq,hqp,hqD,hmesh,?_⟩
  intro etaPP heta hgap nu v betaMax extra hnu hv hcut hbmax hx ft hft
  obtain ⟨beta,hb,hb8,hbM,hbV,hba,hb1,hbe,hbx,k,hkf,hke,hkx,H⟩ :=
    H etaPP heta hgap nu v betaMax extra hnu hv hcut hbmax hx ft hft
  refine ⟨beta,hb,hb8,hbM,hbV,hba,hb1,hbe,hbx,k,hkf,hke,hkx,?_⟩
  filter_upwards [H,fine_clamp μ hd hh hh' hc hc' hκ₀ hκ₁ (half_pos he),
    eventually_ge_atTop (2:ℕ)] with N hs hf hN
  intro heven
  obtain ⟨hatoms,hspend,hrange,hdens,hcount⟩ := hs heven
  refine ⟨hatoms,hspend,hrange,hdens,?_⟩
  let D := modulusFamily nu beta 0 N
  let R := coefficientFamily m r n e q a nu beta k 0 N
  let A := roughAtlas (family μ hd hh hh' hc hc') N κ₀ D R
  let V := nativeResidual N μ hd hh hh' hc hc' D R
  have hnorm : ‖(V:ℂ)-A‖≤(ε/2)*clampMass N root t₀ :=
    hf root t₀ ht ht' hroot m r n e q a nu beta k hrange
  have hupper : V-A.re≤(ε/2)*clampMass N root t₀ := by
    simpa only [Complex.sub_re,Complex.ofReal_re] using (Complex.re_le_norm ((V:ℂ)-A)).trans hnorm
  have hV : whole (signedPart N μ δ h c D R)=V :=
    selected_fine_residual hN root t₀ hd hh hh' hc hc' m r n e q a nu beta k
  change count true 1 N μ κ≤switchCost*clampMass N root t₀+(ε/2)*clampMass N root t₀+
    whole (signedPart N μ δ h c D R) at hcount
  change count true 1 N μ κ≤switchCost*clampMass N root t₀+ε*clampMass N root t₀+A.re
  rw [hV] at hcount
  linarith only [hcount,hupper]

end
end ImbalancedChen.Part5OriginalH430ClassicalFineRoughAtlas

