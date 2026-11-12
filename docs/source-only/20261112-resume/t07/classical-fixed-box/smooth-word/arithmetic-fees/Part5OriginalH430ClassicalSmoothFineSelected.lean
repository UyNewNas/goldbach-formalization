import ImbalancedChen.Part5OriginalH430ClassicalSmoothDensityPrice
import ImbalancedChen.P4AOriginalFiniteAll22FineDensity

/-! The original cofinal Fine selection consumes the ordinary density on
its own coefficient. Its physical range and high-atom budgets survive.
Only the actual signed prime-product sum remains on this clamp upper side. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothFineSelected
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
open P4AOriginalFiniteAll22FineDensity (modulusFamily coefficientFamily exists_fine_same_rho_hdensity)
open P2SeedOmegaLiteralFunctional (switchCost)
open Part5OriginalH430RootIntervalTheta (clampLevel clampMass)
open Part5OriginalH430ClassicalFixedClampMarks (count)
open Part5OriginalH430ClassicalSmoothPositiveSieve (whole signedPart)
open Part5OriginalH430ClassicalSmoothDensityPrice (choose_outer)
open scoped Classical Topology BigOperators

theorem selected_signed_only {root : ℕ} {t₀ κ ε : ℝ} (ht : 0≤t₀) (ht' : t₀≤1/12)
    (hroot : 1/((root:ℝ)+1)≤11/384) (hk : 0<κ) (hk' : κ≤1/112) (he : 0<ε)
    (eMax : ℝ) (heMax : 0<eMax) :
    let μ := clampLevel root t₀
    ∃ h δ c : ℝ,0<h ∧ h≤1/8 ∧ 0<δ ∧ 0<c ∧ c≤1/8 ∧
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
          whole (signedPart N μ δ h c D R) := by
  obtain ⟨h,δ,c,hh,hh',hd,hc,hc',outer⟩ := choose_outer ht ht' hroot hk hk' he
  obtain ⟨m0,hM⟩ := exists_fine_same_rho_hdensity eMax heMax
  refine ⟨h,δ,c,hh,hh',hd,hc,hc',m0,?_⟩
  intro m hm
  obtain ⟨r0,hR⟩ := hM m hm
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨E,hE,hEmax,hq⟩ := hN n hn
  refine ⟨E,hE,hEmax,?_⟩
  intro e he0 heE a ha ha' qMin mMin
  obtain ⟨q,hq0,hqp,hqD,hmesh,hs⟩ := hq e he0 heE a ha ha' qMin mMin
  refine ⟨q,hq0,hqp,hqD,hmesh,?_⟩
  intro etaPP heta hgap nu v betaMax extra hnu hv hcut hbmax hx ft hft
  obtain ⟨beta,hb,hb8,hbM,hbV,hba,hb1,hbe,hbx,k,hkf,hke,hkx,_,N0,hN0,hsel⟩ :=
    hs etaPP heta hgap nu v betaMax extra hnu hv hcut hbmax hx ft hft
  refine ⟨beta,hb,hb8,hbM,hbV,hba,hb1,hbe,hbx,k,hkf,hke,hkx,?_⟩
  filter_upwards [outer,eventually_ge_atTop N0] with N hu hlarge
  intro heven
  obtain ⟨hatoms,hspend,_,hdens,hrange,_⟩ := hsel N hlarge heven
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hβ1 : beta≤1 := by linarith only [hb8]
  have hβsq : beta^2≤beta := by simpa only [pow_two,mul_one] using
    mul_le_mul_of_nonneg_left hβ1 hb.le
  have hwz : nu*beta^2≤19/96 := by
    rw [←hcut]
    exact mul_le_mul_of_nonneg_left hbV.le hnu.le
  have hL : (1:ℝ)<(N:ℝ)^(nu*beta) := one_lt_rpow hNr (mul_pos hnu hb)
  have hwL := rpow_le_rpow_of_exponent_le hNr.le (mul_le_mul_of_nonneg_left hβsq hnu.le)
  have hzN : cutoff N≤(N:ℝ) := by
    calc
      _ ≤ (N:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (19/96:ℝ)≤1)
      _ = _ := rpow_one _
  exact ⟨hatoms,hspend,hrange,hdens,hu heven (bank m) r n e q a (nu*beta^2)
    (alignedWidth (jointIndex (bank m) (data e q a).m) k) ((N:ℝ)^(nu*beta))
    hL hwL (rpow_le_rpow_of_exponent_le hNr.le hwz) hzN hdens⟩

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothFineSelected

