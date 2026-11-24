import ImbalancedChen.P4AOrderedThirdRectangleRate
import ImbalancedChen.P4AFull87RoughEulerRatio

namespace ImbalancedChen.P4AOrderedThirdRectanglePayment
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOrderedThirdRoughCutTransport (F rough_equal projected_cut)
open P4AOrderedThirdRectangleRate (count rate)
open P4AUpperTaggedParityCompiler (changedMass)
open P4AFull87PhysicalReserveFromRate (of_wallRate)

/-- Freeze the entire geometry, including ordered-portion Γ labels,
R4/R5 sources, complete R6 and all R8 action/rounding rows, before
the physical rough exponent. The arithmetic labels are rectangular. -/
theorem fixed_rate (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e) :
    ∃ K E : ℝ, 1<K ∧ 1<E ∧ ∀ B : ℝ, 0≤B → ∀ N cap : ℕ, 2≤N → Even N →
    ∀ omega v tau : ℝ, 0<omega → omega≤v → v≤1 → 0<tau → 3≤(N:ℝ)^omega → E≤omega*Real.log (N:ℝ) →
    (B/omega)*changedMass (F delta n d omega N) (fun _ => []) N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau ≤
      ((count delta n d:ℝ)*150*B*tau+(count delta n d:ℝ)*10*B*K/Real.log (N:ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,h⟩ := rate delta hd n d he (fun _ _ => [])
  refine ⟨K,E,hK,hE,?_⟩
  intro B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog
  rw [(rough_equal delta n d (by omega : 1≤N) cap hw.le ((N:ℝ)^v) tau 1 (fun _ => [])).2.1]
  exact h B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog

theorem rough_ratio (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e) :
    ∃ K E : ℝ, 1<K ∧ 1<E ∧ ∀ N cap : ℕ, 2≤N → Even N → ∀ omega v tau : ℝ,
      0<omega → omega≤v → v≤1 → 0<tau → 3≤(N:ℝ)^omega → E≤omega*Real.log (N:ℝ) →
      let w := (N:ℝ)^omega
      let z := (N:ℝ)^v
      let U := P4AUpperTaggedParityCompiler.universe N cap w z
      let f := F delta n d omega N
      let increase := reciprocalTotientDensity U (P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N cap w z tau)-
        reciprocalTotientDensity U (P4AUpperTaggedParityCompiler.raw f N cap w z)
      (actualSmallEulerProduct N cap w/actualSmallEulerProduct N cap z)*increase ≤
        ((count delta n d:ℝ)*300*tau+(count delta n d:ℝ)*20*K/Real.log (N:ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,h⟩ := P4AFull87RoughEulerRatio.of_wallRate (rate delta hd n d he (fun _ _ => []))
  refine ⟨K,E,hK,hE,?_⟩
  intro N cap hN hEven omega v tau hw hv hv1 ht h3 hlog
  have H := h N cap hN hEven omega v tau hw hv hv1 ht h3 hlog
  dsimp only at H ⊢
  rw [P4AUpperTaggedParityCompiler.rough_density_increase_eq_changedMass] at H ⊢
  rw [(rough_equal delta n d (by omega : 1≤N) cap hw.le ((N:ℝ)^v) tau 1 (fun _ => [])).2.1]
  exact H

theorem paid (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    (nu r u_c epsilonMax : ℝ) (hnu : 0<nu) (hr : 0<r) (hv : nu*r≤1) (hu : 0<u_c) (hm : 0<epsilonMax) :
    ∃ eps : ℝ, 0<eps ∧ eps<1/8 ∧ eps<epsilonMax ∧ eps^2<r ∧ nu*eps<1/1000 ∧
    ∃ tau0 : ℝ, 0<tau0 ∧ ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
    ∀ cap : ℕ, (N:ℝ)^(nu*r)≤(cap:ℝ) → ∀ tau : ℝ, 0<tau → tau≤tau0 →
      let omega := nu*eps^2
      let keep := F delta n d omega N
      let w := (N:ℝ)^omega
      let z := (N:ℝ)^(nu*r)
      let L := (N:ℝ)^(nu*eps)
      let rho := P4AUpperTaggedBetaAttachment.rho keep (fun _ => []) N cap w z tau L
      let spend := P4AFiniteCapTaggedConstructor.compilerExpense keep (fun _ => []) N cap w z tau L
      spend<u_c*(singularSeries N/Real.log (N:ℝ)) ∧
      ((N:ℝ)/Real.log (N:ℝ))*spend<u_c*singularNormalization N ∧
      physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z) rho<
        p4aReserveRawDensity keep N cap 0 z-p4aActualPresieveCorrection keep N cap w z+
        u_c*(singularSeries N/Real.log (N:ℝ)) := by
  obtain ⟨eps,hp,h8,hmax,hsq,hell,t0,ht0,N0,hN0,h⟩ := of_wallRate (rate delta hd n d he (fun _ _ => []))
    nu r u_c epsilonMax hnu hr hv hu hm
  refine ⟨eps,hp,h8,hmax,hsq,hell,t0,ht0,N0,hN0,?_⟩
  intro N hN hEven cap hcap tau ht hsmall
  let omega := nu*eps^2
  have hw : 0<omega := mul_pos hnu (sq_pos_of_pos hp)
  have hn : 1≤N := by omega
  have hz := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ)≤N)
    (mul_le_mul_of_nonneg_left hsq.le hnu.le)
  obtain ⟨hrho,_,hsp,_⟩ := rough_equal delta n d hn cap hw.le ((N:ℝ)^(nu*r)) tau
    ((N:ℝ)^(nu*eps)) (fun _ => [])
  dsimp only
  rw [hsp,hrho,projected_cut delta n d hn cap hw.le ((N:ℝ)^(nu*r)) hz]
  exact h N hN hEven cap hcap tau ht hsmall

end
end ImbalancedChen.P4AOrderedThirdRectanglePayment
