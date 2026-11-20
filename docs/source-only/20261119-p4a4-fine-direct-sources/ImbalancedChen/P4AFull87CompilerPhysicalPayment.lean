import ImbalancedChen.P4AFull87CompilerChangedPartition
import ImbalancedChen.P4AFiniteCapTaggedPayment

namespace ImbalancedChen.P4AFull87CompilerPhysicalPayment
noncomputable section
open scoped Classical BigOperators
open P4AFull87CompilerChangedPartition P4AHeldTaggedFiniteAdmissionPayment
open P4AUpperTaggedParityCompiler

/-- The physical expense of the actual licensed strategy at the manuscript
count scale. The two paid portions share one strict allowance. The remaining
term is an explicitly localized nonnegative rough-modulus sum. -/
theorem exists_actual_payment_with_inherited_remainder :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : Parameters), 0 < P.delta →
      ∀ nu r u_c epsilonMax : ℝ, 0 < nu → 0 < r → 0 < u_c → 0 < epsilonMax →
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
        epsilon^2 < r ∧ nu*epsilon < 1/1000 ∧
      ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ)^(nu*r) ≤ (cap : ℝ) →
      ∀ (history : ℕ → List Bool) (tau : ℝ), 0 < tau → tau ≤ tau0 →
        let omega := nu*epsilon^2
        let w := (N : ℝ)^omega
        let z := (N : ℝ)^(nu*r)
        let L := (N : ℝ)^(nu*epsilon)
        let spend := P4AFiniteCapTaggedConstructor.compilerExpense
          (P.keep N) (P.tags N history) N cap w z tau L
        let remaining := B/omega * pendingMass P N cap history omega (nu*r) tau
        spend < (u_c/2 + remaining) * (singularSeries N / Real.log (N : ℝ)) ∧
        ((N : ℝ) / Real.log (N : ℝ)) * spend <
          (u_c/2 + remaining) * singularNormalization N ∧
        physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
          (P4AUpperTaggedBetaAttachment.rho (P.keep N) (P.tags N history) N cap w z tau L) <
          p4aReserveRawDensity (P.keep N) N cap 0 z -
            p4aActualPresieveCorrection (P.keep N) N cap w z +
          (u_c/2 + remaining) * (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B,hB,hbox⟩ := P4AUpperTaggedBetaAttachment.exists_density_difference_le_changedMass
  refine ⟨B,hB,?_⟩
  intro P hd nu r u_c epsilonMax hnu hr hu hmax
  let em := min epsilonMax (min 1 (min r (1/(2000*nu))))
  have hem : 0 < em := lt_min hmax (lt_min zero_lt_one (lt_min hr (by positivity)))
  obtain ⟨eps,he,h8,hemax,_,Nb,hNb,hbeta⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu r (u_c/4) em hnu hr (by positivity) hem
  have hrest := hemax.trans_le (min_le_right epsilonMax _)
  have h1 : eps < 1 := hrest.trans_le (min_le_left _ _)
  have hr' : eps < r := hrest.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlev := hrest.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlev' := (lt_div_iff₀ (by positivity : 0 < 2000*nu)).mp hlev
  have hsq : eps^2 < r := by nlinarith
  let omega := nu*eps^2
  let v := nu*r
  let slope := B/omega
  have hw : 0 < omega := mul_pos hnu (sq_pos_of_pos he)
  have hv : omega < v := mul_lt_mul_of_pos_left hsq hnu
  have hslope : 0 < slope := div_pos hB hw
  obtain ⟨Nf,hNf,hphysical⟩ := hbox nu hnu eps he h8
  have hJ : 0 < rankBound P omega := Nat.succ_pos _
  obtain ⟨t,ht,Nm,hNm,hm⟩ := exists_admissionUnionMass_lt (rankBound P omega) hJ
    (fun _ => P.caps) omega v hw hv ((u_c/4)/slope) (by positivity)
  refine ⟨eps,he,h8,hemax.trans_le (min_le_left _ _),hsq,by nlinarith,t,ht,
    max Nb (max Nf Nm),hNb.trans (le_max_left _ _),?_⟩
  intro N hN hEven cap hcap history tau htau hsmall
  let w := (N : ℝ)^omega
  let z := (N : ℝ)^v
  let L := (N : ℝ)^(nu*eps)
  let keep := P.keep N
  let tags := P.tags N history
  let scale := singularSeries N / Real.log (N : ℝ)
  let A := P4AFiniteCapTaggedConstructor.compilerExpense keep tags N cap w z tau L
  let R := pendingMass P N cap history omega v tau
  have hbN := (le_max_left _ _).trans hN
  have hN2 := hNb.trans hbN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hwz : w ≤ z := Real.rpow_le_rpow_of_exponent_le hn.le hv.le
  have hfN := (le_max_left Nf Nm).trans ((le_max_right _ _).trans hN)
  have hmN := (le_max_right Nf Nm).trans ((le_max_right _ _).trans hN)
  have hS : 0 < scale := densityScale_pos hN2
  have hbeta' := (hbeta N hbN hEven cap hcap keep).2
  change p4aReservePhysicalDensity keep N cap w z L -
    actualSmallEulerProduct N cap w * p4aReserveRawDensity keep N cap w z ≤
    (u_c/4) * singularSeries N / Real.log (N : ℝ) at hbeta'
  rw [mul_div_assoc] at hbeta'
  have hcat := (lt_div_iff₀ hslope).mp (hm N hmN hEven cap keep tags tau htau hsmall)
  have hchanged := changedMass_le_catalogue_add_pending P hd N cap hN2 history omega v tau hw
  have hbound : slope * changedMass keep tags N cap w z tau < u_c/4 + slope*R := by
    have hh := mul_le_mul_of_nonneg_left hchanged hslope.le
    rw [mul_add] at hh
    exact hh.trans_lt (add_lt_add_right (by simpa only [mul_comm] using hcat) _)
  have hphys := hphysical N hfN hEven cap (hwz.trans hcap) keep tags z tau
  have hphysical' : |physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
       (P4AUpperTaggedBetaAttachment.rho keep tags N cap w z tau L) -
       p4aReservePhysicalDensity keep N cap w z L| < (u_c/4+slope*R)*scale :=
    hphys.trans_lt (mul_lt_mul_of_pos_right hbound hS)
  have hspend : A < (u_c/2+slope*R)*scale := by
    change (p4aReservePhysicalDensity keep N cap w z L -
      actualSmallEulerProduct N cap w * p4aReserveRawDensity keep N cap w z) + _ < _
    change _ ≤ (u_c/4)*scale at hbeta'
    linarith only [add_lt_add_of_le_of_lt hbeta' hphysical']
  refine ⟨hspend,?_,?_⟩
  · have hs : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (zero_lt_one.trans hn) (Real.log_pos hn)
    calc
      _ < ((N : ℝ) / Real.log (N : ℝ)) * ((u_c/2+slope*R)*scale) :=
        mul_lt_mul_of_pos_left hspend hs
      _ = (u_c/2+slope*R) * singularNormalization N := by
        rw [← sourceMassScale_mul_densityScale N]
        dsimp only [scale]
        ring
  · have hproj := p4a_fullRaw_eq_euler_presieved_add_correction keep N cap w z hwz
    have hone := le_abs_self
      (physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
        (P4AUpperTaggedBetaAttachment.rho keep tags N cap w z tau L) -
        p4aReservePhysicalDensity keep N cap w z L)
    dsimp only [A,P4AFiniteCapTaggedConstructor.compilerExpense] at hspend
    change physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
      (P4AUpperTaggedBetaAttachment.rho keep tags N cap w z tau L) <
      p4aReserveRawDensity keep N cap 0 z - p4aActualPresieveCorrection keep N cap w z +
        (u_c/2+slope*R)*scale
    linarith only [hone,hspend,hproj]

end
end ImbalancedChen.P4AFull87CompilerPhysicalPayment
