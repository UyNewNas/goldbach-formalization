import ImbalancedChen.P4AFiniteCapTaggedConstructor
import ImbalancedChen.P4AUpperTaggedContinuationAccounting

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.

Complete compiler payment for the explicit finite-cap constructor. The
whole changed-set cover is proved in the preceding module; no caller
supplies a compiler norm, a wall-cover premise or a density endpoint.
One beta precision is chosen first, then J0 and a positive fine width,
then a common N threshold. Both beta signs use the same physical rho.

This pays only u_c. It does not spend any part of u_d, identify the
constructor with the original full87 history, or prove the manuscript's
stronger displayed C_policy*tau*omega^(-5) asymptotic rate.
-/

namespace ImbalancedChen.P4AFiniteCapTaggedConstructor

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler
open P4AUpperTaggedFrozenAdmissionCatalogue
open P4AHeldTaggedFiniteAdmissionPayment
open P4AHeldTaggedCompilerSupport

/-- All literal coefficient changes, uniformly in the later selector,
historical decisions and fine width. The finite alphabet is fixed first. -/
theorem exists_total_changedMass_lt {n h : ℕ} (values : Fin n → ℝ)
    (omega v : ℝ) (homega : 0 < omega) (hov : omega < v)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      ∀ (select : List ℕ → Fin n) (gate : List ℕ → Bool)
        (history : Fin h → List ℕ → Bool) (tau : ℝ),
      0 < tau → tau ≤ tau0 →
      changedMass (keep values select gate N) (tag (J0 omega) select gate history)
        N cap ((N : ℝ) ^ omega) ((N : ℝ) ^ v) tau < eta := by
  have hJ : 0 < J0 omega := by unfold J0; omega
  obtain ⟨tau0, htau0, N0, hN0, hpay⟩ := exists_admissionUnionMass_lt
    (J0 omega) hJ (fun _ => capAlphabet values) omega v homega hov eta heta
  refine ⟨tau0, htau0, N0, hN0, ?_⟩
  intro N hN hEven cap select gate history tau htau htau0'
  exact (changedMass_le_admissionUnion values select gate history omega v homega
    N cap (hN0.trans hN) tau).trans_lt
      (hpay N hN hEven cap (keep values select gate N)
        (tag (J0 omega) select gate history) tau htau htau0')

/-- The complete physical difference is paid on the same global rho,
including every negative -1 -> 0 change. No signed lower-beta term is
silently changed to its negative. -/
theorem exists_total_physical_compiler_payment {n h : ℕ} (values : Fin n → ℝ)
    (nu epsilon v : ℝ) (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1 / 8)
    (hv : nu * epsilon ^ 2 < v) (eta : ℝ) (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
      ∀ (select : List ℕ → Fin n) (gate : List ℕ → Bool)
        (history : Fin h → List ℕ → Bool) (tau : ℝ),
      0 < tau → tau ≤ tau0 →
      let omega := nu * epsilon ^ 2
      let w := (N : ℝ) ^ omega
      let z := (N : ℝ) ^ v
      let level := (N : ℝ) ^ (nu * epsilon)
      let retained := keep values select gate N
      let tags := tag (J0 omega) select gate history
      |physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
          (P4AUpperTaggedBetaAttachment.rho retained tags N cap w z tau level) -
        p4aReservePhysicalDensity retained N cap w z level| <
        eta * (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := P4AUpperTaggedBetaAttachment.exists_density_difference_le_changedMass
  obtain ⟨Nb, hNb, hbeta⟩ := hsupply nu hnu epsilon he he8
  have homega : 0 < nu * epsilon ^ 2 := mul_pos hnu (sq_pos_of_pos he)
  let M : ℝ := B / (nu * epsilon ^ 2)
  have hM : 0 < M := div_pos hB homega
  obtain ⟨tau0, htau0, Nm, hNm, hmass⟩ := exists_total_changedMass_lt
    (h := h) values (nu * epsilon ^ 2) v homega hv (eta / M) (div_pos heta hM)
  refine ⟨tau0, htau0, max Nb Nm, hNb.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap select gate history tau htau htau0'
  have hm := hmass N ((le_max_right _ _).trans hN) hEven cap
    select gate history tau htau htau0'
  have hb := hbeta N ((le_max_left _ _).trans hN) hEven cap hcap
    (keep values select gate N) (tag (J0 (nu * epsilon ^ 2)) select gate history)
    ((N : ℝ) ^ v) tau
  have hpay : M * changedMass (keep values select gate N)
      (tag (J0 (nu * epsilon ^ 2)) select gate history)
      N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ v) tau < eta := by
    have hp := (lt_div_iff₀ hM).mp hm
    simpa only [mul_comm] using hp
  have hscale := densityScale_pos (hNb.trans ((le_max_left _ _).trans hN))
  dsimp only at hb ⊢
  exact hb.trans_lt (mul_lt_mul_of_pos_right hpay hscale)

/-- Beta attachment defect plus the entire absolute box change. This is
an actual nonnegative expenditure once the beta supplier applies, rather
than an error defined by subtraction from a desired endpoint. -/
def compilerExpense (retained : List ℕ → Bool) (tags : ℕ → List Bool)
    (N cap : ℕ) (w z tau level : ℝ) : ℝ :=
  (p4aReservePhysicalDensity retained N cap w z level -
    actualSmallEulerProduct N cap w * p4aReserveRawDensity retained N cap w z) +
  |physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
      (P4AUpperTaggedBetaAttachment.rho retained tags N cap w z tau level) -
    p4aReservePhysicalDensity retained N cap w z level|

/-- One pre-N schedule pays the entire independent compiler reserve for
this concrete constructor. The original continuation correction remains
with its exact favorable sign; old/new differences must still retain the
difference of their two corrections. No density reserve is used here. -/
theorem exists_total_compiler_reserve {n h : ℕ} (values : Fin n → ℝ)
    (nu r u_c epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (hu : 0 < u_c) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 < r ∧ nu * epsilon < 1 / 1000 ∧
      ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
        (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
        ∀ (select : List ℕ → Fin n) (gate : List ℕ → Bool)
          (history : Fin h → List ℕ → Bool) (tau : ℝ),
        0 < tau → tau ≤ tau0 →
        let omega := nu * epsilon ^ 2
        let w := (N : ℝ) ^ omega
        let z := (N : ℝ) ^ (nu * r)
        let level := (N : ℝ) ^ (nu * epsilon)
        let retained := keep values select gate N
        let tags := tag (J0 omega) select gate history
        compilerExpense retained tags N cap w z tau level <
            u_c * (singularSeries N / Real.log (N : ℝ)) ∧
        physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
            (P4AUpperTaggedBetaAttachment.rho retained tags N cap w z tau level) <
          p4aReserveRawDensity retained N cap 0 z +
            u_c * (singularSeries N / Real.log (N : ℝ)) -
            p4aActualPresieveCorrection retained N cap w z := by
  let emax : ℝ := min epsilonMax (min 1 (min r (1 / (2000 * nu))))
  have hem : 0 < emax := lt_min hepsilonMax
    (lt_min zero_lt_one (lt_min hr (by positivity)))
  obtain ⟨epsilon, he, he8, hem', _her, Nb, hNb, hbeta⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu r (u_c / 3) emax hnu hr (by positivity) hem
  have hemax : epsilon < epsilonMax := hem'.trans_le (min_le_left _ _)
  have helimits : epsilon < min 1 (min r (1 / (2000 * nu))) :=
    hem'.trans_le (min_le_right _ _)
  have he1 : epsilon < 1 := helimits.trans_le (min_le_left _ _)
  have her : epsilon < r :=
    helimits.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hesmall : epsilon < 1 / (2000 * nu) :=
    helimits.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have he2r : epsilon ^ 2 < r := by nlinarith
  have hell : nu * epsilon < 1 / 1000 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2000 * nu)).mp hesmall
    nlinarith
  have hov : nu * epsilon ^ 2 < nu * r := mul_lt_mul_of_pos_left he2r hnu
  obtain ⟨tau0, htau0, Nm, hNm, hmass⟩ := exists_total_physical_compiler_payment
    (h := h) values nu epsilon (nu * r) hnu he he8 hov (u_c / 3) (by positivity)
  refine ⟨epsilon, he, he8, hemax, he2r, hell, tau0, htau0,
    max Nb Nm, hNb.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap select gate history tau htau htau0'
  let retained := keep values select gate N
  let tags := tag (J0 (nu * epsilon ^ 2)) select gate history
  have hN2 : 2 ≤ N := hNb.trans ((le_max_left _ _).trans hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwz : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * r) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hov.le
  have hb := (hbeta N ((le_max_left _ _).trans hN) hEven cap hcap retained).2
  have hm := hmass N ((le_max_right _ _).trans hN) hEven cap
    (hwz.trans hcap) select gate history tau htau htau0'
  have hp := p4a_fullRaw_eq_euler_presieved_add_correction retained N cap
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) hwz
  have hscale := densityScale_pos hN2
  have hmargin : (u_c / 3 + u_c / 3) *
      (singularSeries N / Real.log (N : ℝ)) <
      u_c * (singularSeries N / Real.log (N : ℝ)) := by
    exact mul_lt_mul_of_pos_right (by linarith) hscale
  dsimp only at hb hm ⊢
  change p4aReservePhysicalDensity retained N cap _ _ _ -
      actualSmallEulerProduct N cap _ * p4aReserveRawDensity retained N cap _ _ ≤
      (u_c / 3) * singularSeries N / Real.log (N : ℝ) at hb
  change |physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap _ _)
      (P4AUpperTaggedBetaAttachment.rho retained tags N cap _ _ tau _) -
    p4aReservePhysicalDensity retained N cap _ _ _| < _ at hm
  have hexp : compilerExpense retained tags N cap
      ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) tau
      ((N : ℝ) ^ (nu * epsilon)) <
      u_c * (singularSeries N / Real.log (N : ℝ)) := by
    unfold compilerExpense
    rw [mul_div_assoc] at hb
    nlinarith
  refine ⟨hexp, ?_⟩
  have hupper := (le_abs_self
    (physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap
      ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)))
      (P4AUpperTaggedBetaAttachment.rho retained tags N cap
        ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) tau
        ((N : ℝ) ^ (nu * epsilon))) -
      p4aReservePhysicalDensity retained N cap ((N : ℝ) ^ (nu * epsilon ^ 2))
        ((N : ℝ) ^ (nu * r)) ((N : ℝ) ^ (nu * epsilon))))
  unfold compilerExpense at hexp
  linarith only [hexp, hp, hupper]

end
end ImbalancedChen.P4AFiniteCapTaggedConstructor
