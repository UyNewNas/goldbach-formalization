import ImbalancedChen.P4AUpperTaggedContinuationAccounting
import ImbalancedChen.SmallRosserErrorLimit

/-! The two physical attachments can have different coefficients on a mixed
cell. Their exact density difference nevertheless has a sign once both
actual small Rosser densities are nonnegative. The beta ceiling needed for
this comparison is fixed before the policy, fine grid and target. -/
namespace ImbalancedChen.P4BOriginalRosserDensityOrder

noncomputable section
open Filter Topology
open scoped BigOperators
open P4AUpperTaggedContinuationAccounting

/-- Finite comparison on the literal native carriers, for any original
retention rule and tag. The size of the changed set is unrestricted. -/
theorem raw_le_compiled (retain : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ)
    (hlo : 0 ≤ actualSmallRosserMinusDensity N cap w L)
    (hhi : 0 ≤ actualSmallRosserPlusDensity N cap w L) :
    p4aReservePhysicalDensity retain N cap w z L ≤
      physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
        (P4AUpperTaggedBetaAttachment.rho retain tag N cap w z tau L) := by
  have hp : 0 ≤ positiveChangedMass retain tag N cap w z tau := by
    unfold positiveChangedMass
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hm : 0 ≤ negativeChangedMass retain tag N cap w z tau := by
    unfold negativeChangedMass
    exact Finset.sum_nonneg fun _ _ => by positivity
  apply sub_nonneg.mp
  rw [physical_compiler_change_eq_signed_changed_masses]
  exact add_nonneg (mul_nonneg hhi hp) (mul_nonneg hlo hm)

/-- One ceiling works for every smaller beta, including an unknown
subsequent Fine witness. For each fixed nu and beta the target threshold
precedes both carriers, both policies, the fine width and the rough cutoff. -/
theorem exists_eventual_raw_le_compiled :
    ∃ betaCeiling : ℝ, 0 < betaCeiling ∧
    ∀ nu beta : ℝ, 0 < nu → 0 < beta → beta < 1 / 8 → beta < betaCeiling →
      ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (cap : ℕ) (retain : List ℕ → Bool) (tag : ℕ → List Bool) (z tau : ℝ),
        let w := (N : ℝ) ^ (nu * beta ^ 2)
        let L := (N : ℝ) ^ (nu * beta)
        p4aReservePhysicalDensity retain N cap w z L ≤
          physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
            (P4AUpperTaggedBetaAttachment.rho retain tag N cap w z tau L) := by
  obtain ⟨C, K, hC, _, hRosser⟩ := exists_actualSmallRosser_density_sandwich
  refine ⟨1 / (C + 1), one_div_pos.mpr (by linarith), ?_⟩
  intro nu beta hnu hbeta hb8 hbC
  have hbC' : beta * (C + 1) < 1 :=
    (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hbC
  have hratio : C + 1 < 1 / beta :=
    (lt_div_iff₀ hbeta).mpr (by simpa only [mul_comm beta (C + 1)] using hbC')
  have hExp : C < Real.exp (1 / beta) := by
    linarith only [hratio, Real.add_one_le_exp (1 / beta)]
  have hfloor : C * Real.exp (-(1 / beta)) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr hExp
  obtain ⟨D0, _, hSandwich⟩ := hRosser beta hbeta hb8
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  have hE := (tendsto_order.1
    ((tendsto_actualSmallRosserDensityError C K beta hbeta).comp hscale)).2 1 hfloor
  filter_upwards [hscale.eventually (eventually_ge_atTop D0), hE] with N hN hError
  intro hEven cap retain tag z tau
  obtain ⟨hLower, _, hUpper, _, _⟩ := hSandwich _ hN N cap hEven
  dsimp only at hLower hUpper ⊢
  change actualSmallRosserDensityError C K ((N : ℝ) ^ nu) beta < 1 at hError
  have hEuler := (actualSmallEulerProduct_pos N cap (((N : ℝ) ^ nu) ^ (beta ^ 2)) hEven).le
  have hLo := (mul_nonneg hEuler (sub_nonneg.mpr hError.le)).trans hLower
  have hHi := hEuler.trans hUpper
  simp only [← Real.rpow_mul (Nat.cast_nonneg N)] at hLo hHi
  exact raw_le_compiled retain tag N cap _ z tau _ hLo hHi

end
end ImbalancedChen.P4BOriginalRosserDensityOrder
