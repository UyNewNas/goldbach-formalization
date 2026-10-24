import ImbalancedChen.P4ASameRhoCompact
import ImbalancedChen.ActualUpperDensityAssembly

/-!
Physical endpoint for the fixed actual compact third policy, with nu=1,
sieveR=thirdPrefixRho and cap=N. The full signed-density limit is supplied
by P4ASameRhoCompact.tendsto_full_density. The attachment precision is
chosen after eta, independently of the fixed compact e,h,m parameters.

Draft import mapping: P4ASameRhoCompact.lean.txt must be staged as
ImbalancedChen/P4ASameRhoCompact.lean before this module is elaborated.
No source is installed by this draft. No currentK/full22 estimate is asserted.
-/

namespace ImbalancedChen.P4ASameRhoCompact

noncomputable section
open Filter Topology

theorem thirdPrefixRho_pos_lt_one : 0 < thirdPrefixRho ∧ thirdPrefixRho < 1 := by
  norm_num [thirdPrefixRho]

theorem eventually_compact_cap_covers :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ ((1 : ℝ) * thirdPrefixRho) ≤ (N : ℝ) := by
  filter_upwards [(eventually_ge_atTop (1 : ℕ)).filter_mono inf_le_left] with N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : (1 : ℝ) * thirdPrefixRho ≤ 1 := by
    simpa only [one_mul] using thirdPrefixRho_pos_lt_one.2.le
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr hr

/-- Every positive endpoint reserve is achieved by one positive attachment
precision and one common even-target threshold for the same literal rho.
The compact policy parameters are already fixed before eta is supplied. -/
theorem exists_attached_physical_density_endpoint {e h : ℝ} {m : ℕ}
    (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
      epsilon ^ 2 ≤ thirdPrefixRho ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        physicalDensitySum
            (attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N)
            (attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N) ≤
          (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m + eta) *
            (singularSeries N / Real.log (N : ℝ)) := by
  have hsupply := exists_actualSmallRoughRho_density_le_of_full_policy_limits
    1 thirdPrefixRho 1
    (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m)
    (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m + eta)
    (by norm_num) thirdPrefixRho_pos_lt_one.1 (by norm_num)
    (fun _ N => retain e h m N) (fun N => N)
    (fun _ => baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m)
    eventually_compact_cap_covers
    (fun _ _ _ => by
      simpa only [one_mul, fullDensity] using tendsto_full_density hh he0 he hmesh)
    (fun _ _ _ => le_rfl)
    (by linarith)
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilon1, hepsilonR,
    N₀, hN₀, hbound⟩ := hsupply
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilon1, hepsilonR, N₀, hN₀, ?_⟩
  intro N hN hEven
  simpa only [attachedUpperModuli, attachedUpperCoefficient] using hbound N hN hEven

end
end ImbalancedChen.P4ASameRhoCompact
