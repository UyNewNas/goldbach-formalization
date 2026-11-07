import ImbalancedChen.P4ACompactPhysicalDensityEndpoint

/-!
The actual compact-policy endpoint permits any positive upper bound on
the small-attachment precision. In particular epsilon<min(1,2e) supplies
epsilon<=2e for the independent physical support-exponent proof.

Draft import mapping: sibling P4ACompactPhysicalDensityEndpoint.lean.txt is
to be staged as ImbalancedChen/P4ACompactPhysicalDensityEndpoint.lean,
with its own sibling P4ASameRhoCompact dependency staged as documented.
No installed source is edited by this draft.
-/

namespace ImbalancedChen.P4ASameRhoCompact

noncomputable section
open Filter Topology

/-- The precision ceiling is supplied before one common target threshold.
Both analytic hypotheses are discharged by the actual compact full limit. -/
theorem exists_attached_physical_density_endpoint_with_precision_max
    {e h : ℝ} {m : ℕ}
    (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (eta epsilonMax : ℝ) (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 ≤ thirdPrefixRho ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        physicalDensitySum
            (attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N)
            (attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N) ≤
          (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m + eta) *
            (singularSeries N / Real.log (N : ℝ)) := by
  have hsupply := exists_actualSmallRoughRho_density_le_of_full_policy_limits
    1 thirdPrefixRho epsilonMax
    (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m)
    (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m + eta)
    (by norm_num) thirdPrefixRho_pos_lt_one.1 hepsilonMax
    (fun _ N => retain e h m N) (fun N => N)
    (fun _ => baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m)
    eventually_compact_cap_covers
    (fun _ _ _ => by
      simpa only [one_mul, fullDensity] using tendsto_full_density hh he0 he hmesh)
    (fun _ _ _ => le_rfl)
    (by linarith)
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonR,
    N₀, hN₀, hbound⟩ := hsupply
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonR, N₀, hN₀, ?_⟩
  intro N hN hEven
  simpa only [attachedUpperModuli, attachedUpperCoefficient] using hbound N hN hEven

/-- The actual endpoint now supplies the support exponent's required
epsilon<=2e using a positive precision ceiling; it is not a new premise. -/
theorem exists_attached_physical_density_endpoint_support_precision
    {e h : ℝ} {m : ℕ}
    (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
      epsilon ≤ 2 * e ∧ epsilon ^ 2 ≤ thirdPrefixRho ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        physicalDensitySum
            (attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N)
            (attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N) ≤
          (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m + eta) *
            (singularSeries N / Real.log (N : ℝ)) := by
  have hmax : (0 : ℝ) < min 1 (2 * e) := lt_min (by norm_num) (by linarith)
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax, hepsilonR, N₀, hN₀, hbound⟩ :=
    exists_attached_physical_density_endpoint_with_precision_max hh he0 he hmesh
      eta (min 1 (2 * e)) heta hmax
  exact ⟨epsilon, hepsilon, hepsilon8,
    hepsilonMax.trans_le (min_le_left _ _),
    hepsilonMax.le.trans (min_le_right _ _), hepsilonR, N₀, hN₀, hbound⟩

end
end ImbalancedChen.P4ASameRhoCompact
