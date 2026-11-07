import ImbalancedChen.P4ACompactPhysicalDensityEndpoint
import ImbalancedChen.P4ACoveringCapInvariance

/-!
# P4A: the fixed compact endpoint at every covering cap

Draft dependencies must be staged under the displayed ImbalancedChen import
names. In particular P4ACompactPhysicalDensityEndpoint.lean.txt depends on
P4ASameRhoCompact.lean.txt. Nothing is installed by this source-only file.

The compact endpoint already derives its full signed limit from actual
suppliers. Here epsilon is selected before the arbitrary cap sequence.
Exact covering-cap invariance transfers that endpoint, and the actual
geometric suppliers give the remaining finite physical-weight properties.
There is no hIntegral, sharp K, RealB, or signed-distribution premise.
-/

namespace ImbalancedChen.P4ACompactEndpointAnyCoveringCap

noncomputable section

open Filter Topology
open P4ASameRhoCompact

/-- One attachment precision works for every eventually covering cap
sequence. The target threshold is then shared by the density endpoint,
one-bound, squarefree/coprime carrier and literal sieve majorant.

The compact e,h,m are fixed before eta; epsilon is fixed before cap.
The endpoint constant remains the actual compact baseline plus its proved
cell functional and eta. No full22/currentK identification is asserted. -/
theorem exists_compact_endpoint_for_all_covering_caps {e h : ℝ} {m : ℕ}
    (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
      epsilon ^ 2 ≤ thirdPrefixRho ∧
      ∀ cap : ℕ → ℕ,
        (∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
          (N : ℝ) ^ thirdPrefixRho ≤ (cap N : ℝ)) →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          let Q := attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) cap N
          let rho := attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) cap N
          physicalDensitySum Q rho ≤
              (baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m + eta) *
                (singularSeries N / Real.log (N : ℝ)) ∧
            (∀ q : ℕ, |rho q| ≤ 1) ∧
            (∀ q ∈ Q, Squarefree q ∧ q.Coprime N) ∧
            (∀ n : ℕ,
              (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ thirdPrefixRho)))
                then (1 : ℝ) else 0) ≤ physicalDivisorSum Q rho n) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilon1, hepsilonR,
      Nendpoint, hNendpoint, hEndpoint⟩ :=
    exists_attached_physical_density_endpoint hh he0 he hmesh eta heta
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilon1, hepsilonR, ?_⟩
  intro cap hcap
  rw [Filter.eventually_inf_principal] at hcap
  obtain ⟨Ncap, hNcap⟩ := eventually_atTop.mp hcap
  refine ⟨max Nendpoint Ncap, hNendpoint.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNe : Nendpoint ≤ N := (le_max_left _ _).trans hN
  have hNc : Ncap ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNendpoint.trans hNe
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hcapN : (N : ℝ) ^ thirdPrefixRho ≤ (cap N : ℝ) :=
    hNcap N hNc ⟨hNpos, hEven⟩
  have hcapN' : (N : ℝ) ^ ((1 : ℝ) * thirdPrefixRho) ≤ (cap N : ℝ) := by
    simpa only [one_mul] using hcapN
  have hdiag : (N : ℝ) ^ ((1 : ℝ) * thirdPrefixRho) ≤ (N : ℝ) := by
    simpa only [one_mul, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNreal.le thirdPrefixRho_pos_lt_one.2.le
  have hwz : (N : ℝ) ^ ((1 : ℝ) * epsilon ^ 2) ≤
      (N : ℝ) ^ ((1 : ℝ) * thirdPrefixRho) := by
    apply Real.rpow_le_rpow_of_exponent_le hNreal.le
    simpa only [one_mul] using hepsilonR
  have hsame := P4ACoveringCapInvariance.physicalDensity_eq_of_cover
    (retain e h m N) ((N : ℝ) ^ ((1 : ℝ) * epsilon)) hwz hcapN' hdiag
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · change physicalDensitySum
      (actualSmallRoughModuli (retain e h m N) N (cap N)
        ((N : ℝ) ^ ((1 : ℝ) * epsilon ^ 2))
        ((N : ℝ) ^ ((1 : ℝ) * thirdPrefixRho)))
      (actualSmallRoughRho (retain e h m N) N (cap N)
        ((N : ℝ) ^ ((1 : ℝ) * epsilon ^ 2))
        ((N : ℝ) ^ ((1 : ℝ) * thirdPrefixRho))
        ((N : ℝ) ^ ((1 : ℝ) * epsilon))) ≤ _
    rw [hsame]
    exact hEndpoint N hNe hEven
  · intro q
    exact actualSmallRoughRho_abs_le_one (retain e h m N) N (cap N) _ _ _ q
  · intro q hq
    exact ⟨actualSmallRoughModuli_squarefree (retain e h m N) N (cap N) _ _ hq,
      actualSmallRoughModuli_coprime_target (retain e h m N) N (cap N) _ _ hq⟩
  · intro n
    simpa only [one_mul] using attachedUpperCoefficient_majorant
      (nu := (1 : ℝ)) (r := thirdPrefixRho)
      (by norm_num) hepsilon hepsilon1.le hepsilonR (retain e h m) cap hN2 hcapN' n

end
end ImbalancedChen.P4ACompactEndpointAnyCoveringCap
