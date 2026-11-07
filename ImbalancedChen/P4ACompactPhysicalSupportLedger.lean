import ImbalancedChen.P4ACompactPhysicalIntegralLedger
import ImbalancedChen.P4ACompactCoefficientSupportExponent
import ImbalancedChen.P4ACoveringCapInvariance

/-!
# P4A: one concrete compact rho supplies the density/support ledger

Draft imports must be staged under the displayed ImbalancedChen names.
The physical integral ledger supplies actual h,e,m,epsilon with epsilon<=2e.
The support exponent is proved from that same compact policy. Exact cap
invariance then permits any eventually covering enumeration cap, selected
after all four parameters. All geometric inputs concern the same rho.

The original integral ledger remains unevaluated. This is not a currentK,
full22, RealB, or signed-distribution theorem.

SOURCE ONLY; no compilation was performed.
-/

namespace ImbalancedChen.P4ACompactPhysicalSupportLedger

noncomputable section

open Filter Topology
open P4ASameRhoCompact OriginalThirdFiniteReserveSourceOnly

/-- The only input is eta>0. Every policy/precision parameter and every
finite physical-weight property is supplied. One epsilon precedes every
cap sequence; each eventually covering cap gets a common target threshold.
The active support bound is strict at the original theta exponent. -/
theorem exists_compact_physical_support_ledger (eta : ℝ) (heta : 0 < eta) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
        epsilon ≤ 2 * e ∧ epsilon ^ 2 ≤ thirdPrefixRho ∧
        ∀ cap : ℕ → ℕ,
          (∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
            (N : ℝ) ^ thirdPrefixRho ≤ (cap N : ℝ)) →
          ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
            let Q := attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) cap N
            let rho := attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) cap N
            physicalDensitySum Q rho ≤
                (originalOrdinaryRoot + originalCompactThirdCorrection +
                  (319683857488126290909150567 / 2^111 : ℝ) +
                  originalDensityReserve / 4 + eta) *
                    (singularSeries N / Real.log (N : ℝ)) ∧
              (∀ q : ℕ, rho q ≠ 0 → (q : ℝ) < (N : ℝ) ^ thirdPrefixTheta) ∧
              (∀ q : ℕ, |rho q| ≤ 1) ∧
              (∀ q ∈ Q, Squarefree q ∧ q.Coprime N) ∧
              (∀ n : ℕ,
                (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ thirdPrefixRho)))
                  then (1 : ℝ) else 0) ≤ physicalDivisorSum Q rho n) := by
  obtain ⟨h, hh, e, he0, he, m, hmesh, epsilon, hepsilon, hepsilon8,
      hepsilon1, hepsilonSupport, hepsilonR, Nendpoint, hNendpoint, hEndpoint⟩ :=
    P4ACompactPhysicalIntegralLedger.exists_actual_physical_density_le_original_integral_ledger
      eta heta
  refine ⟨h, hh, e, he0, he, m, hmesh, epsilon, hepsilon, hepsilon8,
    hepsilon1, hepsilonSupport, hepsilonR, ?_⟩
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
  · intro q hq
    exact P4ACompactCoefficientSupportExponent.attachedUpperCoefficient_ne_zero_lt_theta
      e h epsilon m N cap hN2 he hepsilonSupport hq
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
end ImbalancedChen.P4ACompactPhysicalSupportLedger
