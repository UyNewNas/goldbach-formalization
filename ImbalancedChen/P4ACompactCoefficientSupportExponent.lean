import ImbalancedChen.ActualExtendedThirdCompactUpperRho
import ImbalancedChen.RosserShortPrefixAdmissibility
import ImbalancedChen.ActualUpperCountingInputs

/-!
# P4A: actual compact-policy support exponents

Every adopted compact level is a literal minimum with the original root
exponent. Hence every approved compact history is approved by the ordinary
parity upper policy at the root level. The retained-selection dictionary
and actual ordinary Rosser support theorem then bound each rough modulus.

The nonzero physical coefficient factors into that rough modulus and an
actual small Rosser factor strictly below L. This controls active support;
the larger displayed small divisor carrier need not lie below L.

Structural conditions: N>=2 and e<=1/384 ensure the original root level
exceeds one. No compact mesh or h positivity is needed for this support
bound. Epsilon<=2e pays its small-factor exponent within thirdPrefixTheta.

SOURCE ONLY; no compilation was performed.
-/

namespace ImbalancedChen.P4ACompactCoefficientSupportExponent

noncomputable section

open scoped Classical

theorem compactCellLevel_le_root (e h : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    actualExtendedThirdCompactCellLevel e h m t ≤ thirdPrefixTheta - 2 * e := by
  by_cases ht : ∃ j ∈ actualExtendedThirdCompactCells e h m,
      t ∈ actualExtendedThirdOwnedCell m j
  · obtain ⟨j, hj, ht⟩ := ht
    rw [actualExtendedThirdCompactCellLevel_on_cell hj ht]
    exact thirdPrefixBufferedCap_le_root e (actualExtendedThirdPhysicalGamma e m j)
  · have hout : ∀ j ∈ actualExtendedThirdCompactCells e h m,
        t ∉ actualExtendedThirdOwnedCell m j := by
      intro j hj htj
      exact ht ⟨j, hj, htj⟩
    exact (actualExtendedThirdCompactCellLevel_outside hout).le

theorem compactRawLevel_le_root (e h : ℝ) (m N : ℕ)
    (hN : (1 : ℝ) ≤ (N : ℝ)) (history : List ℕ) :
    actualExtendedThirdCompactRawLevel e h m N history ≤
      (N : ℝ) ^ (thirdPrefixTheta - 2 * e) := by
  unfold actualExtendedThirdCompactRawLevel
  exact Real.rpow_le_rpow_of_exponent_le hN (compactCellLevel_le_root e h m _)

/-- Actual compact approvals imply ordinary root-level parity approvals.
This statement is proved for all histories, before any tree is traversed. -/
theorem compactPolicy_implies_ordinary_root
    (e h : ℝ) (m N : ℕ) (hN : (1 : ℝ) ≤ (N : ℝ))
    (positive : Bool) (history : List ℕ)
    (hp : actualExtendedThirdCompactUpperPolicy e h m N positive history = true) :
    ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
      positive history = true := by
  cases positive with
  | true => exact ordinaryParityRosserPolicy_upper_even _ _
  | false =>
      have hadm : ordinaryRosserPrefixAdmissible false
          ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) history := by
        by_cases hlen : history.length ≤ 2
        · rw [actualExtendedThirdCompactUpperPolicy_through_two e h m N false history hlen]
            at hp
          have hpair : ordinaryRosserPrefixAdmissible false
              ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) history ∧
              (history.length = 1 → actualExtendedThirdCompactFirstStop e m N history) := by
            simpa [actualExtendedThirdCompactInitialPolicy, oddFirstExitPolicy] using hp
          exact hpair.1
        · have hraw : ordinaryRosserPrefixAdmissible false
              (actualExtendedThirdCompactRawLevel e h m N (rosserAncestor 3 history))
              history := by
            simpa [actualExtendedThirdCompactUpperPolicy, thirdCappedUpperPolicy,
              firstExitDepthSplicePolicy, hlen, frozenParityRosserPolicy,
              ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
          exact ordinaryRosserPrefixAdmissible_mono false history
            (compactRawLevel_le_root e h m N hN _) hraw
      simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hadm

private theorem validSelection_mono
    (policy larger : Bool → List ℕ → Bool)
    (hdom : ∀ positive history, policy positive history = true →
      larger positive history = true)
    (pre chosen : List ℕ) (positive : Bool)
    (hvalid : FirstExitValidSelection policy pre positive chosen) :
    FirstExitValidSelection larger pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => trivial
  | cons p ps ih =>
      exact ⟨hdom (!positive) (p :: pre) hvalid.1,
        ih (p :: pre) (!positive) hvalid.2⟩

private theorem retainedModuli_subset
    (policy larger : Bool → List ℕ → Bool)
    (hdom : ∀ positive history, policy positive history = true →
      larger positive history = true) (carrier : List ℕ) :
    firstExitRetainedModuli policy carrier ⊆ firstExitRetainedModuli larger carrier := by
  intro d hd
  obtain ⟨chosen, hsub, hvalid, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection policy carrier d).mp hd
  exact (mem_firstExitRetainedModuli_iff_validSelection larger carrier d).mpr
    ⟨chosen, hsub, validSelection_mono policy larger hdom [] chosen true hvalid, hprod⟩

/-- Every actual rough retained modulus is strictly below the original
root level, for any cap and rough cutoffs. -/
theorem fixedRoughSupport_lt_root (e h : ℝ) (m N cap : ℕ) (w z : ℝ)
    (hN : 2 ≤ N) (he : e ≤ 1 / 384) {d : ℕ}
    (hd : d ∈ fixedRoughSupport
      (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z) :
    (d : ℝ) < (N : ℝ) ^ (thirdPrefixTheta - 2 * e) := by
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hrootExp : 0 < thirdPrefixTheta - 2 * e := by
    dsimp [thirdPrefixTheta]
    linarith
  have hroot : 1 < (N : ℝ) ^ (thirdPrefixTheta - 2 * e) :=
    Real.one_lt_rpow hNreal hrootExp
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (actualExtendedThirdCompactUpperPolicy e h m N)
    (actualExtendedThirdCompactUpperPolicy_even e h m N) N cap w z] at hd
  have hparity := retainedModuli_subset
    (actualExtendedThirdCompactUpperPolicy e h m N)
    (ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)))
    (compactPolicy_implies_ordinary_root e h m N hNreal.le)
    (roughPrimeUniverse N cap w z) hd
  rw [ordinaryParityRosserRetainedModuli_eq false _ hroot
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_pairwise_gt N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (by simp)] at hparity
  exact ((mem_ordinaryRosserRetainedModuli_iff false _ hroot
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_pairwise_gt N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) d).mp hparity).2.1

/-- Active physical support pays exactly the small Rosser level exponent.
No bound for the displayed, potentially zero, coefficients is postulated. -/
theorem actualCompactRho_ne_zero_lt_root_add_epsilon
    (e h epsilon : ℝ) (m N cap : ℕ) (w z : ℝ)
    (hN : 2 ≤ N) (he : e ≤ 1 / 384) {q : ℕ}
    (hq : actualExtendedThirdCompactRho e h m N cap w z
      ((N : ℝ) ^ epsilon) q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ (thirdPrefixTheta - 2 * e + epsilon) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  obtain ⟨a, _ha, b, hb, hprod, haL, _hbne⟩ :=
    actualSmallRoughRho_ne_zero_factors
      (actualExtendedThirdCompactUpperPolicy e h m N false)
      N cap w z ((N : ℝ) ^ epsilon) hq
  have hbRoot := fixedRoughSupport_lt_root e h m N cap w z hN he hb
  have hL : 0 < (N : ℝ) ^ epsilon := Real.rpow_pos_of_pos hNpos _
  calc
    (q : ℝ) = (a : ℝ) * (b : ℝ) := by rw [hprod, Nat.cast_mul]
    _ ≤ (N : ℝ) ^ epsilon * (b : ℝ) :=
      mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg _)
    _ < (N : ℝ) ^ epsilon * (N : ℝ) ^ (thirdPrefixTheta - 2 * e) :=
      mul_lt_mul_of_pos_left hbRoot hL
    _ = (N : ℝ) ^ (thirdPrefixTheta - 2 * e + epsilon) := by
      rw [Real.rpow_add hNpos]
      ring

/-- Epsilon<=2e absorbs the attachment level in the original theta
exponent. Positivity of epsilon is not needed for this finite implication. -/
theorem actualCompactRho_ne_zero_lt_theta
    (e h epsilon : ℝ) (m N cap : ℕ) (w z : ℝ)
    (hN : 2 ≤ N) (he : e ≤ 1 / 384) (hepsilon : epsilon ≤ 2 * e) {q : ℕ}
    (hq : actualExtendedThirdCompactRho e h m N cap w z
      ((N : ℝ) ^ epsilon) q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ thirdPrefixTheta := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  exact (actualCompactRho_ne_zero_lt_root_add_epsilon e h epsilon m N cap w z hN he hq).trans_le
    (Real.rpow_le_rpow_of_exponent_le hNreal (by linarith))

/-- The counting interface uses exactly the same physical coefficient.
This specializes the support result to nu=1 and the actual compact cutoff. -/
theorem attachedUpperCoefficient_ne_zero_lt_theta
    (e h epsilon : ℝ) (m N : ℕ) (cap : ℕ → ℕ)
    (hN : 2 ≤ N) (he : e ≤ 1 / 384) (hepsilon : epsilon ≤ 2 * e) {q : ℕ}
    (hq : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) cap N q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ thirdPrefixTheta := by
  apply actualCompactRho_ne_zero_lt_theta e h epsilon m N (cap N)
    ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) hN he hepsilon
  simpa only [attachedUpperCoefficient, one_mul, actualExtendedThirdCompactRho] using hq

end
end ImbalancedChen.P4ACompactCoefficientSupportExponent
