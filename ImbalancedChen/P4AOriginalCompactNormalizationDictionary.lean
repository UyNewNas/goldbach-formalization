import ImbalancedChen.P4ACompactPhysicalSupportLedger
import ImbalancedChen.P4AOrdinaryRootFirstIntegral
import ImbalancedChen.ClosedLeafStoredChargeAggregation

/-!
# P4A: original normalization and local-certificate slots for one actual rho

The exact root identity supplies 4/Theta plus the actual original U1
integral. The actual ClosedCutTree identity supplies the complete ordered
sum of leaf integrals, including closed-face and zero-leaf bookkeeping.
The installed ClosedLeafStoredChargeAggregation API then consumes positional
local leaf certificates and produces one integer sum scaled by 2^80.

No whole-compact-integral enclosure is assumed. The physical parameter
witnesses and every covering-cap threshold are chosen before the tree and
certificate entries. No original integer charge sum is evaluated here.

Draft imports for the physical support ledger and ordinary-root dictionary
must be staged under their displayed names. SOURCE ONLY / UNCOMPILED.
-/

namespace ImbalancedChen.P4AOriginalCompactNormalizationDictionary

noncomputable section

open Filter Topology MeasureTheory
open P4ASameRhoCompact OriginalThirdFiniteReserveSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClosedLeafStoredChargeP4ASourceOnly
open P4AOrdinaryRootFirstIntegral20261024zSourceOnly

/-- Exact all22 normalization before replacing any integral by a stored
endpoint. The U1 term is the actual original full-domain integral. -/
theorem root_and_compact_eq_actual_U1_and_leaf_integrals (tree : ClosedCutTree) :
    originalOrdinaryRoot + originalCompactThirdCorrection =
      4 / thirdPrefixTheta + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
        ((closedLeaves tree compactRegion).map
          (fun c => ∫ t in c, compactKernel t)).sum := by
  rw [originalOrdinaryRoot_eq_constant_add_originalFirstIntegral,
    originalCompactThirdCorrection_eq_sum_closedLeaves tree]

/-- Only local stored leaf certificates enter this comparison. The actual
closed-leaf aggregator supplies the global compact comparison internally. -/
theorem root_and_compact_le_actual_U1_and_storedCharges
    (tree : ClosedCutTree) (entries : List (ℝ × ℤ))
    (hlocal : List.Forall₂ (fun c entry =>
      (∫ t in c, compactKernel t) ≤ entry.1 ∧
        entry.1 ≤ (entry.2 : ℝ) / 2^80)
      (closedLeaves tree compactRegion) entries) :
    originalOrdinaryRoot + originalCompactThirdCorrection ≤
      4 / thirdPrefixTheta + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
        (((entries.map Prod.snd).sum : ℤ) : ℝ) / 2^80 := by
  rw [originalOrdinaryRoot_eq_constant_add_originalFirstIntegral]
  exact add_le_add_left
    (originalCompactThirdCorrection_le_sum_storedCharges tree entries hlocal) _

/-- One actual compact rho satisfies the exact original leaf-integral
normalization and, for every locally certified leaf list, its stored-charge
replacement. All support and geometric conclusions concern the same rho.

The only external input is eta>0. Local certificates are an explicit
conditional conclusion for each actual ordered leaf list, not an assumed
whole-integral bound and not a presumed all22/K certificate. -/
theorem exists_actual_rho_original_normalization_and_local_charge_slots
    (eta : ℝ) (heta : 0 < eta) :
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
            (∀ tree : ClosedCutTree,
              physicalDensitySum Q rho ≤
                (4 / thirdPrefixTheta + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
                  ((closedLeaves tree compactRegion).map
                    (fun c => ∫ t in c, compactKernel t)).sum +
                  (319683857488126290909150567 / 2^111 : ℝ) +
                  originalDensityReserve / 4 + eta) *
                    (singularSeries N / Real.log (N : ℝ))) ∧
              (∀ (tree : ClosedCutTree) (entries : List (ℝ × ℤ)),
                List.Forall₂ (fun c entry =>
                  (∫ t in c, compactKernel t) ≤ entry.1 ∧
                    entry.1 ≤ (entry.2 : ℝ) / 2^80)
                  (closedLeaves tree compactRegion) entries →
                physicalDensitySum Q rho ≤
                  (4 / thirdPrefixTheta + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
                    (((entries.map Prod.snd).sum : ℤ) : ℝ) / 2^80 +
                    (319683857488126290909150567 / 2^111 : ℝ) +
                    originalDensityReserve / 4 + eta) *
                      (singularSeries N / Real.log (N : ℝ))) ∧
              (∀ q : ℕ, rho q ≠ 0 → (q : ℝ) < (N : ℝ) ^ thirdPrefixTheta) ∧
              (∀ q : ℕ, |rho q| ≤ 1) ∧
              (∀ q ∈ Q, Squarefree q ∧ q.Coprime N) ∧
              (∀ n : ℕ,
                (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ thirdPrefixRho)))
                  then (1 : ℝ) else 0) ≤ physicalDivisorSum Q rho n) := by
  obtain ⟨h, hh, e, he0, he, m, hmesh, epsilon, hepsilon, hepsilon8,
      hepsilon1, hepsilonSupport, hepsilonR, hAllCaps⟩ :=
    P4ACompactPhysicalSupportLedger.exists_compact_physical_support_ledger eta heta
  refine ⟨h, hh, e, he0, he, m, hmesh, epsilon, hepsilon, hepsilon8,
    hepsilon1, hepsilonSupport, hepsilonR, ?_⟩
  intro cap hcap
  obtain ⟨N₀, hN₀, hSupply⟩ := hAllCaps cap hcap
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hPack := hSupply N hN hEven
  dsimp only at hPack ⊢
  obtain ⟨hDensity, hSupport, hAbs, hGeometry, hMajorant⟩ := hPack
  have hScale : 0 ≤ singularSeries N / Real.log (N : ℝ) :=
    (densityScale_pos (hN₀.trans hN)).le
  refine ⟨?_, ?_, hSupport, hAbs, hGeometry, hMajorant⟩
  · intro tree
    simpa only [originalOrdinaryRoot_eq_constant_add_originalFirstIntegral,
      originalCompactThirdCorrection_eq_sum_closedLeaves tree] using hDensity
  · intro tree entries hlocal
    have hLocalSum := root_and_compact_le_actual_U1_and_storedCharges tree entries hlocal
    have hCoefficient : originalOrdinaryRoot + originalCompactThirdCorrection +
          (319683857488126290909150567 / 2^111 : ℝ) + originalDensityReserve / 4 + eta ≤
        4 / thirdPrefixTheta + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
          (((entries.map Prod.snd).sum : ℤ) : ℝ) / 2^80 +
          (319683857488126290909150567 / 2^111 : ℝ) + originalDensityReserve / 4 + eta := by
      linarith only [hLocalSum]
    exact hDensity.trans (mul_le_mul_of_nonneg_right hCoefficient hScale)

end
end ImbalancedChen.P4AOriginalCompactNormalizationDictionary
