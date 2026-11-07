import ImbalancedChen.P5SameWholeAssignmentPerLabel
import ImbalancedChen.P5All16MarkedFineScalarBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Independent actual ALL16 marked+rough common-fine Cartesian source ->
the SAME fixed whole-word original per-label tensor. The independently
proved marked multiplicities are not divided out of the physical source.
Its literal original restoring scalar is consumed once, together with
the entire beta sum in group3. No outside marked prime product remains.
-/

namespace ImbalancedChen.P5Z.ActualMarkedSameAssignmentTensor
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open OriginalOrdinaryPresievedSigma
open All16FineMeshGateScalar All16InnerCartesianDictionary
open All16MarkedCommonFineSource All16MarkedFineScalarBudget
open ActualInnerPerLabelGamma SameWholeAssignmentPerLabel

theorem actual_marked_whole_gamma_bounds {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} {rho betaLevel : ℝ} {M : Set (ℝ × ℝ)}
    {c : CoarseGrid n} {a : PresievedRoughGateMeshReserve.Grid 4 m}
    {j : PresievedRoughGateMeshReserve.Grid r m}
    (h : WholeCell eta rho M c a j) (hcut : rho ≤ cellZeta n eta c)
    (out : List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1)))
    (hpart : (out.1 ++ out.2.1 ++ out.2.2).Perm (fullWord a j)) :
    (∀ x, |gamma (commonAlphabet N m) out.1 x| ≤ 1) ∧
      (∀ y, |gamma (commonAlphabet N m) out.2.1 y| ≤ 1) ∧
      (∀ q3, |SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m) out.2.2
        N (cellCap n N eta c) r ((N : ℝ) ^ rho) betaLevel q3| ≤ 1) := by
  exact same_assignment_one_bounds (commonAlphabet N m) (fullWord a j) out hpart (full_word_nodup h)
    N (cellCap n N eta c) r ((N : ℝ) ^ rho) betaLevel
    (fun _ _ hp => (mem_roughPrimeFinset.mp (ActualInnerMeshSeparatedGamma.mesh_prime_rough hp)).2.1)
    (ActualInnerPerLabelGamma.mesh_alphabet_disjoint hN 1 N)
    (fun i hi p hp => whole_label_rough_lower hN h hcut hi hp)

/-- Actual original all16 coefficient, all four marked primes and all
small beta terms -> original restoring scalar times SAME whole-word
three-gamma convolution, before count or coprime-mean tests are chosen. -/
theorem actual_marked_whole_source_tensor {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) {rho betaLevel : ℝ} {M : Set (ℝ × ℝ)}
    {c : CoarseGrid n} {a : PresievedRoughGateMeshReserve.Grid 4 m}
    {j : PresievedRoughGateMeshReserve.Grid r m}
    (h : WholeCell eta rho M c a j) (hcut : rho ≤ cellZeta n eta c)
    (out : List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1)))
    (hpart : (out.1 ++ out.2.1 ++ out.2.2).Perm (fullWord a j)) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N (cellCap n N eta c) ((N : ℝ) ^ rho),
      ∑ p ∈ commonVectors N m 4 a, ∑ u ∈ commonVectors N m r j,
        rowCoefficient n N eta ((N : ℝ) ^ rho) betaLevel (pack p) (e * (List.ofFn u).prod) *
          F (U1011OriginalSixteenArithmeticProducts.fullPrefix (pack p) * (e * (List.ofFn u).prod))) =
      ∑ x ∈ support (commonAlphabet N m) out.1, ∑ y ∈ support (commonAlphabet N m) out.2.1,
        ∑ q3 ∈ SameWholeAssignmentPerLabel.attachedSupport (commonAlphabet N m) out.2.2
          N (cellCap n N eta c) ((N : ℝ) ^ rho),
          restoringScalar 1 j out * gamma (commonAlphabet N m) out.1 x *
            gamma (commonAlphabet N m) out.2.1 y *
              SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m) out.2.2
                N (cellCap n N eta c) r ((N : ℝ) ^ rho) betaLevel q3 * F (x * y * q3) := by
  have hMall := multiplicity_eq_one_of_nodup (fullWord a j) (full_word_nodup h)
  have hMres := inner_mesh_multiplicity_one (cellEll n eta c) h.inner
  have hraw := whole_cell_source_eq_raw_full_box hN heta h F
  have htensor := same_assignment_beta_tensor (commonAlphabet N m) (fullWord a j) out hpart
    N (cellCap n N eta c) r ((N : ℝ) ^ rho) betaLevel ((-1 : ℝ) ^ r)
    (fun i hi p hp => (mem_roughPrimeFinset.mp (ActualInnerMeshSeparatedGamma.mesh_prime_rough hp)).2.1)
    (fun i hi p hp => whole_label_rough_lower hN h hcut hi hp) F
  calc
    _ = ∑ e ∈ actualSmallRosserSupport N (cellCap n N eta c) ((N : ℝ) ^ rho),
        ((-1 : ℝ) ^ r * ActualAll16UnrestrictedResidualConvolution.rawBetaWeight N (cellCap n N eta c) r
          ((N : ℝ) ^ rho) betaLevel e / (multiplicity (fullWord a j) : ℝ)) *
            ∑ xs ∈ actualPrimeSlotBox (commonAlphabet N m) (fullWord a j), F (e * xs.prod) := by
      rw [hraw, hMres, hMall]
      simp only [Nat.cast_one, div_one, Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [htensor]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro q3 hq3
      rw [hMall]
      dsimp only [restoringScalar]
      rw [hMres]
      ring

end
end ImbalancedChen.P5Z.ActualMarkedSameAssignmentTensor
