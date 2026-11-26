import ImbalancedChen.Part3TwoLongRetainedRowReindex

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original generic same-Q/rho finite identity, with its complete
statement and proof preserved byte for byte in the original namespace.
Its source-only provider postimage retains the original P4 callers.
-/
namespace ImbalancedChen.P4BOriginalTwoLongActualDictionary
noncomputable section
open Classical
open scoped BigOperators
open PrimeProducts
open Part3.TwoLongActualHBShortMass
open Part3.TwoLongRetainedRowReindex
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle scales blockIntegers)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)

variable {r : ℕ}
theorem same_rho_mode_eq_fibres (bs : Fin r → Block) (Z : ℝ)
    (y xi : Fin r → ℝ) (rs : Fin r → Role) (i j : Fin r) (hij : i ≠ j)
    (N : ℕ) (S : Finset ℕ) (rho : ℕ → ℂ) :
    MellinInsertion20261028.exactDiscrepancy (rectangle bs)
      S rho completeProduct N
      (fun n => hbSlots Z y rs n * occurrenceMode (scales bs) n xi) =
      ∑ m ∈ shortSupport (fun a : ShortPositions i j => bs a.val),
        shortSequence (fun a : ShortPositions i j => bs a.val) Z
          (fun a => y a.val) (fun a => xi a.val) (fun a => rs a.val) m *
        ∑ q ∈ S, rho q *
          roughFibreCore bs Z y xi rs i j m N q := by
  simp_rw [retained_tensor_eq_shortWeight]
  unfold MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  have hp (n : Fin r → ℕ) : completeProduct n = shortProduct (restrict i j n) * n i * n j := by
    rw [completeProduct, product_two_positions i j hij]
    dsimp [shortProduct, restrict]
    ring
  simp_rw [hp]
  rw [rectangle_signed_pushforward bs Z y xi rs i j hij]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  calc
    _ = ∑ u ∈ blockIntegers (bs i), ∑ v ∈ blockIntegers (bs j),
        ∑ q ∈ S,
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (rho q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      simp only [Finset.mul_sum]
    _ = ∑ u ∈ blockIntegers (bs i), ∑ q ∈ S,
        ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (rho q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ q ∈ S, ∑ u ∈ blockIntegers (bs i),
        ∑ v ∈ blockIntegers (bs j),
          longWeight (bs i) Z (y i) (xi i) (rs i) u *
          longWeight (bs j) Z (y j) (xi j) (rs j) v *
          (rho q *
            MellinInsertion20261028.residueKernel q N (m*u*v)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      unfold roughFibreCore
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      ring

end
end ImbalancedChen.P4BOriginalTwoLongActualDictionary
