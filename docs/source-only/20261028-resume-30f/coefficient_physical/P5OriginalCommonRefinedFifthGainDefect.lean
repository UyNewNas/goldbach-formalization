import ImbalancedChen.P5OriginalCommonRefinedSeedHull
import ImbalancedChen.P1OriginalCoarseFifthCellIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The kernel is the original canonical LOWER/I5 profile with TWO independent
strict own-cube indicators.  Raising the common fourth parent consumes a
specific part of the old fifth gain.  The clipping formula below computes
this part; approval/support inclusion is not used as signed monotonicity.
These are continuous-kernel identities evaluated on actual prime histories.
The finite arithmetic densities are not replaced by these kernels: their
same-policy common compact approximation and attached errors remain open.
-/
namespace ImbalancedChen.P5OriginalCommonRefinedFifthGainDefect
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P1OriginalFifthIntegral

/-- An exact clipping identity, without differentiating or replacing the
two own-cube indicators by a common gate. -/
theorem kernel_hull_defect (a b f : ℝ) (hab : a ≤ b) (t : Fin 5 → ℝ) :
    cellKernel a b t - cellKernel (max a f) (max b f) t =
      cellKernel a (min (max a f) b) t := by
  by_cases hfa : f ≤ a
  · rw [max_eq_left hfa, max_eq_left (hfa.trans hab), min_eq_left hab]
    simp [cellKernel]
  · have haf : a ≤ f := le_of_lt (lt_of_not_ge hfa)
    by_cases hfb : f ≤ b
    · rw [max_eq_right haf, max_eq_left hfb, min_eq_left hfb]
      unfold cellKernel
      ring
    · have hbf : b ≤ f := le_of_lt (lt_of_not_ge hfb)
      rw [max_eq_right haf, max_eq_right hbf, min_eq_right hbf]
      simp [cellKernel]

theorem cellKernel_nonneg (a b : ℝ) (hab : a ≤ b) (t : Fin 5 → ℝ)
    (ht : ∀ i, 0 < t i) : 0 ≤ cellKernel a b t := by
  exact mul_nonneg (sub_nonneg.mpr (p1PrimeOwnCubeGatedProfile_mono
    t (ht (Fin.last 4)) hab))
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le))

theorem cellKernel_mono_new (a b c : ℝ) (hbc : b ≤ c) (t : Fin 5 → ℝ)
    (ht : ∀ i, 0 < t i) : cellKernel a b t ≤ cellKernel a c t := by
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_right (p1PrimeOwnCubeGatedProfile_mono t (ht (Fin.last 4)) hbc) _)
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le))

def oldGain (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  cellKernel (oldInherited d N pre) (oldFifth d N pre)
    (primeHistoryLogCoordinates N 5 pre)

def commonGain (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  cellKernel (commonInherited d N pre) (exponent5 d N pre)
    (primeHistoryLogCoordinates N 5 pre)

/-- The actual old fifth final cap clips the parent charge. The charge
does not keep growing after the old fifth increment has been exhausted. -/
def parentGainDefect (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  cellKernel (oldInherited d N pre)
    (min (commonInherited d N pre) (oldFifth d N pre))
    (primeHistoryLogCoordinates N 5 pre)

theorem oldGain_sub_commonGain (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    oldGain d N pre - commonGain d N pre = parentGainDefect d N pre := by
  unfold oldGain commonGain parentGainDefect
  rw [fifth_eq_old_max_fallback, inherited_eq_old_max_fallback]
  exact kernel_hull_defect _ _ _ (oldInherited_le_oldFifth d N pre) _

theorem defect_nonneg (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (ht : ∀ i, 0 < primeHistoryLogCoordinates N 5 pre i) :
    0 ≤ parentGainDefect d N pre := by
  apply cellKernel_nonneg _ _ _ _ ht
  exact le_min ((le_max_left _ _).trans_eq (inherited_eq_old_max_fallback d N pre).symm)
    (oldInherited_le_oldFifth d N pre)

theorem commonGain_nonneg (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (ht : ∀ i, 0 < primeHistoryLogCoordinates N 5 pre i) :
    0 ≤ commonGain d N pre :=
  cellKernel_nonneg _ _ (P5OriginalCommonRefinedPreservation.inherited4_le_exponent5 d N pre) _ ht

/-- This is the canonical kernel comparison only. It is deliberately NOT
a monotonicity theorem for finite signed arithmetic Rosser densities. -/
theorem commonGain_le_oldGain (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (ht : ∀ i, 0 < primeHistoryLogCoordinates N 5 pre i) :
    commonGain d N pre ≤ oldGain d N pre := by
  have hn := defect_nonneg d N pre ht
  rw [← oldGain_sub_commonGain] at hn
  exact sub_nonneg.mp hn

theorem defect_le_full_parent_charge (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (ht : ∀ i, 0 < primeHistoryLogCoordinates N 5 pre i) :
    parentGainDefect d N pre ≤
      cellKernel (oldInherited d N pre) (commonInherited d N pre)
        (primeHistoryLogCoordinates N 5 pre) :=
  cellKernel_mono_new _ _ _ (min_le_left _ _) _ ht

theorem defect_le_oldGain (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (ht : ∀ i, 0 < primeHistoryLogCoordinates N 5 pre i) :
    parentGainDefect d N pre ≤ oldGain d N pre := by
  rw [← oldGain_sub_commonGain]
  exact sub_le_self _ (commonGain_nonneg d N pre ht)

theorem defect_zero_off_changedParents (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5) (hout : pre ∉ changedParents d N) :
    parentGainDefect d N pre = 0 := by
  have he : commonInherited d N pre = oldInherited d N pre := by
    by_contra hn
    exact hout ⟨hlen, hn⟩
  simp only [parentGainDefect, he, min_eq_left (oldInherited_le_oldFifth d N pre),
    cellKernel, sub_self, zero_mul]

/-- If fallback clears the old final fifth cap, ALL the old local fifth
increment has already been spent on its newly raised current parent. -/
theorem commonGain_zero_of_fallback_above_old_fifth (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hf : oldFifth d N pre ≤ inheritedFallback d N pre) :
    commonGain d N pre = 0 := by
  simp only [commonGain, fallback_above_old_fifth d N pre hf, cellKernel, sub_self, zero_mul]

/-- Both literal strict own-cube gates of the old gain remain visible. -/
theorem defect_eq_two_indicators (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    parentGainDefect d N pre =
      ((if primeTupleOwnCubeForm (primeHistoryLogCoordinates N 5 pre) <
          min (commonInherited d N pre) (oldFifth d N pre) then
          primeTupleMinusProfile (min (commonInherited d N pre) (oldFifth d N pre))
            (primeHistoryLogCoordinates N 5 pre) else 0) -
        (if primeTupleOwnCubeForm (primeHistoryLogCoordinates N 5 pre) < oldInherited d N pre then
          primeTupleMinusProfile (oldInherited d N pre) (primeHistoryLogCoordinates N 5 pre) else 0)) *
        ∏ i, 1 / primeHistoryLogCoordinates N 5 pre i := rfl

end
end ImbalancedChen.P5OriginalCommonRefinedFifthGainDefect
