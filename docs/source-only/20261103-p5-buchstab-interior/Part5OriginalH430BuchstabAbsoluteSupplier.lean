import ImbalancedChen.Part5OriginalH430BuchstabInteriorDictionary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual strict Buchstab rows -> the original native atom main terms,
coefficientwise ABSOLUTE error -> all immutable430 predecessors -> one
nonnegative labelled family at one Q. The previously proved ceiling
correction is charged once. No target error, count licence, h34, hLower,
or common441 realization is a parameter of the final supplier.

The actual physical-node/prefix links, parent admission, compact positive
residual range and original lower-direction guard remain visible. Binding
all of them to the full original Program.Member graph is a separate task.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabAbsoluteSupplier

noncomputable section
open Set Filter
open scoped Classical BigOperators Topology
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430BuchstabInteriorDictionary

def absoluteInteriorError (up : Bool) (N : ℕ) (Q : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom, |closedRow up N Q old p b-
      thetaAtom N Q (parentProduct old)*integralRow up p b| *
    |oldAtomValue oldH oldh b|

def absoluteBuchstabError (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom, |strictRow up N Q chi old p b-
      thetaAtom N Q (parentProduct old)*integralRow up p b| *
    |oldAtomValue oldH oldh b|

theorem absoluteBuchstabError_nonneg (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) :
    0 ≤ absoluteBuchstabError up N Q chi old p oldH oldh :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Both error sums take absolute values before the old-array sum.
The existing ceiling payment is not concealed in a signed cancellation. -/
theorem absoluteBuchstabError_le (up : Bool) (N : ℕ) (Q chi : ℝ)
    (old : List ℕ) (p : PhysicalNode) (oldH oldh : Fin 200 → ℤ) :
    absoluteBuchstabError up N Q chi old p oldH oldh ≤
      absoluteCeilingError up N Q chi old p oldH oldh +
        absoluteInteriorError up N Q old p oldH oldh := by
  unfold absoluteBuchstabError absoluteCeilingError absoluteInteriorError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b hb
  have h := abs_sub_le (strictRow up N Q chi old p b) (closedRow up N Q old p b)
    (thetaAtom N Q (parentProduct old)*integralRow up p b)
  rw [abs_sub_comm (strictRow up N Q chi old p b) (closedRow up N Q old p b)] at h
  simpa only [add_mul] using mul_le_mul_of_nonneg_right h (abs_nonneg _)

theorem absoluteInteriorError_le {up : Bool} {N : ℕ} {Q delta : ℝ}
    {old : List ℕ} {p : PhysicalNode} (oldH oldh : Fin 200 → ℤ)
    (h : ∀ b : RowAtom,
      |closedRow up N Q old p b-thetaAtom N Q (parentProduct old)*integralRow up p b| ≤
        delta*thetaAtom N Q (parentProduct old)) :
    absoluteInteriorError up N Q old p oldH oldh ≤
      (delta*thetaAtom N Q (parentProduct old))*oldAtomL1 oldH oldh := by
  unfold absoluteInteriorError oldAtomL1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  exact mul_le_mul_of_nonneg_right (h b) (abs_nonneg _)

/-- Full two-row local supplier at the actual 430 immutable predecessors.
The common threshold is before all later targets, histories, directions,
generations and positive labelled families. No division by Theta occurs. -/
theorem immutable430_uniform_buchstab_absolute {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (old : ι → List ℕ) (p : ι → PhysicalNode) (chi sigma : ι → ℝ)
      (up : ι → Bool) (g : ι → Fin 430),
      (∀ i ∈ S, parentWindow N Q (old i) (chi i)) →
      (∀ i ∈ S, residual (p i) = physicalLevel N Q (old i)) →
      (∀ i ∈ S, (p i).ceiling = chi i) →
      (∀ i ∈ S, 1 ≤ (p i).argument) →
      (∀ i ∈ S, directionGuard (up i) (p i)) →
      (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, physicalLevel N Q (old i) ∈ Icc Lmin Lmax) →
      (∑ i ∈ S, sigma i*absoluteBuchstabError (up i) N Q (chi i) (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) ≤
        epsilon*parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
  let delta : ℝ := epsilon/(2*(immutable430AtomL1+1))
  have hM := immutable430AtomL1_nonneg
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hbudget : delta*immutable430AtomL1 ≤ epsilon/2 := by
    have heq : delta*(immutable430AtomL1+1) = epsilon/2 := by
      dsimp [delta]
      field_simp [show immutable430AtomL1+1 ≠ 0 by linarith] <;> ring
    nlinarith only [heq,hd]
  obtain ⟨Ti,hTi⟩ := uniform_closed_row_atom_error hmin hmax hd
  obtain ⟨Tc,hTc⟩ := immutable430_uniform_ceiling_error hmin
    (by positivity : 0 < epsilon/2)
  refine ⟨max 4 (max Ti Tc), ?_⟩
  intro N hN Q ι S old p chi sigma up g hw hL hC hs hg hsigma hcompact
  have hN4 : 4 ≤ N := by omega
  have htheta (i : ι) (hi : i ∈ S) : 0 ≤ thetaAtom N Q (parentProduct (old i)) :=
    thetaAtom_nonneg hN4 (hw i hi).2.1 (parentWindow_logs (hw i hi)).2.1
  have htotal : 0 ≤ parentTheta N Q S (fun i => parentProduct (old i)) sigma :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hsigma i hi) (htheta i hi))
  have hinterior :
      (∑ i ∈ S, sigma i*absoluteInteriorError (up i) N Q (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) ≤
        (epsilon/2)*parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
    have hbound : (∑ i ∈ S, sigma i*absoluteInteriorError (up i) N Q (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) ≤
        (delta*immutable430AtomL1)*parentTheta N Q S (fun i => parentProduct (old i)) sigma := by
      unfold parentTheta
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hrow := hTi N (by omega) Q (chi i) (old i) (p i) (up i)
        (hw i hi) (hL i hi) (hC i hi) (hg i hi) (hcompact i hi)
      have hlocal := (absoluteInteriorError_le (precedingH (g i)) (precedingh (g i)) hrow).trans
        (mul_le_mul_of_nonneg_left (preceding_oldAtomL1_le (g i))
          (mul_nonneg hd.le (htheta i hi)))
      have hm := mul_le_mul_of_nonneg_left hlocal (hsigma i hi)
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hm
    exact hbound.trans (mul_le_mul_of_nonneg_right hbudget htotal)
  have hceiling := hTc N (by omega) Q S old p chi sigma up g hw hL hC hs hsigma
    (fun i hi => (hcompact i hi).1)
  calc
    _ ≤ ∑ i ∈ S, sigma i *
        (absoluteCeilingError (up i) N Q (chi i) (old i) (p i)
          (precedingH (g i)) (precedingh (g i)) +
        absoluteInteriorError (up i) N Q (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (absoluteBuchstabError_le _ _ _ _ _ _ _ _) (hsigma i hi)
    _ = (∑ i ∈ S, sigma i*absoluteCeilingError (up i) N Q (chi i) (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) +
        ∑ i ∈ S, sigma i*absoluteInteriorError (up i) N Q (old i) (p i)
          (precedingH (g i)) (precedingh (g i)) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ (epsilon/2)*parentTheta N Q S (fun i => parentProduct (old i)) sigma +
        (epsilon/2)*parentTheta N Q S (fun i => parentProduct (old i)) sigma :=
      add_le_add hceiling hinterior
    _ = _ := by ring

/-- The same actual supplier handles zero total mass in absolute form.
The zero case is proved before any later normalization or feedback step. -/
theorem immutable430_uniform_buchstab_zero {Lmin Lmax : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (old : ι → List ℕ) (p : ι → PhysicalNode) (chi sigma : ι → ℝ)
      (up : ι → Bool) (g : ι → Fin 430),
      (∀ i ∈ S, parentWindow N Q (old i) (chi i)) →
      (∀ i ∈ S, residual (p i) = physicalLevel N Q (old i)) →
      (∀ i ∈ S, (p i).ceiling = chi i) →
      (∀ i ∈ S, 1 ≤ (p i).argument) →
      (∀ i ∈ S, directionGuard (up i) (p i)) →
      (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, physicalLevel N Q (old i) ∈ Icc Lmin Lmax) →
      parentTheta N Q S (fun i => parentProduct (old i)) sigma = 0 →
      (∑ i ∈ S, sigma i*absoluteBuchstabError (up i) N Q (chi i) (old i) (p i)
          (precedingH (g i)) (precedingh (g i))) = 0 := by
  obtain ⟨T,hT⟩ := immutable430_uniform_buchstab_absolute hmin hmax (by norm_num : (0:ℝ) < 1)
  refine ⟨T, ?_⟩
  intro N hN Q ι S old p chi sigma up g hw hL hC hs hg hsigma hcompact hzero
  apply le_antisymm
  · simpa only [hzero,mul_zero] using
      hT N hN Q S old p chi sigma up g hw hL hC hs hg hsigma hcompact
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hsigma i hi)
      (absoluteBuchstabError_nonneg _ _ _ _ _ _ _ _))

end
end ImbalancedChen.Part5OriginalH430BuchstabAbsoluteSupplier
