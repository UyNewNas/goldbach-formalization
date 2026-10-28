import ImbalancedChen.Part3OriginalPoissonSourceCorrections
import ImbalancedChen.Part3OriginalMediumPhysicalE3FiveAbel
import ImbalancedChen.Part3OriginalMediumEmptyE3Blocks
import ImbalancedChen.Part3OriginalMediumRetainedPhaseNormalization
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
Every actual clean source block reaches the pre-existing physical
five-coordinate Abel tower, with the full retained phase. Empty scalar
boxes are zero before any Abel call; H<1 is also handled explicitly.
The nonclean complete-lcm/root packet and all source corrections remain
on the exact source equation. No variation or prefix bound is assumed.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalE3RowReindex
open ImbalancedChen.Part3.OriginalMediumPhysicalShiftReindex
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveAbelTower
open ImbalancedChen.Part3.OriginalMediumFiveAbelGlobalFubini
open ImbalancedChen.Part3.OriginalMediumPhysicalE3FiveAbel
open ImbalancedChen.Part3.OriginalMediumEmptyE3Blocks
open ImbalancedChen.Part3.OriginalMediumRetainedPhaseNormalization
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
open ImbalancedChen.Part3.OriginalPoissonSourceCorrections20261028

namespace ImbalancedChen.Part3.OriginalSourcePhysicalAbelCaller20261028

attribute [local instance] Classical.propDecidable

/-- Assemble the existing four empty-endpoint lemmas; no new
nonempty-box premise is required from the source caller. -/
theorem E3_zero_of_not_ordered (B : FixedBlock) (ho : ¬OrderedBox B) :
    B.E3 = 0 := by
  by_cases hq : B.qLo ≤ B.qHi
  · by_cases hw : Nat.ceil B.roughLength ≤ Nat.floor (2 * B.roughLength)
    · by_cases hn : Nat.ceil B.atom.U ≤ Nat.floor (2 * B.atom.U)
      · by_cases hh : B.hLo ≤ B.hHi
        · exact False.elim (ho ⟨hq, hw, hn, hh⟩)
        · exact E3_zero_of_h_empty B (lt_of_not_ge hh)
      · exact E3_zero_of_n_empty B (lt_of_not_ge hn)
    · exact E3_zero_of_w_empty B (lt_of_not_ge hw)
  · exact E3_zero_of_q_empty B (lt_of_not_ge hq)

/-- This conditional chooses the genuine existing Abel tower only
after scalar interval order; the other branch is a proved empty sum. -/
def physicalAbelCaller (B : FixedBlock) : ℂ :=
  if ho : OrderedBox B then total B (coeff5 B) (weight5 B) else 0

theorem E3_eq_physicalAbelCaller (B : FixedBlock) :
    B.E3 = physicalAbelCaller B := by
  by_cases ho : OrderedBox B
  · simpa only [physicalAbelCaller, dif_pos ho] using E3_five_abel B ho
  · simpa only [physicalAbelCaller, dif_neg ho] using E3_zero_of_not_ordered B ho

theorem hCarrier_eq_empty_of_H_lt_one (B : FixedBlock) (hH : B.H < 1) :
    B.hCarrier = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro h hh
  obtain ⟨hlo, hhi⟩ := (Finset.mem_filter.mp hh).2
  have hloR : (1 : ℝ) ≤ (h.natAbs : ℝ) := by exact_mod_cast hlo
  linarith

/-- No real-H singleton is introduced even if the scalar Abel box is
nonempty: actual h membership makes the entire E3 empty for H<1. -/
theorem E3_zero_of_H_lt_one (B : FixedBlock) (hH : B.H < 1) : B.E3 = 0 := by
  rw [E3_eq_rawBox]
  simp only [rawBox, hCarrier_eq_empty_of_H_lt_one B hH,
    Finset.product_empty, Finset.sum_empty]

theorem physicalAbelCaller_zero_of_H_lt_one (B : FixedBlock) (hH : B.H < 1) :
    physicalAbelCaller B = 0 := by
  rw [← E3_eq_physicalAbelCaller, E3_zero_of_H_lt_one B hH]

/-- The original retained-argument normalization, instantiated at the
actual FixedBlock geometry; Q/q0 and D/d are not absorbed or replaced. -/
theorem actualBlock_retainedArgument_normalized
    (B : FixedBlock) (tq t1 t2 tn th : ℝ)
    (htq : tq ≠ 0) (ht1 : t1 ≠ 0) (ht2 : t2 ≠ 0) (htn : tn ≠ 0) :
    retainedArgument (B.atom.residue : ℝ) (B.q0 * tq) (B.d : ℝ)
      (B.roughLength * t1) (B.roughLength * t2) (B.atom.U * tn) (B.H * th) =
      ((B.atom.residue : ℝ) / B.atom.scale) * (B.atom.Q1 / B.q0) *
        (B.D / (B.d : ℝ)) * Real.log B.atom.scale ^ 5 *
          (th / (tq * t1 * t2 * tn)) := by
  have hd : (B.d : ℝ) ≠ 0 := by exact_mod_cast B.d_pos.ne'
  simpa only [FixedBlock.H, MediumAtom.scale] using
    retainedArgument_normalized (B.atom.residue : ℝ) B.atom.Q1 B.D B.roughLength
      B.atom.U B.atom.V (Real.log B.atom.scale ^ 5) B.q0 (B.d : ℝ)
      tq t1 t2 tn th B.Q_pos.ne' B.D_pos.ne' B.rough_pos.ne'
      B.U_pos.ne' B.V_pos.ne' B.q0_pos.ne' hd htq ht1 ht2 htn

def actualFamilyAbel {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) : ℂ :=
  ∑ i : SourceBlockIndex atom z y,
    physicalAbelCaller (actualProfile (genuineBlock atom z y hA Csep i)) /
      (i.2.1.val : ℂ)

theorem genuineTypedE3_eq_actualFamilyAbel {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) :
    genuineTypedE3 atom z y hA Csep = actualFamilyAbel atom z y hA Csep := by
  unfold genuineTypedE3 actualFamilyAbel
  apply Finset.sum_congr rfl
  intro i hi
  rw [E3_eq_physicalAbelCaller]

/-- The original primitive S3 now calls the actual physical Abel tower
on every clean block. All full nonclean kernels and corrections survive. -/
theorem literalS3Normalized_eq_actual_Abel_nonclean_corrections
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (Csep : ℕ) :
    literalS3Normalized atom z y = actualFamilyAbel atom z y hA Csep +
      genuineNoncleanE2 atom z y hA Csep + sourceCorrectionsNormalized atom z y := by
  rw [literalS3Normalized_eq_typed_nonclean_corrections hA z y Csep,
    genuineTypedE3_eq_actualFamilyAbel]

end ImbalancedChen.Part3.OriginalSourcePhysicalAbelCaller20261028
