import ImbalancedChen.Part3OriginalSourcePoissonFamilyDictionary
import Mathlib.Tactic

/-!
Source only, uncompiled, zero formal credit.
The real key-H window and its integer floor are exactly reconciled,
including H<1. Both signed ownership pieces are disjoint and exhaustive
on nonzero integers. Actual sourceMode and lambdaTrim support then allow
whole-key carrier rearrangements without inventing a numerical cutoff.
-/

noncomputable section
open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalPhysicalPoissonTruncation20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSourcePoissonFamilyDictionary20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalPoissonFrequencyOwnership20261028

/-- Real-window pieces sit inside the integer floor window, not ceil(H). -/
theorem signedHWindow_subset_floorWindow (H : ℝ) (negative : Bool) :
    signedHWindow H negative ⊆ signedWindow (Nat.floor H) := by
  intro h hh
  have hr := (Finset.mem_filter.mp hh).2.2
  exact (mem_signedWindow _ _).mpr (Nat.le_floor hr)

/-- Both actual signed h windows exactly partition a finite Poisson sum;
frequency zero is independently known to have zero coefficient. -/
theorem sum_signedHWindows_eq_floorWindow {H : ℝ} (hH : 0 ≤ H)
    (f : ℤ → ℂ) (hf : f 0 = 0) :
    (∑ negative : Bool, ∑ h ∈ signedHWindow H negative, f h) =
      ∑ h ∈ signedWindow (Nat.floor H), f h := by
  have hsub := signedHWindow_subset_floorWindow H
  calc
    _ = ∑ negative : Bool, ∑ h ∈ signedWindow (Nat.floor H),
        if h ∈ signedHWindow H negative then f h else 0 := by
      apply Finset.sum_congr rfl
      intro negative hn
      rw [← Finset.sum_filter]
      congr 1
      ext h
      simp only [Finset.mem_filter]
      exact ⟨fun hh => hh.2, fun hh => ⟨hsub negative hh, hh⟩⟩
    _ = ∑ h ∈ signedWindow (Nat.floor H), ∑ negative : Bool,
        if h ∈ signedHWindow H negative then f h else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hz : h = 0
      · subst h
        simp only [hf, ite_self, Finset.sum_const_zero]
      · have hn : 1 ≤ h.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz)
        have hreal : (h.natAbs : ℝ) ≤ H :=
          (show (h.natAbs : ℝ) ≤ (Nat.floor H : ℝ) by
            exact_mod_cast (mem_signedWindow _ _).mp hh).trans (Nat.floor_le hH)
        obtain ⟨negative, hneg, hu⟩ := (signedHWindow_unique H h).mp ⟨hn, hreal⟩
        rw [Finset.sum_eq_single negative]
        · simp only [if_pos hneg]
        · intro other ho hne
          exact if_neg (fun hm => hne (hu other hm))
        · simp

/-- The actual source packet has zero h=0 coefficient on both compatible
and incompatible branches. -/
theorem sourceMode_zero (atom : MediumAtom) (z y : ℝ) (k : Key) (v : FibreIndex) :
    sourceMode atom z y k v 0 = 0 := by
  simp [sourceMode, paperPsiNonzeroMode]

theorem actual_keyRealH_nonneg {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (k : Key) : 0 ≤ keyRealH atom k := by
  have hx : 1 ≤ atom.scale := by
    unfold MediumAtom.scale
    nlinarith [hA.1, hA.2.1]
  have hlog := Real.log_nonneg hx
  have hQ : 0 < atom.Q1 := lt_of_lt_of_le zero_lt_one hA.2.2.1
  have hV : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  unfold keyRealH keyD keyR
  positivity

/-- Actual retained source packet, split into the family's real positive
and negative H windows, with no change of modulus or Fourier profile. -/
theorem head_retained_eq_actual_signed_windows
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) (v : FibreIndex) :
    headCoefficient atom (strictReceiverCutoff z) y k v *
      retainedModes atom (sourceKeyH atom k) v =
        ∑ negative : Bool, ∑ h ∈ signedHWindow (keyRealH atom k) negative,
          sourceMode atom z y k v h := by
  rw [head_retained_eq_source_modes]
  exact (sum_signedHWindows_eq_floorWindow (actual_keyRealH_nonneg hA k)
    (sourceMode atom z y k v) (sourceMode_zero atom z y k v)).symm

/-- Primitive-d exclusion is an exact zero of the actual coefficient. -/
theorem sourceMode_zero_of_nonprimitive_d
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key)
    (q small r s n1 n2 : ℕ) (h : ℤ) (hc : ¬small.Coprime atom.residue.natAbs) :
    sourceMode atom z y k (sourceFibre q small r s n1 n2) h = 0 := by
  have hz := lambdaTrim_zero_of_nonprimitive atom (strictReceiverCutoff z) y k small r hA hc
  simp [sourceMode, headCoefficient, sourceFibre, hz]

/-- Closed upper rough endpoints introduced by FixedBlock carry zero
actual source mass whenever they fall outside the owned half-open window. -/
theorem sourceMode_zero_of_left_rough_outside (atom : MediumAtom) (z y : ℝ) (k : Key)
    (q small r s n1 n2 : ℕ) (h : ℤ) (hr : r ∉ dyadicWindow k.w) :
    sourceMode atom z y k (sourceFibre q small r s n1 n2) h = 0 := by
  have hz := lambdaTrim_zero_outside_rough_window atom (strictReceiverCutoff z) y k small r hr
  simp [sourceMode, headCoefficient, sourceFibre, hz]

theorem sourceMode_zero_of_right_rough_outside (atom : MediumAtom) (z y : ℝ) (k : Key)
    (q small r s n1 n2 : ℕ) (h : ℤ) (hs : s ∉ dyadicWindow k.w) :
    sourceMode atom z y k (sourceFibre q small r s n1 n2) h = 0 := by
  have hz := lambdaTrim_zero_outside_rough_window atom (strictReceiverCutoff z) y k small s hs
  simp [sourceMode, headCoefficient, sourceFibre, hz]

end ImbalancedChen.Part3.OriginalPoissonFrequencyOwnership20261028
