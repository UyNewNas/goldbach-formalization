import ImbalancedChen.Part3OriginalPoissonZeroCenteringCaller
import ImbalancedChen.Part3OriginalMediumAbelPhysicalBox
import ImbalancedChen.Part3OriginalMediumWeight0Normalized
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The original real-H carrier is preserved while its enclosing Abel
endpoints are tightened from ceil(H) to floor(H). This supplies the
actual PhysicalBox endpoint licence, rather than assuming a variation
bound on the slightly larger zero-extended scalar interval.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalShiftReindex
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveAbelTower
open ImbalancedChen.Part3.OriginalMediumFiveAbelGlobalFubini
open ImbalancedChen.Part3.OriginalMediumPhysicalE3FiveAbel
open ImbalancedChen.Part3.OriginalMediumAbelPhysicalBox
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSourcePhysicalAbelCaller20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalActualPoissonTightH20261028

attribute [local instance] Classical.propDecidable

def tightHWindow (H : ℝ) (negative : Bool) : Finset ℤ :=
  ((Finset.Icc (-(Nat.ceil H : ℤ)) (Nat.ceil H : ℤ)) ∩
    (if negative then Finset.Icc (-(Nat.floor H : ℤ)) (-1)
      else Finset.Icc 1 (Nat.floor H : ℤ))).filter
    (fun h => 1 ≤ h.natAbs ∧ (h.natAbs : ℝ) ≤ H)

private theorem floor_bounds_of_real_abs (H : ℝ) (h : ℤ)
    (hr : (h.natAbs : ℝ) ≤ H) :
    -(Nat.floor H : ℤ) ≤ h ∧ h ≤ (Nat.floor H : ℤ) := by
  have hf : h.natAbs ≤ Nat.floor H := Nat.le_floor hr
  have hi : (h.natAbs : ℤ) ≤ (Nat.floor H : ℤ) := by exact_mod_cast hf
  rw [Int.natCast_natAbs] at hi
  exact abs_le.mp hi

theorem signedHWindow_eq_tightHWindow (H : ℝ) (negative : Bool) :
    signedHWindow H negative = tightHWindow H negative := by
  ext h
  cases negative
  · simp only [signedHWindow, tightHWindow, Finset.mem_filter,
      Finset.mem_inter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hc, hs⟩, hh⟩
      exact ⟨⟨hc, ⟨hs.1, (floor_bounds_of_real_abs H h hh.2).2⟩⟩, hh⟩
    · rintro ⟨⟨hc, hs⟩, hh⟩
      exact ⟨⟨hc, ⟨hs.1, hc.2⟩⟩, hh⟩
  · simp only [signedHWindow, tightHWindow, Finset.mem_filter,
      Finset.mem_inter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hc, hs⟩, hh⟩
      exact ⟨⟨hc, ⟨(floor_bounds_of_real_abs H h hh.2).1, hs.2⟩⟩, hh⟩
    · rintro ⟨⟨hc, hs⟩, hh⟩
      exact ⟨⟨hc, ⟨hc.1, hs.2⟩⟩, hh⟩

def tightPoissonAtlasBlock {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) : FixedBlock :=
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  { B with
    hLo := if negative then -(Nat.floor B.H : ℤ) else 1
    hHi := if negative then -1 else (Nat.floor B.H : ℤ)
    h_one_sign := by cases negative <;> simp }

theorem tightPoissonAtlasBlock_hCarrier {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative).hCarrier =
      (poissonAtlasBlock atom z y k hA Csep j small hd negative).hCarrier := by
  have he := (signedHWindow_eq_tightHWindow (keyRealH atom k) negative).symm
  cases negative <;> exact he

theorem tightPoissonAtlasBlock_carrier {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative).carrier =
      (poissonAtlasBlock atom z y k hA Csep j small hd negative).carrier := by
  unfold FixedBlock.carrier
  rw [tightPoissonAtlasBlock_hCarrier]
  rfl

theorem tightPoissonAtlasBlock_E3 {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative).E3 =
      (poissonAtlasBlock atom z y k hA Csep j small hd negative).E3 := by
  unfold FixedBlock.E3
  rw [tightPoissonAtlasBlock_carrier]
  rfl

theorem admissible_scale_gt_one {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) : 1 < atom.scale := by
  exact (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans hA.2.2.2.2.2.1

/-- A genuine actual source licence for the normalized derivative box.
The excluded cases below are already proved zero E3 sums. -/
theorem tightPoissonAtlasBlock_physicalBox {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (ho : OrderedBox (poissonAtlasBlock atom z y k hA Csep j small hd negative))
    (hH : 1 ≤ (poissonAtlasBlock atom z y k hA Csep j small hd negative).H) :
    PhysicalBox (tightPoissonAtlasBlock atom z y k hA Csep j small hd negative) := by
  have hf : (1 : ℕ) ≤ Nat.floor (keyRealH atom k) := Nat.le_floor hH
  have hfI : (1 : ℤ) ≤ (Nat.floor (keyRealH atom k) : ℤ) := by exact_mod_cast hf
  have hfloor : (Nat.floor (keyRealH atom k) : ℝ) ≤ keyRealH atom k :=
    Nat.floor_le (zero_le_one.trans hH)
  refine { toOrderedBox := ⟨ho.q, ho.w, ho.n, ?_⟩,
    x_gt_one := admissible_scale_gt_one hA, h_lower := ?_, h_upper := ?_ }
  · cases negative
    · change (1 : ℤ) ≤ (Nat.floor (keyRealH atom k) : ℤ)
      exact hfI
    · change -(Nat.floor (keyRealH atom k) : ℤ) ≤ -1
      omega
  · cases negative
    · change -keyRealH atom k ≤ (1 : ℝ)
      linarith
    · change -keyRealH atom k ≤ -(Nat.floor (keyRealH atom k) : ℝ)
      linarith
  · cases negative
    · change (Nat.floor (keyRealH atom k) : ℝ) ≤ keyRealH atom k
      exact hfloor
    · change (-1 : ℝ) ≤ keyRealH atom k
      linarith

def actualTightAbelCaller {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) : ℂ :=
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  if OrderedBox B ∧ 1 ≤ B.H then total T (coeff5 T) (weight5 T) else 0

/-- Original actual E3 equals the tight physical Abel call on every
branch, with all H<1 and scalar-empty branches zero explicitly. -/
theorem actual_E3_eq_tight_Abel {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).E3 =
      actualTightAbelCaller atom z y k hA Csep j small hd negative := by
  by_cases ho : OrderedBox (poissonAtlasBlock atom z y k hA Csep j small hd negative)
  · by_cases hH : 1 ≤ (poissonAtlasBlock atom z y k hA Csep j small hd negative).H
    · have hp := tightPoissonAtlasBlock_physicalBox atom z y k hA Csep j small hd negative ho hH
      rw [← tightPoissonAtlasBlock_E3 atom z y k hA Csep j small hd negative]
      exact (E3_five_abel _ hp.toOrderedBox).trans
        (by simp only [actualTightAbelCaller, if_pos ⟨ho, hH⟩])
    · rw [E3_zero_of_H_lt_one _ (lt_of_not_ge hH)]
      simp only [actualTightAbelCaller, hH, and_false, if_false]
  · rw [E3_zero_of_not_ordered _ ho]
    simp only [actualTightAbelCaller, ho, false_and, if_false]

end ImbalancedChen.Part3.OriginalActualPoissonTightH20261028
