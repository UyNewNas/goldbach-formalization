import ImbalancedChen.Part5OriginalUpsilon5FloorKernel
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-!
Original enhanced U5 prime-harmonic transport. SOURCE ONLY; never compiled.

The continuous part uses the actual convergent lower factor on all of [2,5].
The finite floor is transported by eight affine branches, with weak/strict
ownership retained, including every singleton knot of the literal lookup.
No table soundness, causal density identification, or physical support licence
is inferred from this harmonic statement.
-/

namespace ImbalancedChen.Part5OriginalUpsilon5CausalDictionary

noncomputable section

open Filter Topology MeasureTheory Set
open scoped Classical BigOperators

abbrev currentCube : Set (Fin 2 → ℝ) := univ.pi (fun _ : Fin 2 => Icc a h)

/-- The enhanced kernel is regular even on the unordered ambient square.
This supplies the actual prime test, which requires the whole closed cube. -/
theorem cube_residual_argument_bounds {x : Fin 2 → ℝ} (hx : x ∈ currentCube) :
    0 < residual x ∧ argument x ∈ Icc (2 : ℝ) 5 := by
  have h0 := hx 0 (mem_univ _)
  have h1 := hx 1 (mem_univ _)
  have hl : VariableEnvelope.B a ≤ level (x 0) (x 1) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hvA (t : ℝ) : VariableEnvelope.v t ≤ VariableEnvelope.A t := by
    rw [VariableEnvelope.v_eq_min]
    exact min_le_left _ _
  have hu : level (x 0) (x 1) ≤ x 0 + x 1 + 5 * a := by
    unfold level
    apply max_le
    · exact (hvA _).trans (by
        dsimp [VariableEnvelope.A, a] at *; linarith [h0.1, h1.1])
    · apply max_le
      · exact (hvA _).trans (by
          dsimp [VariableEnvelope.A, a] at *; linarith [h0.1, h1.1])
      · dsimp [VariableEnvelope.B, VariableEnvelope.cap, a] at *
        linarith [h0.1, h1.1]
  have hlow : 2 * a < residual x := by
    dsimp [residual, VariableEnvelope.B, VariableEnvelope.cap, a, h] at *
    linarith [h0.2, h1.2]
  have ha : 0 < a := by norm_num [a]
  refine ⟨lt_trans (by positivity : 0 < 2 * a) hlow, ?_, ?_⟩
  · exact (le_div_iff₀ ha).mpr hlow.le
  · apply (div_le_iff₀ ha).mpr
    dsimp [residual]
    linarith

theorem continuousOn_enhanced_kernel_cube (corr : ℝ → ℝ)
    (hc : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    ContinuousOn (kernel corr) currentCube := by
  have hm : MapsTo argument currentCube (Icc (2 : ℝ) 5) :=
    fun _ hx => (cube_residual_argument_bounds hx).2
  exact (continuousOn_const.mul
    ((continuousOn_lowerAmplitude.comp continuous_argument.continuousOn hm).add
      (hc.comp continuous_argument.continuousOn hm))).div
    continuous_residual.continuousOn
    (fun _ hx => (cube_residual_argument_bounds hx).1.ne')

def nativeEnhancedHarmonic (N : ℕ) (corr : ℝ → ℝ) : ℝ :=
  ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ h),
    kernel corr (actualPrimeTupleLog N ![t.1, t.2]) /
      (Nat.totient (t.1 * t.2) : ℝ)

/-- Genuine enhanced, varying-level test; s>4 keeps the actual lower factor. -/
theorem tendsto_nativeEnhancedHarmonic_continuous (corr : ℝ → ℝ)
    (hc : ContinuousOn corr (Icc (2 : ℝ) 5)) :
    Tendsto (fun N : ℕ => nativeEnhancedHarmonic N corr) atTop (𝓝 (integral corr)) := by
  simpa only [nativeEnhancedHarmonic, integral, triangle, a, h] using
    tendsto_currentChenUpsilon5_harmonic_test (kernel corr)
      (continuousOn_enhanced_kernel_cube corr hc)

def harmonicCorrection (x : Fin 2 → ℝ) : ℝ := 4 / residual x

theorem continuousOn_harmonicCorrection_cube :
    ContinuousOn harmonicCorrection currentCube :=
  continuousOn_const.div continuous_residual.continuousOn
    (fun _ hx => (cube_residual_argument_bounds hx).1.ne')

/-! A concrete finite max/min circuit for the actual enhanced residual. -/

def residualSlope : Fin 4 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ![-ContinuousLinearMap.proj 0 - (1 / 2 : ℝ) • ContinuousLinearMap.proj 1,
    -(1 / 2 : ℝ) • (ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1),
    -(5 / 2 : ℝ) • (ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1),
    -ContinuousLinearMap.proj 0 - ContinuousLinearMap.proj 1]

def residualOffset : Fin 4 → ℝ := ![1 / 2, 1 / 2, 57 / 64, VariableEnvelope.B a]
def residualAffine (j : Fin 4) (x : Fin 2 → ℝ) : ℝ := residualOffset j + residualSlope j x

theorem residualSlope_ne_zero (j : Fin 4) : residualSlope j ≠ 0 := by
  intro he
  have he' := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L ![1, 0]) he
  fin_cases j <;> norm_num [residualSlope] at he'

theorem residualSlope_sub_ne_zero {i j : Fin 4} (hij : i ≠ j) :
    residualSlope i - residualSlope j ≠ 0 := by
  intro he
  have h0 := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L ![1, 0]) he
  have h1 := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L ![0, 1]) he
  fin_cases i <;> fin_cases j <;> norm_num [residualSlope] at *

theorem residual_eq_affine_circuit {x : Fin 2 → ℝ} (hx : x ∈ currentCube) :
    residual x = max (residualAffine 0 x)
      (max (min (residualAffine 1 x) (residualAffine 2 x)) (residualAffine 3 x)) := by
  have ht : x 1 ≤ VariableEnvelope.mu := by
    have hh := (hx 1 (mem_univ _)).2
    norm_num [h, VariableEnvelope.mu] at *
    linarith
  unfold residual level
  rw [VariableEnvelope.v_eq_A ht, VariableEnvelope.v_eq_min]
  simp only [← max_sub_sub_right, ← min_sub_sub_right]
  congr 1
  · simp [residualAffine, residualOffset, residualSlope, VariableEnvelope.A]
    <;> ring
  · congr 1
    · congr 1 <;>
        simp [residualAffine, residualOffset, residualSlope,
          VariableEnvelope.A, VariableEnvelope.C] <;> ring
    · simp [residualAffine, residualOffset, residualSlope]
      <;> ring

abbrev EnhancedBranch := Bool × Bool × Bool

def minIndex (b : EnhancedBranch) : Fin 4 := if b.1 then 1 else 2
def upperIndex (b : EnhancedBranch) : Fin 4 := if b.2.1 then minIndex b else 3
def rootIndex (b : EnhancedBranch) : Fin 4 := if b.2.2 then 0 else upperIndex b

def branchCell (b : EnhancedBranch) : Set (Fin 2 → ℝ) := {x |
  (if b.1 then residualAffine 1 x ≤ residualAffine 2 x
    else residualAffine 2 x < residualAffine 1 x) ∧
  (if b.2.1 then residualAffine 3 x ≤ residualAffine (minIndex b) x
    else residualAffine (minIndex b) x < residualAffine 3 x) ∧
  (if b.2.2 then residualAffine (upperIndex b) x ≤ residualAffine 0 x
    else residualAffine 0 x < residualAffine (upperIndex b) x)}

def branchOf (x : Fin 2 → ℝ) : EnhancedBranch :=
  let b0 := decide (residualAffine 1 x ≤ residualAffine 2 x)
  let m : Fin 4 := if b0 then 1 else 2
  let b1 := decide (residualAffine 3 x ≤ residualAffine m x)
  let q : Fin 4 := if b1 then m else 3
  (b0, b1, decide (residualAffine q x ≤ residualAffine 0 x))

theorem mem_branchCell_iff (b : EnhancedBranch) (x : Fin 2 → ℝ) :
    x ∈ branchCell b ↔ branchOf x = b := by
  rcases b with ⟨b0, b1, b2⟩
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp only [branchCell, mem_setOf_eq, minIndex, upperIndex,
      Bool.false_eq_true, ↓reduceIte]
  all_goals
    constructor
    · rintro ⟨h0, h1, h2⟩
      simp_all [branchOf, not_le]
    · intro he
      unfold branchOf at he
      split_ifs at he <;> simp_all [not_le]

theorem branch_residual {b : EnhancedBranch} {x : Fin 2 → ℝ}
    (hx : x ∈ currentCube) (hb : x ∈ branchCell b) :
    residual x = residualAffine (rootIndex b) x := by
  rw [residual_eq_affine_circuit hx]
  rcases b with ⟨b0, b1, b2⟩
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp only [branchCell, mem_setOf_eq, minIndex, upperIndex, rootIndex,
      Bool.false_eq_true, ↓reduceIte] at hb ⊢ <;>
    rcases hb with ⟨h0, h1, h2⟩ <;>
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right,
      le_of_lt]

/-! Mixed affine tests, including empty strict cores at singleton walls. -/

def mixedRegion {r : ℕ} (L : Fin r → (Fin 2 → ℝ) →L[ℝ] ℝ)
    (c : Fin r → ℝ) (weak : Fin r → Bool) : Set (Fin 2 → ℝ) :=
  {x | ∀ j, if weak j then L j x ≤ c j else L j x < c j}

theorem measurableSet_mixedRegion {r : ℕ}
    (L : Fin r → (Fin 2 → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (weak : Fin r → Bool) :
    MeasurableSet (mixedRegion L c weak) := by
  simp only [mixedRegion, setOf_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : weak j = true
  · simp only [hj, ↓reduceIte]
    exact (isClosed_le (L j).continuous continuous_const).measurableSet
  · simp only [hj, ↓reduceIte]
    exact (isOpen_lt (L j).continuous continuous_const).measurableSet

theorem tendsto_prime_test_mixed {r : ℕ}
    (L : Fin r → (Fin 2 → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (weak : Fin r → Bool)
    (hL : ∀ j, L j ≠ 0) (f : (Fin 2 → ℝ) → ℝ) (hf : ContinuousOn f currentCube) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 2 => a) (fun _ => h)
      ((mixedRegion L c weak).indicator f)) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin 2 => a) (fun _ => h) ∩ mixedRegion L c weak,
        f x * ∏ i, 1 / x i)) := by
  apply tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num [a]) (by norm_num [a, h]) L c hL _
    (measurableSet_mixedRegion L c weak) ?_ ?_ f hf
  · intro x hx j
    by_cases hj : weak j = true
    · simpa only [hj, ↓reduceIte] using (hx j).le
    · simpa only [hj, ↓reduceIte] using hx j
  · intro x hx j
    by_cases hj : weak j = true
    · simpa only [hj, ↓reduceIte] using hx j
    · exact (by simpa only [hj, ↓reduceIte] using hx j : L j x < c j).le

def branchLeft (b : EnhancedBranch) : Fin 3 → Fin 4 := ![1, 3, upperIndex b]
def branchRight (b : EnhancedBranch) : Fin 3 → Fin 4 := ![2, minIndex b, 0]
def branchWeak (b : EnhancedBranch) : Fin 3 → Bool := ![b.1, b.2.1, b.2.2]

def branchForm (b : EnhancedBranch) (j : Fin 3) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  if branchWeak b j then residualSlope (branchLeft b j) - residualSlope (branchRight b j)
  else residualSlope (branchRight b j) - residualSlope (branchLeft b j)

def branchBound (b : EnhancedBranch) (j : Fin 3) : ℝ :=
  if branchWeak b j then residualOffset (branchRight b j) - residualOffset (branchLeft b j)
  else residualOffset (branchLeft b j) - residualOffset (branchRight b j)

theorem branchForm_ne_zero (b : EnhancedBranch) (j : Fin 3) : branchForm b j ≠ 0 := by
  have hij : branchLeft b j ≠ branchRight b j := by
    rcases b with ⟨b0, b1, b2⟩
    cases b0 <;> cases b1 <;> cases b2 <;> fin_cases j <;>
      norm_num [branchLeft, branchRight, minIndex, upperIndex]
  unfold branchForm
  split_ifs
  · exact residualSlope_sub_ne_zero hij
  · exact residualSlope_sub_ne_zero hij.symm

theorem mixed_branch_iff (b : EnhancedBranch) (x : Fin 2 → ℝ) :
    x ∈ mixedRegion (branchForm b) (branchBound b) (branchWeak b) ↔
      x ∈ branchCell b := by
  rcases b with ⟨b0, b1, b2⟩
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp [mixedRegion, branchCell, Fin.forall_fin_succ, branchForm, branchBound,
      branchWeak, branchLeft, branchRight, minIndex, upperIndex, residualAffine] <;>
    constructor <;> rintro ⟨h0, h1, h2⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- Four literal atom inequalities: [2,5], then the open interval or the
two opposing weak inequalities defining the exact lookup singleton. -/
def atomLower (b : FloorAtom) : ℝ :=
  match b with | .inl i => floorGrid i.val | .inr j => floorGrid j.val
def atomUpper (b : FloorAtom) : ℝ :=
  match b with | .inl i => floorGrid (i.val + 1) | .inr j => floorGrid j.val
def atomWeak : FloorAtom → Bool := fun b => match b with | .inl _ => false | .inr _ => true

def atomForms (q : Fin 4) : Fin 4 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ![-residualSlope q, residualSlope q, -residualSlope q, residualSlope q]
def atomBounds (q : Fin 4) (b : FloorAtom) : Fin 4 → ℝ :=
  ![residualOffset q - 2 * a, 5 * a - residualOffset q,
    residualOffset q - a * atomLower b, a * atomUpper b - residualOffset q]
def atomWeaks (b : FloorAtom) : Fin 4 → Bool := ![true, true, atomWeak b, atomWeak b]

theorem mixed_atom_iff (q : Fin 4) (b : FloorAtom) (x : Fin 2 → ℝ) :
    x ∈ mixedRegion (atomForms q) (atomBounds q b) (atomWeaks b) ↔
      residualAffine q x / a ∈ floorAtomSet b := by
  have ha : 0 < a := by norm_num [a]
  cases b with
  | inl i =>
    simp only [mixedRegion, Fin.forall_fin_succ, atomForms, atomBounds, atomWeaks,
      atomWeak, atomLower, atomUpper, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Bool.false_eq_true, ↓reduceIte, neg_apply,
      floorAtomSet, mem_inter_iff, mem_Icc, mem_Ioo, residualAffine,
      Fin.forall_fin_zero, and_true, and_assoc]
    rw [le_div_iff₀ ha, div_le_iff₀ ha, lt_div_iff₀ ha, div_lt_iff₀ ha]
    constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;>
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  | inr j =>
    simp only [mixedRegion, Fin.forall_fin_succ, atomForms, atomBounds, atomWeaks,
      atomWeak, atomLower, atomUpper, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, ↓reduceIte, neg_apply,
      floorAtomSet, mem_inter_iff, mem_Icc, mem_singleton_iff, residualAffine,
      Fin.forall_fin_zero, and_true]
    rw [le_div_iff₀ ha, div_le_iff₀ ha, div_eq_iff ha.ne']
    constructor
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

def pieceForms (b : EnhancedBranch) : Fin 8 → (Fin 2 → ℝ) →L[ℝ] ℝ :=
  Fin.append currentChenPairOrderForms (Fin.append (branchForm b) (atomForms (rootIndex b)))
def pieceBounds (b : EnhancedBranch) (k : FloorAtom) : Fin 8 → ℝ :=
  Fin.append (fun _ : Fin 1 => 0) (Fin.append (branchBound b) (atomBounds (rootIndex b) k))
def pieceWeaks (b : EnhancedBranch) (k : FloorAtom) : Fin 8 → Bool :=
  Fin.append (fun _ : Fin 1 => false) (Fin.append (branchWeak b) (atomWeaks k))
def affineFloorPiece (b : EnhancedBranch) (k : FloorAtom) : Set (Fin 2 → ℝ) :=
  mixedRegion (pieceForms b) (pieceBounds b k) (pieceWeaks b k)

theorem pieceForms_ne_zero (b : EnhancedBranch) : ∀ j, pieceForms b j ≠ 0 := by
  simp only [pieceForms, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  refine ⟨currentChenPairOrderForms_ne_zero, branchForm_ne_zero b, ?_⟩
  intro j
  fin_cases j <;> simp only [atomForms, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] <;>
    first | exact residualSlope_ne_zero _ | exact neg_ne_zero.mpr (residualSlope_ne_zero _)

theorem mem_affineFloorPiece_iff (b : EnhancedBranch) (k : FloorAtom) (x : Fin 2 → ℝ) :
    x ∈ affineFloorPiece b k ↔
      x 0 < x 1 ∧ x ∈ branchCell b ∧ residualAffine (rootIndex b) x / a ∈ floorAtomSet k := by
  change (∀ j, if pieceWeaks b k j then pieceForms b j x ≤ pieceBounds b k j
    else pieceForms b j x < pieceBounds b k j) ↔ _
  simp only [pieceWeaks, pieceForms, pieceBounds, Fin.forall_fin_add,
    Fin.append_left, Fin.append_right]
  change ((∀ j : Fin 1, currentChenPairOrderForms j x < 0) ∧
    x ∈ mixedRegion (branchForm b) (branchBound b) (branchWeak b) ∧
    x ∈ mixedRegion (atomForms (rootIndex b)) (atomBounds (rootIndex b) k) (atomWeaks k)) ↔ _
  rw [mixed_branch_iff, mixed_atom_iff]
  simp [currentChenPairOrderForms]

theorem affineFloorPiece_dictionary {x : Fin 2 → ℝ} (hx : x ∈ currentCube)
    (b : EnhancedBranch) (k : FloorAtom) :
    x ∈ affineFloorPiece b k ↔
      x 0 < x 1 ∧ x ∈ branchCell b ∧ x ∈ pulledFloorAtom k := by
  rw [mem_affineFloorPiece_iff]
  constructor
  · rintro ⟨ho, hb, hk⟩
    exact ⟨ho, hb, by simpa only [pulledFloorAtom, mem_preimage, argument,
      branch_residual hx hb] using hk⟩
  · rintro ⟨ho, hb, hk⟩
    exact ⟨ho, hb, by simpa only [pulledFloorAtom, mem_preimage, argument,
      branch_residual hx hb] using hk⟩

/-- Every actual one of the eight-times-401 pieces is in the pinned prime
test class. Neither a desired limit nor a prime-boundary estimate is a premise. -/
theorem tendsto_actual_affine_floor_piece (b : EnhancedBranch) (k : FloorAtom) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin 2 => a) (fun _ => h)
      ((affineFloorPiece b k).indicator harmonicCorrection)) atTop
      (𝓝 (∫ x in logPrimeBox (fun _ : Fin 2 => a) (fun _ => h) ∩ affineFloorPiece b k,
        harmonicCorrection x * ∏ i, 1 / x i)) := by
  exact tendsto_prime_test_mixed (pieceForms b) (pieceBounds b k) (pieceWeaks b k)
    (pieceForms_ne_zero b) harmonicCorrection continuousOn_harmonicCorrection_cube

/-- Exact branch partition at each point, before any prime or integral limit. -/
theorem sum_affineFloorPiece_indicator {x : Fin 2 → ℝ} (hx : x ∈ currentCube)
    (k : FloorAtom) (f : (Fin 2 → ℝ) → ℝ) :
    (∑ b : EnhancedBranch, (affineFloorPiece b k).indicator f x) =
      ((primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)) ∩
        pulledFloorAtom k).indicator f x := by
  let R := (primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)) ∩ pulledFloorAtom k
  calc
    _ = ∑ b : EnhancedBranch, if b = branchOf x then R.indicator f x else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      have hd := affineFloorPiece_dictionary hx b k
      rw [mem_branchCell_iff] at hd
      by_cases hb : b = branchOf x
      · subst b
        have hr : x ∈ affineFloorPiece (branchOf x) k ↔ x ∈ R := by
          simpa only [R, mem_inter_iff, mem_currentChenPairOrderRegion,
            eq_self_iff_true, true_and, and_true] using hd
        by_cases hR : x ∈ R
        · simp only [if_pos rfl, indicator_of_mem hR, indicator_of_mem (hr.mpr hR)]
        · simp only [if_pos rfl, indicator_of_notMem hR,
            indicator_of_notMem (mt hr.mp hR)]
      · have hp : x ∉ affineFloorPiece b k := by
          intro hp
          exact hb (hd.mp hp).2.1.symm
        simp only [if_neg hb, indicator_of_notMem hp]
    _ = _ := by simp

theorem sum_floor_piece_integrals (k : FloorAtom) :
    (∑ b : EnhancedBranch,
      ∫ x in logPrimeBox (fun _ : Fin 2 => a) (fun _ => h) ∩ affineFloorPiece b k,
        harmonicCorrection x * ∏ i, 1 / x i) =
      ∫ x in triangle ∩ pulledFloorAtom k, correctionWeight x := by
  let B := logPrimeBox (fun _ : Fin 2 => a) (fun _ => h)
  let W := fun x : Fin 2 → ℝ => harmonicCorrection x * ∏ i, 1 / x i
  have hi : IntegrableOn W B := integrableOn_logPrimeBox_test_cube
    (by norm_num [a]) harmonicCorrection continuousOn_harmonicCorrection_cube
  have hp (b : EnhancedBranch) : MeasurableSet (affineFloorPiece b k) :=
    measurableSet_mixedRegion _ _ _
  have hR : MeasurableSet ((primeAffineGateRegion currentChenPairOrderForms
      (fun _ => 0)) ∩ pulledFloorAtom k) :=
    (measurableSet_primeAffineGateRegion _ _).inter (measurableSet_pulledFloorAtom k)
  calc
    _ = ∑ b : EnhancedBranch, ∫ x in B, (affineFloorPiece b k).indicator W x := by
      apply Finset.sum_congr rfl
      intro b _
      exact (setIntegral_indicator (hp b)).symm
    _ = ∫ x in B, ∑ b : EnhancedBranch, (affineFloorPiece b k).indicator W x :=
      (integral_finsetSum _ (fun b _ => hi.indicator (hp b))).symm
    _ = ∫ x in B, ((primeAffineGateRegion currentChenPairOrderForms
        (fun _ => 0)) ∩ pulledFloorAtom k).indicator W x := by
      apply setIntegral_congr_fun (measurableSet_logPrimeBox _ _)
      intro x hx
      exact sum_affineFloorPiece_indicator (logPrimeBox_mem_closure hx) k W
    _ = _ := by
      rw [setIntegral_indicator hR]
      simp only [B, W, triangle, correctionWeight, harmonicCorrection, inter_assoc]

/-- The arithmetic value of the whole finite table, not just of open cells. -/
theorem floor_correction_finite_pieces (nums : Fin 200 → ℤ)
    {x : Fin 2 → ℝ} (hx : x ∈ currentCube) :
    (∑ k : FloorAtom, floorAtomValue nums k *
      ∑ b : EnhancedBranch, (affineFloorPiece b k).indicator harmonicCorrection x) =
      (primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)).indicator
        (fun x => floorStep nums (argument x) * harmonicCorrection x) x := by
  simp_rw [sum_affineFloorPiece_indicator hx]
  by_cases ho : x ∈ primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)
  · rw [indicator_of_mem ho]
    unfold floorStep
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : x ∈ pulledFloorAtom k
    · have hk' : argument x ∈ floorAtomSet k := hk
      simp only [indicator_of_mem (show x ∈ _ ∩ _ from ⟨ho, hk⟩),
        indicator_of_mem hk']
    · have hk' : argument x ∉ floorAtomSet k := hk
      simp only [indicator_of_notMem (show x ∉ _ ∩ _ from fun h => hk h.2),
        indicator_of_notMem hk', mul_zero, zero_mul]
  · rw [indicator_of_notMem ho]
    apply Finset.sum_eq_zero
    intro k _
    rw [indicator_of_notMem (show x ∉ _ ∩ _ from fun h => ho h.1), mul_zero]

theorem enhanced_kernel_finite_pieces (nums : Fin 200 → ℤ)
    {x : Fin 2 → ℝ} (hx : x ∈ currentCube) :
    (primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)).indicator
      (kernel (floorStep nums)) x =
      (primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)).indicator
        (kernel (fun _ => 0)) x +
      ∑ k : FloorAtom, floorAtomValue nums k *
        ∑ b : EnhancedBranch, (affineFloorPiece b k).indicator harmonicCorrection x := by
  rw [floor_correction_finite_pieces nums hx]
  by_cases ho : x ∈ primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)
  · simp only [indicator_of_mem ho]
    dsimp [kernel, harmonicCorrection]
    ring
  · simp only [indicator_of_notMem ho, add_zero]

private def primeTestLinear (N : ℕ) : ((Fin 2 → ℝ) → ℝ) →ₗ[ℝ] ℝ where
  toFun := actualPrimeBoxTestSum N (fun _ : Fin 2 => a) (fun _ => h)
  map_add' f g := by
    simp only [actualPrimeBoxTestSum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [actualPrimeBoxTestSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

theorem nativeEnhancedHarmonic_floor_finite_fubini (nums : Fin 200 → ℤ)
    {N : ℕ} (hN : 2 ≤ N) :
    nativeEnhancedHarmonic N (floorStep nums) = nativeEnhancedHarmonic N (fun _ => 0) +
      ∑ k : FloorAtom, floorAtomValue nums k *
        ∑ b : EnhancedBranch, actualPrimeBoxTestSum N (fun _ : Fin 2 => a) (fun _ => h)
          ((affineFloorPiece b k).indicator harmonicCorrection) := by
  have hN' : 1 < N := by omega
  have hd (corr : ℝ → ℝ) :=
    currentChenUpsilon5_harmonic_eq_actualPrimeBox hN (kernel corr)
  simp only [nativeEnhancedHarmonic, a, h] at ⊢
  rw [hd (floorStep nums), hd (fun _ => 0)]
  change primeTestLinear N
    ((primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)).indicator
      (kernel (floorStep nums))) = _
  calc
    _ = primeTestLinear N
        ((primeAffineGateRegion currentChenPairOrderForms (fun _ => 0)).indicator
          (kernel (fun _ => 0)) +
          ∑ k : FloorAtom, floorAtomValue nums k •
            ∑ b : EnhancedBranch, (affineFloorPiece b k).indicator harmonicCorrection) := by
      unfold primeTestLinear actualPrimeBoxTestSum
      apply Finset.sum_congr rfl
      intro p hp
      have hx := ((mem_actualPrimeBoxTuples_log_iff hN' _ _ p).mp hp).2
      congr 1
      simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        enhanced_kernel_finite_pieces nums (logPrimeBox_mem_closure hx)
    _ = _ := by
      simp only [map_add, map_sum, map_smul, smul_eq_mul]
      rfl

/-- Native original-selector prime harmonic convergence for EVERY finite
closed-cell array. In particular no continuity of the saved floor is assumed. -/
theorem tendsto_nativeEnhancedHarmonic_floor (nums : Fin 200 → ℤ) :
    Tendsto (fun N : ℕ => nativeEnhancedHarmonic N (floorStep nums)) atTop
      (𝓝 (integral (floorStep nums))) := by
  have hc := tendsto_finsetSum (Finset.univ : Finset FloorAtom) (fun k _ =>
    (tendsto_const_nhds (x := floorAtomValue nums k)).mul
      (tendsto_finsetSum (Finset.univ : Finset EnhancedBranch) (fun b _ =>
        tendsto_actual_affine_floor_piece b k)))
  have hh := (tendsto_nativeEnhancedHarmonic_continuous (fun _ => 0)
    continuousOn_const).add hc
  have hi : integral (floorStep nums) = integral (fun _ => 0) +
      ∑ k : FloorAtom, floorAtomValue nums k *
        ∑ b : EnhancedBranch,
          ∫ x in logPrimeBox (fun _ : Fin 2 => a) (fun _ => h) ∩ affineFloorPiece b k,
            harmonicCorrection x * ∏ i, 1 / x i := by
    rw [integral_floor_finite_fubini]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [sum_floor_piece_integrals]
  rw [hi]
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (nativeEnhancedHarmonic_floor_finite_fubini nums hN).symm

/-- The literal adopted h248 floor and the actual enhanced canonical integral. -/
theorem tendsto_nativeEnhancedHarmonic_adoptedH248 :
    Tendsto (fun N : ℕ => nativeEnhancedHarmonic N adoptedH248Floor) atTop
      (𝓝 (∫ x in triangle, canonicalKernel adoptedH248Floor x * ∏ i, 1 / x i)) := by
  rw [← integral_eq_canonical]
  exact tendsto_nativeEnhancedHarmonic_floor adoptedH248Numerators

end

end ImbalancedChen.Part5OriginalUpsilon5CausalDictionary
