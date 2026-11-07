import ImbalancedChen.P5U6AdoptedEnhancedHarmonic
import ImbalancedChen.P5U6RetainedExplicitBuffer

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Closed-cell soundness, including the adjacent-minimum values at all knots,
is transferred to the literal original U6 R-denominator harmonic sum.
The original h248 cell inequalities remain primitive, OPEN inputs: this file
does not prove original-family seed/W1/W2 soundness or the copied-bank endpoint
license. In particular, an independent source lower bound cannot license a
larger copied-bank number. No physical sieve/count lower bound is assumed or
concluded. The final result concerns the actual retained harmonic main only.
-/

namespace ImbalancedChen.P5U6OriginalH248ClosedCellLicenseSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
open Part5OriginalUpsilon5CausalDictionary
open P5U6AdoptedH248BindingSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly
open P5U6RetainedExplicitBufferSourceOnly
open P5U6SteppedPrimeAdmissibilitySourceOnly
open P5U6AdoptedEnhancedHarmonicSourceOnly

abbrev Point := Fin 2 → ℝ

/-- The original lower correction is zero below 2 and outside the saved
support. This definition makes that convention explicit. -/
def supportedLower (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ∈ Icc (2 : ℝ) 5 then h s else 0

/-- These are scalar, original CLOSED-cell inequalities, not an assumed U6
integral or prime-pair limit. Their production from the original recurrence
is OPEN, including the k50 left endpoint 101/50 noted in the source review. -/
def OriginalClosedCellBounds (h : ℝ → ℝ) : Prop :=
  ∀ (i : Fin 200) (s : ℝ), s ∈ Icc (2 : ℝ) 5 →
    s ∈ Icc (floorGrid i.val) (floorGrid (i.val + 1)) →
      floorValue adoptedH248Numerators i ≤ h s

private theorem grid_mono {m n : ℕ} (hmn : m ≤ n) : floorGrid m ≤ floorGrid n := by
  unfold floorGrid
  exact add_le_add_left
    (div_le_div_of_nonneg_right (by exact_mod_cast hmn) (by norm_num)) _

/-- Every active atom is licensed by an original closed grid cell.
At an interior knot the minimum is bounded by the RIGHT closed cell;
at the final knot the last closed cell is used. No knot is deleted. -/
theorem atomValue_le_of_originalClosedCells {h : ℝ → ℝ}
    (hcells : OriginalClosedCellBounds h) {b : FloorAtom} {s : ℝ}
    (hb : s ∈ floorAtomSet b) : floorAtomValue adoptedH248Numerators b ≤ h s := by
  cases b with
  | inl i =>
    exact hcells i s hb.1 ⟨hb.2.1.le, hb.2.2.le⟩
  | inr j =>
    have hs : s = floorGrid j.val := hb.2
    change floorKnotValue adoptedH248Numerators j ≤ h s
    unfold floorKnotValue
    split_ifs with hzero hlast
    · apply hcells 0 s hb.1
      rw [hs, hzero]
      exact ⟨le_rfl, grid_mono (by omega)⟩
    · apply hcells 199 s hb.1
      rw [hs, hlast]
      exact ⟨grid_mono (by omega), le_rfl⟩
    · let i : Fin 200 := ⟨j.val, by omega⟩
      apply (min_le_right _ _).trans
      apply hcells i s hb.1
      change floorGrid j.val ≤ s ∧ s ≤ floorGrid (j.val + 1)
      rw [hs]
      exact ⟨le_rfl, grid_mono (by omega)⟩

/-- Original cell inequalities and scalar nonnegativity imply the literal
adopted floor inequality, using uniqueness of atoms rather than summing
401 upper bounds. This also proves the zero-outside-support convention. -/
theorem adoptedFloor_le_supportedLower {h : ℝ → ℝ}
    (hcells : OriginalClosedCellBounds h)
    (hnonneg : ∀ s ∈ Icc (2 : ℝ) 5, 0 ≤ h s) (s : ℝ) :
    adoptedH248Floor s ≤ supportedLower h s := by
  by_cases hs : s ∈ Icc (2 : ℝ) 5
  · rw [supportedLower, if_pos hs]
    by_cases hex : ∃ b : FloorAtom, s ∈ floorAtomSet b
    · obtain ⟨b, hb⟩ := hex
      have heq : adoptedH248Floor s = floorAtomValue adoptedH248Numerators b := by
        unfold adoptedH248Floor floorStep
        calc
          _ = (floorAtomSet b).indicator (fun _ => floorAtomValue adoptedH248Numerators b) s :=
            Finset.sum_eq_single b
              (fun c _ hcb => indicator_of_notMem
                (fun hc => hcb (floorAtom_unique hc hb)) _)
              (by simp)
          _ = _ := indicator_of_mem hb _
      rw [heq]
      exact atomValue_le_of_originalClosedCells hcells hb
    · have hz : adoptedH248Floor s = 0 := by
        unfold adoptedH248Floor floorStep
        apply Finset.sum_eq_zero
        intro b _
        exact indicator_of_notMem (fun hb => hex ⟨b, hb⟩) _
      rw [hz]
      exact hnonneg s hs
  · rw [supportedLower, if_neg hs]
    exact le_of_eq (floorStep_outside adoptedH248Numerators hs)

def semanticTest (h : ℝ → ℝ) (x : Point) : ℝ :=
  currentChenUpsilon6OrdinaryClippedTest x +
    supportedLower h (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x

/-- The scalar correction uses R=1/2-u-v throughout, with no a-denominator
replacement. Multiplication by harmonic density 1/(uv) gives 4h/(Ruv). -/
theorem semanticTest_eq_original {h : ℝ → ℝ} {x : Point}
    (hx : x ∈ currentChenUpsilon6LogRectangle) :
    semanticTest h x =
      4 * (Real.log (currentChenUpsilon6OrdinaryProfile x - 1) +
        supportedLower h (currentChenUpsilon6OrdinaryProfile x)) / originalResidual x := by
  rw [semanticTest, currentChenUpsilon6OrdinaryClippedTest_eq hx]
  unfold currentChenUpsilon6OrdinaryFactor bareCorrection
  rw [originalResidual_eq_a_mul_profile]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def retainedSemanticPairSum {m : ℕ} (h : ℝ → ℝ) (N : ℕ) (eta : ℝ)
    (l r : Fin m → Fin 2 → ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta,
    ({x : Point | x ∉ boxMask l r}).indicator (semanticTest h)
      (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)

/-- A comparison of literal finite prime sums, retaining every arithmetic
knot and the very same finite mask. No asymptotic lower supplier occurs. -/
theorem nativeRetained_le_semantic {m N : ℕ} (hN : 2 ≤ N)
    {h : ℝ → ℝ} (hcells : OriginalClosedCellBounds h)
    (hnonneg : ∀ s ∈ Icc (2 : ℝ) 5, 0 ≤ h s)
    {eta : ℝ} (heta : 0 ≤ eta) (l r : Fin m → Fin 2 → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (box (l i) (r i)) (box (l j) (r j)))) :
    nativeRetainedBoxFamily N eta l r ≤ retainedSemanticPairSum h N eta l r := by
  rw [nativeRetainedBoxFamily_eq_pair_sum hN eta l r hdis]
  unfold retainedSemanticPairSum
  apply Finset.sum_le_sum
  intro t ht
  have hcoords : currentChenUpsilon6LogCoordinates N t = actualPrimeTupleLog N ![t.1, t.2] := by
    funext i
    fin_cases i <;> rfl
  have hx := ((mem_currentChenUpsilon6OrdinarySelector_log_iff hN eta t).mp ht).2.2
  rw [hcoords] at hx
  have hdom : actualPrimeTupleLog N ![t.1, t.2] ∈ currentChenUpsilon6LogDomain eta :=
    ⟨hx.1, hx.2.2.le⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hm : actualPrimeTupleLog N ![t.1, t.2] ∈ boxMask l r
  · rw [indicator_of_notMem (not_not.mpr hm), indicator_of_notMem (not_not.mpr hm)]
  · rw [indicator_of_mem hm, indicator_of_mem hm]
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_right (adoptedFloor_le_supportedLower hcells hnonneg _)
    unfold bareCorrection
    exact div_nonneg (by norm_num)
      (le_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 * (417 / 5000 : ℝ))
        (originalResidual_ge_two_a heta hdom)))

/-- The actual retained harmonic main, with one explicit buffer fixed
BEFORE N, is eventually within epsilon below the unbuffered adopted retained
integral. The original scalar closed-cell inequalities remain OPEN inputs;
this is not a physical Y6 count bound and claims no original table license. -/
theorem eventually_retainedSemanticPairSum_lower {m : ℕ} {h : ℝ → ℝ}
    (hcells : OriginalClosedCellBounds h)
    (hnonneg : ∀ s ∈ Icc (2 : ℝ) 5, 0 ≤ h s)
    (l r : Fin m → Fin 2 → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (box (l i) (r i)) (box (l j) (r j))))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      retainedEstimatorIntegral (fun x => x ∈ boxMask l r) 0 - epsilon <
        retainedSemanticPairSum h N (epsilon / 1008) l r := by
  have heta : 0 ≤ epsilon / 1008 := by positivity
  have hbuffer := retained_loss_le_tolerance (fun x => x ∈ boxMask l r)
    (measurableSet_boxMask l r) (epsilon := epsilon / 2) heta
    (by linarith : epsilon / 1008 ≤ (epsilon / 2) / 504)
  have hbuffer' := (le_abs_self _).trans hbuffer
  have hlim := tendsto_nativeRetainedBoxFamily (epsilon / 1008) heta l r hdis
  have hnear := hlim.eventually_const_lt
    (show retainedEstimatorIntegral (fun x => x ∈ boxMask l r) (epsilon / 1008) -
      epsilon / 2 < retainedEstimatorIntegral (fun x => x ∈ boxMask l r) (epsilon / 1008) by linarith)
  filter_upwards [hnear, eventually_ge_atTop (2 : ℕ)] with N hnearN hN
  have hcompare := nativeRetained_le_semantic hN hcells hnonneg heta l r hdis
  linarith

end

end ImbalancedChen.P5U6OriginalH248ClosedCellLicenseSourceOnly
