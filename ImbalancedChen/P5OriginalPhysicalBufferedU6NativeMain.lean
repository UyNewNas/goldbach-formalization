import ImbalancedChen.P5U6OriginalPairedMaskNativeHarmonic
import ImbalancedChen.P5U6UniformMovingMaskBuffer

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Literal PHYSICAL original U6 product buffer with product<=N^(833/2500-eta)
and the same actual paired-v2 deletion mask. The existing ordinary harmonic
supplier has STRICT product and horizontal gates. They are not declared
equal: the closed physical main is exactly the strict main PLUS its
literal arithmetic boundary sum. Nonnegativity, not a null-set deletion,
allows the strict main to supply the physical lower bound.
The fixed eta is chosen before N using the genuine uniform mask-buffer
loss and the already proved actual-mask native harmonic limit.
-/
namespace ImbalancedChen.P5OriginalPhysicalBufferedU6NativeMainSourceOnly

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open P5Z.U1011OriginalPairedRowPrimeTests
open P5Z.U1011OriginalPairedFixedMaskHarmonic (outerUnion)
open P5U6OriginalPairedMaskNativeHarmonicSourceOnly
open P5U6UniformMovingMaskBufferSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly

def closedSelector (S : Finset Row) (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  currentChenUpsilon6RetainedSelector N (nativeMask (outerUnion S) N) eta

def strictSelector (S : Finset Row) (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  (currentChenUpsilon6OrdinarySelector N eta).filter
    (fun p => ¬nativeMask (outerUnion S) N p)

def StrictInterior (N : ℕ) (eta : ℝ) (p : ℕ × ℕ) : Prop :=
  (N : ℝ) ^ (19 / 125 : ℝ) < (p.2 : ℝ) ∧
    ((p.1 * p.2 : ℕ) : ℝ) < (N : ℝ) ^ ((833 / 2500 : ℝ) - eta)

/-- Both original prime/centre exclusions and all weak physical walls
are retained by this exact dictionary, supplied from their actual source. -/
theorem mem_closedSelector_log {N : ℕ} (hN : 2 ≤ N) (S : Finset Row)
    (eta : ℝ) (p : ℕ × ℕ) :
    p ∈ closedSelector S N eta ↔
      p.1 ∈ chenAdditivePrimeCarrier N ∧ p.2 ∈ chenAdditivePrimeCarrier N ∧
      ¬nativeMask (outerUnion S) N p ∧
      currentChenUpsilon6LogCoordinates N p ∈ currentChenUpsilon6LogDomain eta := by
  exact mem_currentChenUpsilon6RetainedSelector_log_iff
    (by exact_mod_cast (show 1 < N by omega)) _ eta p

theorem closedSelector_physical_product (S : Finset Row) (N : ℕ) (eta : ℝ)
    {p : ℕ × ℕ} (hp : p ∈ closedSelector S N eta) :
    ((p.1 * p.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ ((833 / 2500 : ℝ) - eta) := by
  have h := (Finset.mem_filter.mp hp).2
  convert h using 1 <;> norm_num

/-- Exact strict-core identity. It does not erase either arithmetic wall. -/
theorem strictSelector_eq_closed_filter (S : Finset Row) (N : ℕ) (eta : ℝ) :
    strictSelector S N eta = (closedSelector S N eta).filter (StrictInterior N eta) := by
  ext p
  simp only [strictSelector, closedSelector, currentChenUpsilon6OrdinarySelector,
    currentChenUpsilon6RetainedSelector, StrictInterior, Finset.mem_filter,
    not_false_eq_true]
  tauto

theorem strictSelector_subset_closed (S : Finset Row) (N : ℕ) (eta : ℝ) :
    strictSelector S N eta ⊆ closedSelector S N eta := by
  rw [strictSelector_eq_closed_filter]
  exact Finset.filter_subset _ _

def boundarySelector (S : Finset Row) (N : ℕ) (eta : ℝ) : Finset (ℕ × ℕ) :=
  closedSelector S N eta \ strictSelector S N eta

/-- Every boundary label lies on one of the two ACTUAL retained walls.
It remains an arithmetic fibre, even though its real analogue is null. -/
theorem boundarySelector_wall (S : Finset Row) (N : ℕ) (eta : ℝ)
    {p : ℕ × ℕ} (hp : p ∈ boundarySelector S N eta) :
    (p.2 : ℝ) = (N : ℝ) ^ (19 / 125 : ℝ) ∨
      ((p.1 * p.2 : ℕ) : ℝ) = (N : ℝ) ^ ((833 / 2500 : ℝ) - eta) := by
  obtain ⟨hc, hn⟩ := Finset.mem_sdiff.mp hp
  have hprod := closedSelector_physical_product S N eta hc
  have hbase := (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  have hbands := (Finset.mem_filter.mp hbase).2
  have hhorizontal : (N : ℝ) ^ (19 / 125 : ℝ) ≤ (p.2 : ℝ) := hbands.2.2.1
  have hnot : ¬StrictInterior N eta p := by
    intro h
    exact hn (by rw [strictSelector_eq_closed_filter]; exact Finset.mem_filter.mpr ⟨hc, h⟩)
  by_cases hh : (N : ℝ) ^ (19 / 125 : ℝ) < (p.2 : ℝ)
  · right
    apply le_antisymm hprod
    by_contra hnprod
    exact hnot ⟨hh, lt_of_not_ge hnprod⟩
  · exact Or.inl (le_antisymm (le_of_not_gt hh) hhorizontal)

def closedMain (S : Finset Row) (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ p ∈ closedSelector S N eta, pairWeight N p

def boundaryMain (S : Finset Row) (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ p ∈ boundarySelector S N eta, pairWeight N p

/-- The b691 strict main attaches EXACTLY to db27's true adopted-mask
native numerator. Total real division also preserves the masked zeros. -/
theorem strictMain_eq_nativeU6 (S : Finset Row) (N : ℕ) (eta : ℝ) :
    maskedMain N (nativeMask (outerUnion S) N) eta = nativeU6 S eta N := by
  unfold maskedMain nativeU6 pairWeight adoptedTest enhancedFactor
  apply Finset.sum_congr rfl
  intro p _
  by_cases hm : nativeMask (outerUnion S) N p <;> simp [hm]

/-- Exact CLOSED physical main: strict b691 main PLUS literal boundaries. -/
theorem closedMain_eq_strict_add_boundary (S : Finset Row) (N : ℕ) (eta : ℝ) :
    closedMain S N eta = maskedMain N (nativeMask (outerUnion S) N) eta +
      boundaryMain S N eta := by
  have hs := Finset.sum_sdiff (f := pairWeight N) (strictSelector_subset_closed S N eta)
  have hstrict := maskedMain_eq_filtered N (nativeMask (outerUnion S) N) eta
  change maskedMain N (nativeMask (outerUnion S) N) eta =
    ∑ p ∈ strictSelector S N eta, pairWeight N p at hstrict
  rw [hstrict]
  change (∑ p ∈ closedSelector S N eta, pairWeight N p) =
    (∑ p ∈ strictSelector S N eta, pairWeight N p) +
      ∑ p ∈ closedSelector S N eta \ strictSelector S N eta, pairWeight N p
  linarith only [hs]

theorem closedPairWeight_nonneg {N : ℕ} (hN : 2 ≤ N) (S : Finset Row)
    {eta : ℝ} (heta : 0 ≤ eta) {p : ℕ × ℕ} (hp : p ∈ closedSelector S N eta) :
    0 ≤ pairWeight N p := by
  have hd := ((mem_closedSelector_log hN S eta p).1 hp).2.2.2
  have hcoords : currentChenUpsilon6LogCoordinates N p = actualPrimeTupleLog N ![p.1, p.2] := by
    funext i
    fin_cases i <;> rfl
  have hd0 : actualPrimeTupleLog N ![p.1, p.2] ∈ currentChenUpsilon6LogDomain 0 := by
    rw [← hcoords]
    refine ⟨hd.1, ?_⟩
    have hg := hd.2
    change currentChenUpsilon6LogCoordinates N p 0 + currentChenUpsilon6LogCoordinates N p 1 ≤
      (833 / 2500 : ℝ) - 0
    linarith
  exact div_nonneg (adoptedTest_nonneg hd0) (Nat.cast_nonneg _)

theorem closedMain_ge_strict {N : ℕ} (hN : 2 ≤ N) (S : Finset Row)
    {eta : ℝ} (heta : 0 ≤ eta) :
    maskedMain N (nativeMask (outerUnion S) N) eta ≤ closedMain S N eta := by
  rw [closedMain_eq_strict_add_boundary]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro p hp
  exact closedPairWeight_nonneg hN S heta (Finset.mem_sdiff.mp hp).1

/-- One POSITIVE FIXED eta precedes N. This is a lower bound for the
literal closed physical harmonic main, with no hBuffer/hMaskMean premise. -/
theorem exists_fixed_buffered_physical_lower (S : Finset Row) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ N : ℕ in atTop,
      retainedEstimatorIntegral (fun x => x ∈ ascendingPointMask S) 0 - epsilon ≤
        closedMain S N eta := by
  let tol := epsilon / 2
  have htol : 0 < tol := by dsimp [tol]; positivity
  let eta := tol / 1008
  have heta : 0 < eta := div_pos htol (by norm_num)
  refine ⟨eta, heta, ?_⟩
  have hnear := (tendsto_nativeU6 S 0 (by norm_num)).eventually
    (lt_mem_nhds (sub_lt_self _ htol))
  filter_upwards [hnear, eventually_uniform_masked_buffer_loss htol,
    eventually_ge_atTop (2 : ℕ)] with N hnearN hlossN hN
  have hloss := hlossN (nativeMask (outerUnion S) N)
  have hdiff := (le_abs_self _).trans_lt hloss
  rw [strictMain_eq_nativeU6 S N 0] at hdiff
  have hclosed := closedMain_ge_strict hN S heta.le
  change maskedMain N (nativeMask (outerUnion S) N) (tol / 1008) ≤ closedMain S N eta at hclosed
  dsimp only [tol] at hnearN hdiff hclosed
  linarith

end
end ImbalancedChen.P5OriginalPhysicalBufferedU6NativeMainSourceOnly
