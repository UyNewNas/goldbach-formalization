import ImbalancedChen.Part3Gamma0CuspMinimalWidth
import ImbalancedChen.Part3Gamma0CuspChartOverlap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The actual Gamma0(N) cusp-one deck element has integer horizontal powers in
the normalized chart. Its half-open high strip therefore gives disjoint
cells indexed by all integers, not just the immediate translate. These
cells partition the entire scaled high cusp neighborhood. The statements
below concern only this parabolic chart; no full Gamma0 orbit quotient,
quotient measure, or automorphic spectral measure is constructed.
-/

namespace ImbalancedChen.Part3.Gamma0CuspDeckPartition20261024zz

noncomputable section

open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane Pointwise
open P3ActualCuspScalingSourceOnly
open ImbalancedChen.Part3.Gamma0CuspMeasure20261024zz
open ImbalancedChen.Part3.Gamma0CuspMinimalWidth20261024zz
open ImbalancedChen.Part3.Gamma0CuspChartOverlap20261024zz

/-- Scalar extension of a power of the *actual* integral Gamma0 deck
matrix. This real action makes measurability and volume invariance explicit. -/
def deckRealPower (N : ℕ) (k : ℤ) : SL(2, ℝ) :=
  SpecialLinearGroup.map (algebraMap ℤ ℝ) ((cuspDeckSL N) ^ k)

theorem deckRealPower_smul_eq_actual (N : ℕ) (k : ℤ)
    (w : UpperHalfPlane) :
    deckRealPower N k • w = (cuspDeckSL N) ^ k • w := by
  rfl

/-- The kth measurable cell of the actual cusp-one deck action. -/
def deckCell (N : ℕ) (hN : 0 < (N : ℝ)) (k : ℤ) : Set UpperHalfPlane :=
  deckRealPower N k • scaledHighStrip N hN

theorem mem_deckCell_iff (N : ℕ) (hN : 0 < (N : ℝ))
    (k : ℤ) (u : UpperHalfPlane) :
    u ∈ deckCell N hN k ↔
      ∃ w ∈ highStripIco,
        u = newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w) := by
  constructor
  · intro hu
    change u ∈ (fun v : UpperHalfPlane => deckRealPower N k • v) ''
      scaledHighStrip N hN at hu
    obtain ⟨v, hv, rfl⟩ := hu
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨w, hw, ?_⟩
    rw [deckRealPower_smul_eq_actual]
    exact cuspDeck_zpow_scaled_action N hN k w
  · rintro ⟨w, hw, rfl⟩
    change newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w) ∈
      (fun v : UpperHalfPlane => deckRealPower N k • v) ''
        scaledHighStrip N hN
    refine ⟨newSL (N : ℝ) hN • w, ⟨w, hw, rfl⟩, ?_⟩
    rw [deckRealPower_smul_eq_actual]
    exact cuspDeck_zpow_scaled_action N hN k w

theorem deckCell_measurable (N : ℕ) (hN : 0 < (N : ℝ)) (k : ℤ) :
    MeasurableSet (deckCell N hN k) := by
  unfold deckCell
  exact (scaledHighStrip_measurable N hN).const_smul _

theorem deckCell_measure (N : ℕ) (hN : 0 < (N : ℝ)) (k : ℤ) :
    (volume : Measure UpperHalfPlane) (deckCell N hN k) =
      (volume : Measure UpperHalfPlane) highStripIco := by
  calc
    (volume : Measure UpperHalfPlane) (deckCell N hN k) =
        (volume : Measure UpperHalfPlane) (scaledHighStrip N hN) := by
      exact measure_smul (volume : Measure UpperHalfPlane)
        (deckRealPower N k) (scaledHighStrip N hN)
    _ = (volume : Measure UpperHalfPlane) highStripIco :=
      scaledHighStrip_measure N hN

/-- Different integer deck powers give disjoint half-open cells. The proof
uses uniqueness of the integer representative in the recovery source. -/
theorem deckCell_disjoint_of_ne (N : ℕ) (hN : 0 < (N : ℝ))
    {j k : ℤ} (hjk : j ≠ k) :
    Disjoint (deckCell N hN j) (deckCell N hN k) := by
  apply Set.disjoint_left.mpr
  intro u huj huk
  obtain ⟨w, hw, huj⟩ := (mem_deckCell_iff N hN j u).mp huj
  obtain ⟨v, hv, huk⟩ := (mem_deckCell_iff N hN k u).mp huk
  have hscaled : newSL (N : ℝ) hN • ((j : ℝ) +ᵥ w) =
      newSL (N : ℝ) hN • ((k : ℝ) +ᵥ v) := huj.symm.trans huk
  have hcoord : (j : ℝ) +ᵥ w = (k : ℝ) +ᵥ v := by
    have h := congrArg
      (fun t : UpperHalfPlane => (newSL (N : ℝ) hN)⁻¹ • t) hscaled
    simpa only [← smul_smul, inv_mul_cancel, one_smul] using h
  have hjmem : (((j : ℝ) +ᵥ w).re - (j : ℝ)) ∈
      Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
    simpa only [UpperHalfPlane.vadd_re, add_sub_cancel_left] using hw.1
  have hkmem : (((j : ℝ) +ᵥ w).re - (k : ℝ)) ∈
      Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
    rw [hcoord]
    simpa only [UpperHalfPlane.vadd_re, add_sub_cancel_left] using hv.1
  obtain ⟨q, _hq, hunique⟩ :=
    highStripIco_unique_horizontal_period ((j : ℝ) +ᵥ w)
  exact hjk ((hunique j hjmem).trans (hunique k hkmem).symm)

/-- The full high cusp region in the same scaled coordinate. -/
def scaledHighCusp (N : ℕ) (hN : 0 < (N : ℝ)) : Set UpperHalfPlane :=
  newSL (N : ℝ) hN • {w : UpperHalfPlane | 1 ≤ w.im}

/-- Every high cusp point has exactly one integer horizontal
representative in the half-open cell. -/
theorem scaledHighCusp_eq_iUnion_deckCell (N : ℕ)
    (hN : 0 < (N : ℝ)) :
    scaledHighCusp N hN = ⋃ k : ℤ, deckCell N hN k := by
  ext u
  constructor
  · intro hu
    change u ∈ (fun w : UpperHalfPlane => newSL (N : ℝ) hN • w) ''
      {w : UpperHalfPlane | 1 ≤ w.im} at hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨k, hk, _⟩ := highStripIco_unique_horizontal_period w
    let v : UpperHalfPlane := (-(k : ℝ)) +ᵥ w
    have hv : v ∈ highStripIco := by
      constructor
      · simpa only [v, UpperHalfPlane.vadd_re, neg_add_eq_sub] using hk
      · simpa only [v, UpperHalfPlane.vadd_im] using hw
    have hrecover : (k : ℝ) +ᵥ v = w := by
      dsimp [v]
      rw [← add_vadd]
      simp
    apply Set.mem_iUnion.mpr
    refine ⟨k, (mem_deckCell_iff N hN k _).mpr ?_⟩
    exact ⟨v, hv, by rw [hrecover]⟩
  · intro hu
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hu
    obtain ⟨w, hw, rfl⟩ := (mem_deckCell_iff N hN k u).mp hk
    change newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w) ∈
      (fun v : UpperHalfPlane => newSL (N : ℝ) hN • v) ''
        {v : UpperHalfPlane | 1 ≤ v.im}
    refine ⟨(k : ℝ) +ᵥ w, ?_, rfl⟩
    simpa only [UpperHalfPlane.vadd_im] using hw.2

/-- The countable high-cusp cell union is measurable. -/
theorem scaledHighCusp_measurable (N : ℕ) (hN : 0 < (N : ℝ)) :
    MeasurableSet (scaledHighCusp N hN) := by
  rw [scaledHighCusp_eq_iUnion_deckCell]
  exact MeasurableSet.iUnion (fun k => deckCell_measurable N hN k)

theorem scaledHighCusp_unique_deckCell (N : ℕ)
    (hN : 0 < (N : ℝ)) {u : UpperHalfPlane}
    (hu : u ∈ scaledHighCusp N hN) :
    ∃! k : ℤ, u ∈ deckCell N hN k := by
  rw [scaledHighCusp_eq_iUnion_deckCell] at hu
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hu
  refine ⟨k, hk, ?_⟩
  intro j hj
  by_contra hne
  exact (Set.disjoint_left.mp (deckCell_disjoint_of_ne N hN hne)) hj hk

/-- Finite unions of these genuine deck cells have additive hyperbolic
volume, with no quotient-measure interpretation. -/
theorem deckCells_finset_measure (N : ℕ) (hN : 0 < (N : ℝ))
    (s : Finset ℤ) :
    (volume : Measure UpperHalfPlane) (⋃ k ∈ s, deckCell N hN k) =
      (s.card : ℝ≥0∞) *
        (volume : Measure UpperHalfPlane) highStripIco := by
  have hpair : PairwiseDisjoint (↑s : Set ℤ) (deckCell N hN) := by
    intro j _hj k _hk hjk
    exact deckCell_disjoint_of_ne N hN hjk
  calc
    (volume : Measure UpperHalfPlane) (⋃ k ∈ s, deckCell N hN k) =
        ∑ k ∈ s, (volume : Measure UpperHalfPlane) (deckCell N hN k) := by
      exact measure_biUnion_finset hpair
        (fun k _hk => deckCell_measurable N hN k)
    _ = ∑ _k ∈ s, (volume : Measure UpperHalfPlane) highStripIco := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact deckCell_measure N hN k
    _ = (s.card : ℝ≥0∞) *
          (volume : Measure UpperHalfPlane) highStripIco := by
      simp [Finset.sum_const, nsmul_eq_mul]

end

end ImbalancedChen.Part3.Gamma0CuspDeckPartition20261024zz
