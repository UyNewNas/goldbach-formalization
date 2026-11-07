import ImbalancedChen.P1HistoricalUpperFourthJointGeometry
import ImbalancedChen.AffinePrimeWallReserve

/-!
# P1: the actual rank-four arithmetic reserve next to the PLUS wall

This source-only module keeps the actual admitted tuples of the historical
third-capped upper policy.  Their old fourth level is read on the SAME
fourth mesh owner.  The strip is literally

  0 < old4 j - (sum i, t i) - t 3 <= delta.

The finite dictionary is an equality before any estimate.  The actual
weight is the original product of 1 / (p_i - 1), and the public majorant
is the closed strip of the proved nonzero form t0+t1+t2+2*t3.

`exists_actualPrimeAffineWallStrip_mass_lt` supplies the arithmetic limit;
no residual mean, prime-wall-nullity premise, or replacement carrier is
assumed.  A finite family receives one width before one common threshold.

Sibling source-only import to install on integration:
  ImbalancedChen.P1HistoricalUpperFourthJointGeometry.
This file has not been compiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set

namespace P1HistoricalFourthArithmeticWallStrip

/-- This is the PLUS s=1 wall, not the rank-four own-cube form. -/
def plusWallForm : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1 +
    ContinuousLinearMap.proj 2 + (2 : ℝ) • ContinuousLinearMap.proj 3

theorem plusWallForm_apply (t : Fin 4 → ℝ) :
    plusWallForm t = t 0 + t 1 + t 2 + 2 * t 3 := by
  simp [plusWallForm]

theorem plusWallForm_eq_sum_add_last (t : Fin 4 → ℝ) :
    plusWallForm t = (∑ i, t i) + t 3 := by
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [plusWallForm_apply]
  rw [hsum]
  ring

theorem plusWallForm_ne_zero : plusWallForm ≠ 0 := by
  intro h
  have hh := congrArg (fun F : (Fin 4 → ℝ) →L[ℝ] ℝ => F (fun _ => 1)) h
  norm_num [plusWallForm] at hh

/-- The public supplier takes a finite family; here it has one wall. -/
def publicWallForms : Fin 1 → (Fin 4 → ℝ) →L[ℝ] ℝ := fun _ => plusWallForm

def publicWallBounds (lambda : ℝ) : Fin 1 → ℝ := fun _ => lambda

theorem publicWallForms_ne_zero : ∀ i, publicWallForms i ≠ 0 := by
  intro i
  exact plusWallForm_ne_zero

/-- The open interior and the closed outer edge are both retained. -/
def inOldWallStrip (lambda delta : ℝ) (t : Fin 4 → ℝ) : Prop :=
  0 < lambda - (∑ i, t i) - t 3 ∧
    lambda - (∑ i, t i) - t 3 ≤ delta

/-- The literal gap strip is precisely the right-hand neighborhood of s=1;
its thickness in s is delta/t3, so no normalization factor is lost. -/
theorem inOldWallStrip_iff_ratio_strip (lambda delta : ℝ) (t : Fin 4 → ℝ)
    (ht : 0 < t 3) :
    inOldWallStrip lambda delta t ↔
      1 < (lambda - ∑ i, t i) / t 3 ∧
        (lambda - ∑ i, t i) / t 3 ≤ 1 + delta / t 3 := by
  have hlow : 0 < lambda - (∑ i, t i) - t 3 ↔
      1 < (lambda - ∑ i, t i) / t 3 := by
    rw [one_lt_div ht]
    constructor <;> intro h <;> linarith
  have hupp : lambda - (∑ i, t i) - t 3 ≤ delta ↔
      (lambda - ∑ i, t i) / t 3 ≤ 1 + delta / t 3 := by
    rw [div_le_iff₀ ht]
    have hcancel := div_mul_cancel₀ delta ht.ne'
    constructor <;> intro h <;> nlinarith
  exact and_congr hlow hupp

theorem inOldWallStrip_mono {lambda delta delta' : ℝ} {t : Fin 4 → ℝ}
    (hdelta : delta ≤ delta') (ht : inOldWallStrip lambda delta t) :
    inOldWallStrip lambda delta' t := by
  exact ⟨ht.1, ht.2.trans hdelta⟩

/-- A one-sided actual strip lies inside the public closed affine strip. -/
theorem inOldWallStrip_mem_public {lambda delta : ℝ} {t : Fin 4 → ℝ}
    (ht : inOldWallStrip lambda delta t) :
    t ∈ primeAffineWallStrip publicWallForms (publicWallBounds lambda) delta := by
  refine ⟨0, ?_⟩
  change |plusWallForm t - lambda| ≤ delta
  rw [plusWallForm_eq_sum_add_last, abs_of_nonpos (by linarith [ht.1])]
  linarith [ht.2]

/-- Literal admitted rank-four tuples, restricted to one common T3 owner. -/
def admittedWallTuples (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : Finset (Fin 4 → ℕ) :=
  (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter fun p =>
      actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
        inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p)

/-- No weight is replaced by a continuous density in this definition. -/
def admittedWallMass (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : ℝ :=
  ∑ p ∈ admittedWallTuples D N cap j delta, ∏ i, 1 / ((p i : ℝ) - 1)

/-- Exact rearrangement onto the public cube retains target deletion,
strict ordering, both original T3 parent gates, and half-open ownership. -/
theorem admittedWallTuples_eq_cube_filter
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    admittedWallTuples D N cap j delta =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter (fun p =>
          actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
              primeAffineGateRegion HistoricalPrefixCapData.p1_fourthParentGateForms
                (D.p1_fourthParentGateBounds j) ∧
          inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p)) := by
  have hdict := p1_historicalUpperFourthAdmittedTuples_cell_filter
    D hab hcheck N cap hN hcap j
  ext p
  constructor
  · intro hp
    obtain ⟨ha, ht, hs⟩ := Finset.mem_filter.mp hp
    have hc : p ∈ (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
          (fun q => actualPrimeTupleLog N q ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :=
      Finset.mem_filter.mpr ⟨ha, ht⟩
    rw [hdict] at hc
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2, hs⟩
  · intro hp
    obtain ⟨hb, ht, hs⟩ := Finset.mem_filter.mp hp
    have hc : p ∈ (actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter (fun q => actualPrimeTupleLog N q ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion HistoricalPrefixCapData.p1_fourthParentGateForms
              (D.p1_fourthParentGateBounds j)) :=
      Finset.mem_filter.mpr ⟨hb, ht⟩
    rw [← hdict] at hc
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2, hs⟩

theorem admittedWallMass_eq_cube_sum
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    admittedWallMass D N cap j delta =
      ∑ p ∈ (actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter (fun p =>
          actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
              primeAffineGateRegion HistoricalPrefixCapData.p1_fourthParentGateForms
                (D.p1_fourthParentGateBounds j) ∧
          inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p)),
        ∏ i, 1 / ((p i : ℝ) - 1) := by
  unfold admittedWallMass
  rw [admittedWallTuples_eq_cube_filter D hab hcheck N cap hN hcap j delta]

/-- Shrinking the strip reduces its actual arithmetic mass. -/
theorem admittedWallMass_mono
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) {delta delta' : ℝ} (hdelta : delta ≤ delta') :
    admittedWallMass D N cap j delta ≤ admittedWallMass D N cap j delta' := by
  rw [admittedWallMass_eq_cube_sum D hab hcheck N cap hN hcap j delta,
    admittedWallMass_eq_cube_sum D hab hcheck N cap hN hcap j delta']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hb, ht, hs⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hb, ht, inOldWallStrip_mono hdelta hs⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- The arithmetic budget is paid on a concrete public cube strip.
Dropping T3/order/owner predicates only enlarges a sum of positive weights. -/
theorem admittedWallMass_le_publicStrip
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    admittedWallMass D N cap j delta ≤
      actualPrimeAffineWallStripMass N (fun _ : Fin 4 => (D.a : ℝ))
        (fun _ => (D.b : ℝ)) publicWallForms (publicWallBounds (D.old4 j : ℝ)) delta := by
  rw [admittedWallMass_eq_cube_sum D hab hcheck N cap hN hcap j delta]
  unfold actualPrimeAffineWallStripMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hb, _ht, hs⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hb, inOldWallStrip_mem_public hs⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- A requested positive reserve chooses the width BEFORE the threshold.
The threshold works for every later target and every adequate enumeration cap. -/
theorem exists_admittedWallMass_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        admittedWallMass D N cap j delta < eta := by
  obtain ⟨delta, hd, N₀, hN₀, hbound⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by exact_mod_cast ha : 0 < (D.a : ℝ)) (by exact_mod_cast hab : (D.a : ℝ) < D.b)
    publicWallForms (publicWallBounds (D.old4 j : ℝ)) publicWallForms_ne_zero eta heta
  refine ⟨delta, hd, N₀, hN₀, ?_⟩
  intro N cap hN hcap
  have hn : 1 < N := by omega
  exact (admittedWallMass_le_publicStrip D hab hcheck N cap hn hcap j delta).trans_lt
    (hbound N hN)

/-- Different half-open owners cannot count an actual tuple twice. -/
theorem admittedWallTuples_disjoint (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (delta : ℝ) (j k : Fin 4 → Fin (D.m + 1)) (hne : j ≠ k) :
    Disjoint (admittedWallTuples D N cap j delta) (admittedWallTuples D N cap k delta) := by
  rw [Finset.disjoint_left]
  intro p hpj hpk
  have hj := (Finset.mem_filter.mp hpj).2.1
  have hk := (Finset.mem_filter.mp hpk).2.1
  exact hne (logPrimeMeshCell_unique (by exact_mod_cast hab) hj hk)

/-- The finite-family mass is exactly a rearrangement over a disjoint union;
there is no multiplicity loss or extra factorial in this accounting. -/
theorem sum_admittedWallMass_eq_biUnion
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ) (delta : ℝ)
    (J : Finset (Fin 4 → Fin (D.m + 1))) :
    (∑ j ∈ J, admittedWallMass D N cap j delta) =
      ∑ p ∈ J.biUnion (fun j => admittedWallTuples D N cap j delta),
        ∏ i, 1 / ((p i : ℝ) - 1) := by
  unfold admittedWallMass
  symm
  apply Finset.sum_biUnion
  intro j _hj k _hk hne
  exact admittedWallTuples_disjoint D hab N cap delta j k hne

/-- Any fixed finite family has one positive width and one common arithmetic
threshold.  This includes all selected and fallback fourth owners at once. -/
theorem exists_sum_admittedWallMass_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (J : Finset (Fin 4 → Fin (D.m + 1)))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        (∑ j ∈ J, admittedWallMass D N cap j delta) < eta := by
  induction J using Finset.induction_on generalizing eta with
  | empty =>
      refine ⟨1, zero_lt_one, 2, le_rfl, ?_⟩
      intro N cap _hN _hcap
      simpa using heta
  | @insert j J hj ih =>
      obtain ⟨delta₁, hd₁, N₁, hN₁, hbound₁⟩ :=
        exists_admittedWallMass_lt D ha hab hcheck j (eta / 2) (half_pos heta)
      obtain ⟨delta₂, hd₂, N₂, hN₂, hbound₂⟩ := ih (eta / 2) (half_pos heta)
      refine ⟨min delta₁ delta₂, lt_min hd₁ hd₂, max N₁ N₂,
        hN₁.trans (le_max_left _ _), ?_⟩
      intro N cap hN hcap
      have hn₁ : N₁ ≤ N := (le_max_left _ _).trans hN
      have hn₂ : N₂ ≤ N := (le_max_right _ _).trans hN
      have hn : 1 < N := by omega
      have hb₁ : admittedWallMass D N cap j (min delta₁ delta₂) < eta / 2 :=
        (admittedWallMass_mono D hab hcheck N cap hn hcap j (min_le_left _ _)).trans_lt
          (hbound₁ N cap hn₁ hcap)
      have hb₂ : (∑ k ∈ J, admittedWallMass D N cap k (min delta₁ delta₂)) < eta / 2 := by
        apply lt_of_le_of_lt _ (hbound₂ N cap hn₂ hcap)
        apply Finset.sum_le_sum
        intro k _hk
        exact admittedWallMass_mono D hab hcheck N cap hn hcap k (min_le_right _ _)
      rw [Finset.sum_insert hj]
      linarith

/-- Direct all-owners endpoint; the finite family is the genuine complete mesh. -/
theorem exists_all_admittedWallMass_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        (∑ j : Fin 4 → Fin (D.m + 1), admittedWallMass D N cap j delta) < eta := by
  exact exists_sum_admittedWallMass_lt D ha hab hcheck Finset.univ eta heta

end P1HistoricalFourthArithmeticWallStrip

end

end ImbalancedChen
