import ImbalancedChen.P2FiniteMarkedGamma5SeedConversionFloor
import ImbalancedChen.P2FiniteMarkedGamma5AtlasFamily
import ImbalancedChen.P5zFiniteFallbackPositiveOuter

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasFinitePP

noncomputable section
open Filter Finset Real
open P2FiniteMarkedGamma5NativeSeedSum
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2Selected430CausalOccurrenceExporter P2EnhancedLowerPhysicalTransition
open Part5OriginalH430EmittedNativeQueries Part5OriginalH430EmittedPathMultiplicity
open P2FiniteMarkedGamma5FixedNativeItinerary
open Part5OriginalH430NativeQueryPaths Part5OriginalH430IntegerItineraries
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430FrozenRootRefinement (RootCode frozenLeafCutoffFloor)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalCausalSmoothAtlas (Plan Code)
open P2FiniteMarkedGamma5AtlasFamily (atlasFamily atlasFamily_nonneg)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (rho)
open scoped Classical BigOperators

/-- A fixed seed shape includes its root prime and both slots of every pair.
Only tails fitting the manuscript rank cap occur in the sum. -/
abbrev Entry (n : ℕ) :=
  {v : Index 430 × RootCode n × Fin (frozenSourceRankBound + 1) //
    Nat.card (NativeSlot v.1.val.1) + 2 + v.2.2.val ≤ frozenSourceRankBound}

noncomputable instance (n : ℕ) : Fintype (Entry n) := Fintype.ofFinite _

abbrev oldRank {n : ℕ} (v : Entry n) := Nat.card (NativeSlot v.val.1.val.1)
abbrev tailRank {n : ℕ} (v : Entry n) := v.val.2.2.val
abbrev rank {n : ℕ} (v : Entry n) := oldRank v + (2 + tailRank v)
abbrev Tuple {n : ℕ} (N : ℕ) (v : Entry n) := Fin (rank v) → Fin (2*N+1)

private theorem mark_nonneg (i : Index 430) : 0 ≤ fixedWeight i := by
  unfold fixedWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  first | exact (edgeWeight_pos e).le | cases e <;> simp [edgeWeight] <;> positivity

/-- A plan is fixed per finite entry. Its code predicate may vary with T,
as allowed by the original all-order Family budget. -/
def weight {n : ℕ} (v : Entry n) (P : Plan) (width : ℝ)
    (hf : 0 < frozenLeafCutoffFloor) (hw : 0 < width) (hw1 : width ≤ 1)
    (accept : ℕ → (Fin (oldRank v) → Code P) → Prop)
    (N : ℕ) (u : Tuple N v) : ℝ :=
  (atlasFamily P frozenSourceRankBound (oldRank v) (tailRank v)
    frozenLeafCutoffFloor width (fun T => log (cellQ T n v.val.2.1))
    accept hf hw hw1 v.property).ambient N ⟨rank v, by
      have H := v.property
      change oldRank v + 2 + tailRank v ≤ frozenSourceRankBound at H
      dsimp [rank]; omega⟩ (fun j => ((u j).val : ℝ))

private theorem weight_nonneg {n : ℕ} (v : Entry n) (P : Plan) (width : ℝ)
    (hf : 0 < frozenLeafCutoffFloor) (hw : 0 < width) (hw1 : width ≤ 1)
    (accept : ℕ → (Fin (oldRank v) → Code P) → Prop) (N : ℕ) (u : Tuple N v) :
    0 ≤ weight v P width hf hw hw1 accept N u := by
  unfold weight
  apply atlasFamily_nonneg

/-- Finite fallback at the actual target. Every term uses its full prime
tuple enumerator at cap 2N, the same moduli and the same coefficient.
The supplied atlas code readouts still need their geometric comparison
to the selected seed sum; this finite inequality makes no such assumption. -/
theorem fallback {n : ℕ} (P : Entry n → Plan) (width : ℝ)
    (hf : 0 < frozenLeafCutoffFloor) (hw : 0 < width) (hw1 : width ≤ 1)
    (accept : (v : Entry n) → ℕ → (Fin (oldRank v) → Code (P v)) → Prop)
    (B : Bank) (round mesh : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau L : ℝ) (hL : 1 < L) (hwL : (N : ℝ)^omega ≤ L)
    (hwz : (N : ℝ)^omega ≤ cutoff N) (hz : cutoff N ≤ (N : ℝ)) :
    let S := fun v : Entry n => Part3.labelledPrimeTuples (rank v) (2*N)
    let W := fun v : Entry n => weight v (P v) width hf hw hw1 (accept v) N
    let m := fun v : Entry n => fixedWeight v.val.1
    let Q := moduli N ((N : ℝ)^omega)
    let R := rho B round mesh e q a omega N tau L
    (∑ v, m v * p5z_labelledPrimeMass (S v) Part3.labelledProduct (W v) N) ≤
      (∑ v, m v * p5z_labelledMass (S v) (W v)) * physicalDensitySum Q R +
      (∑ v, m v * p5z_labelledCoprimeCorrection (S v) Part3.labelledProduct (W v) Q R) +
      (∑ v, m v * Part3.primeProductSignedError (rank v) (2*N) N Q R (W v)) +
      (∑ v, m v * p5z_labelledSmallPrimeMass (S v) Part3.labelledProduct (W v) N
        (Nat.ceil (cutoff N))) := by
  dsimp only
  have H := P5zLabelledIntegerShiftPositiveSieve.sum_primeMass_le_main_add_errors
    (univ : Finset (Entry n)) (fun v => fixedWeight v.val.1)
    (fun v => Part3.labelledPrimeTuples (rank v) (2*N))
    (fun _ => Part3.labelledProduct)
    (fun v => weight v (P v) width hf hw hw1 (accept v) N) N (Nat.ceil (cutoff N))
    (moduli N ((N : ℝ)^omega)) (rho B round mesh e q a omega N tau L)
    (fun v _ => mark_nonneg v.val.1)
    (fun v _ u _ => weight_nonneg v (P v) width hf hw hw1 (accept v) N u)
    (P4AOriginalFiniteFallbackCount.upper_majorant B round mesh e q a omega N tau L
      hL hwL hwz hz)
  simpa only [p5z_labelledDistributionError_eq_primeProductSignedError] using H

/-- Match a numerical density ceiling to the same-N converted price of
the original seed mass, with its target singular series and no limit in d. -/
theorem density_times_seed_ordinary {epsilon : ℝ} (he : 0 < epsilon)
    (he1 : epsilon < 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (n : ℕ) (k : Part5OriginalH430PhysicalRoots.Root)
      (t : ℝ), 0 ≤ t → t ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ (D C : ℝ), 0 ≤ C → D ≤ C * (singularSeries N / log (N:ℝ)) →
      let Q := Part5OriginalH430FrozenIntegerSupport.rootQ N n k t
      let m := P2FiniteMarkedGamma5SeedOrdinaryPrice.seedMass N n k t
        (fun p w => P2EnhancedBadGamma5ArithmeticGeometry.ordinaryBad N (Q p) w.prod)
      let Y := P2FiniteMarkedGamma5SeedOrdinaryPrice.seedMass N n k t
        (fun p w => P2EnhancedSwitchedTrueNormalization.thetaConversion N w.prod *
          P2EnhancedBadGamma5ArithmeticGeometry.ordinaryBad N (Q p) w.prod)
      m * D ≤ (C / (1-epsilon)) * ((1/4:ℝ)*Y) := by
  filter_upwards [P2FiniteMarkedGamma5SeedConversionFloor.same_seed_density_unit he] with N H
  intro n k t ht ht' hn D C hC hD
  dsimp only
  specialize H n k t ht ht' hn
  dsimp only at H
  let m := P2FiniteMarkedGamma5SeedOrdinaryPrice.seedMass N n k t
    (fun p w => P2EnhancedBadGamma5ArithmeticGeometry.ordinaryBad N
      (Part5OriginalH430FrozenIntegerSupport.rootQ N n k t p) w.prod)
  have hm : 0 ≤ m := by
    unfold m P2FiniteMarkedGamma5SeedOrdinaryPrice.seedMass
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro x _
    split_ifs
    · apply mul_nonneg (mark_nonneg i)
      exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    · exact le_rfl
  have hu : 0 < 1-epsilon := sub_pos.mpr he1
  calc
    m * D ≤ m * (C * (singularSeries N / log (N:ℝ))) :=
      mul_le_mul_of_nonneg_left hD hm
    _ = (C/(1-epsilon))*(((1-epsilon)*singularSeries N/log (N:ℝ))*m) := by
      calc
        _ = (C * ((1-epsilon)⁻¹ * (1-epsilon))) *
            (singularSeries N / log (N:ℝ)) * m := by rw [inv_mul_cancel₀ hu.ne']; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left H (div_nonneg hC hu.le)

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedAtlasFinitePP
