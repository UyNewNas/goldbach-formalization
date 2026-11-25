import ImbalancedChen.P2FiniteMarkedGamma5ActualRank
import ImbalancedChen.P2FiniteMarkedGamma5SeedPlateau
import ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The existing physical profile equals one on the actual U4 marked source.
This file only identifies its separate old/fresh/tail coordinates with
the original logarithmic source point and applies the existing plateau.
All old marks and every repeated rough factor remain separate slots.
No floor, rank, prime licence or source equality is assumed anew.

The old arithmetic-history imports still require qualification. No
complete Family, collar payment, or PP/VM estimate is claimed here.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualPhysicalPlateau

noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels pair_eq)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430SeedHistoryMass
open P2FiniteMarkedGamma5LogExtension
open P2FiniteMarkedGamma5PhysicalExtension
open P2FiniteMarkedGamma5ActualRank
open P2FiniteMarkedGamma5SeedPlateau
open P2FiniteMarkedGamma5EulerWordBudget
open scoped Classical BigOperators

/-- Literal physical values at every tagged source slot. -/
def sourcePhysicalPoint (old qs : List ℕ) (m : ℕ) :
    PhysicalPoint old.length m.primeFactorsList.length
  | .inl i => (old[i.val] : ℝ)
  | .inr (.inl i) => (sourcePair qs i : ℝ)
  | .inr (.inr i) => (canonicalTail m i : ℝ)

/-- The already accepted prefix-log product identity gives the exact
old logarithmic source point; no old coordinate is collapsed in the
physical domain itself. -/
theorem sourcePhysicalPoint_logPoint (old qs : List ℕ) (m : ℕ)
    (hold : ∀ q ∈ old, 0 < q) :
    P2FiniteMarkedGamma5PhysicalExtension.logPoint (sourcePhysicalPoint old qs m) =
      P2FiniteMarkedGamma5LogExtension.logPoint (parentProduct old)
        (sourcePair qs) (canonicalTail m) := by
  apply Prod.ext
  · calc
      _ = log (∏ i, sourcePhysicalPoint old qs m (.inl i)) :=
        logPoint_prefix_eq_log_product
          (fun i => Nat.cast_pos.mpr (hold _ (List.getElem_mem i.isLt)))
      _ = log (parentProduct old : ℝ) := by
        congr 1
        change (∏ i : Fin old.length, (old[i.val] : ℝ)) = (old.prod : ℝ)
        have hlist : List.ofFn (fun i : Fin old.length => old[i.val]) = old :=
          List.ofFn_getElem
        have hprod := congrArg (fun xs : List ℕ => (xs.prod : ℝ)) hlist
        simpa only [Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn] using hprod
  · rfl

/-- The original source conditions supply the floor at each physical
coordinate, with no coordinate-floor hypothesis passed by the caller. -/
theorem enhanced_position_physical_floor {N n p dep m : ℕ} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N .U4)
    (l : LevelIndex N n .U4 t p dep) {qs : List ℕ}
    (hq : qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l))
    (hm : m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227 / 50))) :
    ∀ i, (N : ℝ) ^ frozenLeafCutoffFloor ≤
      sourcePhysicalPoint (levelOccurrence l).current.old qs m i := by
  have hs := (enhanced_position_source_data hN ht ht' hn hp l hq hm).1
  intro i
  rcases i with i | i
  · exact (hs _ (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl (List.getElem_mem i.isLt)))))).2
  · rcases i with i | i
    · have hmem : sourcePair qs i ∈ qs := by
        rw [pair_eq (mem_filter.mp hq).1]
        fin_cases i <;> simp [sourcePair]
      exact (hs _ (List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inr hmem))))).2
    · exact (hs _ (List.mem_append.mpr (Or.inr (canonicalTail_mem m i)))).2

/-- The actual physical source is on the one plateau, using exactly the
historical cutoff N^frozenLeafCutoffFloor and the original Gamma5 gates. -/
theorem enhanced_position_physical_source_one {N n p dep m : ℕ} {t width : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N .U4)
    (hw : 0 < width) (l : LevelIndex N n .U4 t p dep) {qs : List ℕ}
    (hq : qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l))
    (hm : m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227 / 50))) :
    physicalProfile (log (rootQ N n .U4 t p)) (N : ℝ) width
      ((N : ℝ) ^ frozenLeafCutoffFloor)
      (sourcePhysicalPoint (levelOccurrence l).current.old qs m) = 1 := by
  have hb : 0 < (N : ℝ) ^ frozenLeafCutoffFloor :=
    rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  rw [physicalProfile_eq_original _ _ _ hb
    (enhanced_position_physical_floor hN ht ht' hn hp l hq hm)]
  rw [sourcePhysicalPoint_logPoint _ qs m
    (fun q hq => (enhanced_position_old_prime_floor hN ht ht' hn hp l q hq).1.pos)]
  exact (enhanced_position_source_one hN ht ht' hn hp hw l hq hm).2.2.2

/-- The accepted slot permutation retains the same plateau at the
original Family interface's finite coordinate numbering. -/
theorem enhanced_position_finPhysical_source_one {N n p dep m : ℕ} {t width : ℝ}
    (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ originalBand N .U4)
    (hw : 0 < width) (l : LevelIndex N n .U4 t p dep) {qs : List ℕ}
    (hq : qs ∈ badLabels N (rootQ N n .U4 t p) (wordProduct l))
    (hm : m ∈ roughNumbers ((N : ℝ) / (wordProduct l * qs.prod : ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227 / 50))) :
    finPhysicalProfile (log (rootQ N n .U4 t p)) (N : ℝ) width
      ((N : ℝ) ^ frozenLeafCutoffFloor)
      (physicalToFin (sourcePhysicalPoint (levelOccurrence l).current.old qs m)) = 1 := by
  rw [finPhysicalProfile_physicalToFin]
  exact enhanced_position_physical_source_one hN ht ht' hn hp hw l hq hm

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualPhysicalPlateau
