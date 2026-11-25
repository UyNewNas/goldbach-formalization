import ImbalancedChen.P2FiniteMarkedGamma5SharpTupleCount
import ImbalancedChen.P2FiniteMarkedGamma5ActualTargetExclusion
import ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport
import Mathlib.Data.Nat.GCD.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

A finite comparison for the original inner physical-profile sum at one
literal old word and one common Q. The sharp part is charged to the
original ordinaryBad with coefficient one. The same original weighted
complete-product noncoprime slice pays the excluded arithmetic part.
The remaining supported inner tuples lie in the original properStrip.

Complete-product coprimality is used only for this positive partition.
It is not identified with the original pair-source condition, and no
tail coprimality or distinctness is added to ordinaryBad. All coordinates,
empty old/tail blocks and repeated tail values are retained.

The strip term is an explicit count on the same bounded prime carrier.
No strip-payment estimate, original history sum, J bound or global smooth
selected-history realization is assumed or concluded.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5InnerComparison

noncomputable section
open Finset Real
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)
open P2FiniteMarkedGamma5LogExtension (program raw accepted raw_iff_passed)
open P2FiniteMarkedGamma5PhysicalExtension
  (physicalProduct physicalProfile_bounds logPoint_prefix_eq_log_product)
open P2FiniteMarkedGamma5EulerWordBudget
  (finPhysicalProfile finToPhysical slotEquiv)
open P2FiniteMarkedGamma5IntegerSupport (physicalProduct_finToPhysical)
open P2FiniteMarkedGamma5RadialProfileCollar (radialWidth radialWidth_pos)
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues)
open P2FiniteMarkedGamma5ActualRadialAggregate
  (Split admissibleSplit tuplePrefix boundedProfileWeight boundedInnerSlice)
open P2FiniteMarkedGamma5ActualTargetExclusion (noncoprimeSlice)
open P2FiniteMarkedGamma5SharpTupleCount
  (Tuple tupleFresh tupleTail sharpTuples mem_sharpTuples sharp_count_le_ordinaryBad)
open P2FiniteMarkedGamma5NonradialSupport
  (properStrip inner_nonzero_failure_mem_properStrip)
open P2EnhancedBadGamma5ArithmeticGeometry (ordinaryBad)
open scoped Classical BigOperators

/-- The existing prefix-log product identity reads the original integer
old word. The fresh and tail blocks are the unchanged slot projections. -/
theorem tuple_physical_logPoint {k r : ℕ} (u : Fin (k + (2 + r)) → ℕ)
    (hu : ∀ i, 0 < u i) :
    P2FiniteMarkedGamma5PhysicalExtension.logPoint
        (finToPhysical k r (fun i => (u i : ℝ))) =
      P2FiniteMarkedGamma5LogExtension.logPoint (tuplePrefix u).prod
        (tupleFresh u) (tupleTail u) := by
  apply Prod.ext
  · calc
      _ = log (∏ i : Fin k, finToPhysical k r (fun j => (u j : ℝ)) (.inl i)) :=
        logPoint_prefix_eq_log_product (fun i => Nat.cast_pos.mpr (hu _))
      _ = log ((tuplePrefix u).prod : ℝ) := by
        congr 1
        change (∏ i : Fin k, (u (i.castAdd (2 + r)) : ℝ)) =
          ((tuplePrefix u).prod : ℝ)
        simp only [tuplePrefix, List.prod_ofFn, Nat.cast_prod]
  · rfl

/-- The clean part of the inner support on the original proper strips.
The complete-coprime condition belongs only to the error partition;
the original ordinaryBad source keeps its original arithmetic conditions. -/
def properStripTuples (N : ℕ) (Q h : ℝ) (w : List ℕ) (s : Split) :
    Finset (Tuple N s) :=
  (Part3.labelledPrimeTuples (s.1.val + (2 + s.2.val)) (2 * N)).filter fun v =>
    admissibleSplit s ∧
      w = tuplePrefix (tupleValues v) ∧
      finPhysicalProfile (log Q) (N : ℝ) (radialWidth h)
        ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ)) ≠ 0 ∧
      (Part3.labelledProduct v : ℝ) ≤ (N : ℝ) ∧
      Nat.Coprime (Part3.labelledProduct v) N ∧
      properStrip (log Q) (log (N : ℝ)) (radialWidth h)
        (P2FiniteMarkedGamma5PhysicalExtension.logPoint
          (finToPhysical s.1.val s.2.val (fun i => ((v i).val : ℝ))))

private theorem bounded_weight_bounds (N k r : ℕ) (logQ h : ℝ) (w : List ℕ)
    (v : Fin (k + (2 + r)) → Fin (2 * N + 1)) :
    0 ≤ boundedProfileWeight N k r logQ h w v ∧
      boundedProfileWeight N k r logQ h w v ≤ 1 := by
  unfold boundedProfileWeight
  split_ifs
  · exact physicalProfile_bounds logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor)
      (finToPhysical k r (fun i => ((v i).val : ℝ)))
  · exact ⟨le_rfl, zero_le_one⟩

private theorem inner_weight_le {N : ℕ} {Q h : ℝ} {w : List ℕ}
    {s : Split} {v : Tuple N s}
    (hN : 0 < N) (hd : 0 < w.prod) (hR : 1 < Q / (w.prod : ℝ)) (hh : 0 < h)
    (hs : admissibleSplit s)
    (hv : v ∈ Part3.labelledPrimeTuples (s.1.val + (2 + s.2.val)) (2 * N)) :
    (if (Part3.labelledProduct v : ℝ) ≤ (N : ℝ) then
      boundedProfileWeight N s.1.val s.2.val (log Q) h w v else 0) ≤
      (if v ∈ sharpTuples N Q w s then (1 : ℝ) else 0) +
      (if Nat.Coprime (Part3.labelledProduct v) N then 0 else
        boundedProfileWeight N s.1.val s.2.val (log Q) h w v) +
      (if v ∈ properStripTuples N Q h w s then (1 : ℝ) else 0) := by
  have hbds := bounded_weight_bounds N s.1.val s.2.val (log Q) h w v
  have hsharp0 : 0 ≤ (if v ∈ sharpTuples N Q w s then (1 : ℝ) else 0) := by
    positivity
  have hstrip0 : 0 ≤ (if v ∈ properStripTuples N Q h w s then (1 : ℝ) else 0) := by
    positivity
  have hbad0 : 0 ≤ (if Nat.Coprime (Part3.labelledProduct v) N then (0 : ℝ) else
      boundedProfileWeight N s.1.val s.2.val (log Q) h w v) := by
    split_ifs
    · exact le_rfl
    · exact hbds.1
  by_cases hcap : (Part3.labelledProduct v : ℝ) ≤ (N : ℝ)
  · rw [if_pos hcap]
    by_cases hz : boundedProfileWeight N s.1.val s.2.val (log Q) h w v = 0
    · simp only [hz]
      positivity
    · have hprefix : w = tuplePrefix (tupleValues v) := by
        by_contra hn
        apply hz
        simp only [boundedProfileWeight, if_neg hn]
      have hne : finPhysicalProfile (log Q) (N : ℝ) (radialWidth h)
          ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ)) ≠ 0 := by
        simpa only [boundedProfileWeight, if_pos hprefix] using hz
      by_cases hcop : Nat.Coprime (Part3.labelledProduct v) N
      · simp only [if_pos hcop, add_zero]
        have hprime : ∀ i, (v i).val.Prime := (mem_filter.mp hv).2
        let x := finToPhysical s.1.val s.2.val (fun i => ((v i).val : ℝ))
        have hlog :
            P2FiniteMarkedGamma5PhysicalExtension.logPoint x =
              P2FiniteMarkedGamma5LogExtension.logPoint w.prod
                (tupleFresh (tupleValues v)) (tupleTail (tupleValues v)) := by
          have ht := tuple_physical_logPoint (tupleValues v) (fun i => (hprime i).pos)
          rw [← hprefix] at ht
          exact ht
        by_cases haccepted :
            accepted (log Q) (log (N : ℝ))
              (P2FiniteMarkedGamma5PhysicalExtension.logPoint x)
        · have hfresh (i : Fin 2) : (tupleFresh (tupleValues v) i).Coprime N :=
            Nat.Coprime.of_dvd_left
              (dvd_prod_of_mem (fun j => (v j).val)
                (mem_univ (slotEquiv s.1.val s.2.val (.inr (.inl i))))) hcop
          have hraw : ∀ g ∈ program s.2.val,
              raw N Q w.prod (tupleFresh (tupleValues v)) (tupleTail (tupleValues v)) g := by
            intro g hg
            apply (raw_iff_passed hN hd hR
              (fun i => (hprime (slotEquiv s.1.val s.2.val (.inr (.inl i)))).pos)
              (fun i => (hprime (slotEquiv s.1.val s.2.val (.inr (.inr i)))).pos) g).mpr
            rw [← hlog]
            exact haccepted g hg
          have hsharp : v ∈ sharpTuples N Q w s :=
            mem_sharpTuples.mpr ⟨hprime, hs, hprefix, hfresh, hraw⟩
          rw [if_pos hsharp]
          exact hbds.2.trans (le_add_of_nonneg_right hstrip0)
        · have hb : 0 < (N : ℝ) ^ frozenLeafCutoffFloor :=
            rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
          have hcap' : physicalProduct x ≤ (N : ℝ) := by
            simpa only [x, physicalProduct_finToPhysical, Part3.labelledProduct,
              Nat.cast_prod] using hcap
          have hstrip := inner_nonzero_failure_mem_properStrip
            (x := x) hb (radialWidth_pos hh) hne hcap' haccepted
          have hmem : v ∈ properStripTuples N Q h w s :=
            mem_filter.mpr ⟨hv, hs, hprefix, hne, hcap, hcop, hstrip⟩
          rw [if_pos hmem]
          exact hbds.2.trans (le_add_of_nonneg_left hsharp0)
      · rw [if_neg hcop]
        linarith only [hsharp0, hstrip0]
  · rw [if_neg hcap]
    exact add_nonneg (add_nonneg hsharp0 hbad0) hstrip0

private theorem sum_indicator_eq_card {α : Type*} [DecidableEq α]
    (S T : Finset α) (hTS : T ⊆ S) :
    (∑ v ∈ S, if v ∈ T then (1 : ℝ) else 0) = (T.card : ℝ) := by
  have hfilter : S.filter (fun v => v ∈ T) = T := by
    ext v
    simp only [mem_filter]
    exact ⟨And.right, fun h => ⟨hTS h, h⟩⟩
  rw [← sum_filter, hfilter]
  simp

/-- A single original split: the smooth weight is paid by the sharp
count, the unchanged weighted noncoprime slice and a proper-strip count. -/
theorem boundedInnerSlice_le_sharp_add_errors (N : ℕ) (Q h : ℝ) (w : List ℕ)
    (hN : 0 < N) (hd : 0 < w.prod) (hR : 1 < Q / (w.prod : ℝ)) (hh : 0 < h)
    (s : Split) (hs : admissibleSplit s) :
    boundedInnerSlice N s.1.val s.2.val (log Q) h w ≤
      ((sharpTuples N Q w s).card : ℝ) +
      noncoprimeSlice N s.1.val s.2.val (log Q) h w +
      ((properStripTuples N Q h w s).card : ℝ) := by
  let P := Part3.labelledPrimeTuples (s.1.val + (2 + s.2.val)) (2 * N)
  have hsharp := sum_indicator_eq_card P (sharpTuples N Q w s) (filter_subset _ _)
  have hstrip := sum_indicator_eq_card P (properStripTuples N Q h w s) (filter_subset _ _)
  calc
    _ ≤ ∑ v ∈ P,
        (if v ∈ sharpTuples N Q w s then (1 : ℝ) else 0) +
        (if Nat.Coprime (Part3.labelledProduct v) N then 0 else
          boundedProfileWeight N s.1.val s.2.val (log Q) h w v) +
        (if v ∈ properStripTuples N Q h w s then (1 : ℝ) else 0) :=
      sum_le_sum (fun v hv => inner_weight_le hN hd hR hh hs hv)
    _ = _ := by
      simp only [sum_add_distrib, hsharp, hstrip, noncoprimeSlice, P]

/-- The exact original fixed-word inner sum, with the original bounded
split admission. The sharp contribution is charged once to ordinaryBad.
There is no assumption that the entire inner support is sharp. -/
theorem inner_sum_le_ordinaryBad_add_errors (N : ℕ) (Q h : ℝ) (w : List ℕ)
    (hN : 0 < N) (hd : 0 < w.prod) (hR : 1 < Q / (w.prod : ℝ)) (hh : 0 < h) :
    (∑ s : Split, if admissibleSplit s then
      boundedInnerSlice N s.1.val s.2.val (log Q) h w else 0) ≤
      ordinaryBad N Q w.prod +
      (∑ s : Split, if admissibleSplit s then
        noncoprimeSlice N s.1.val s.2.val (log Q) h w else 0) +
      ∑ s : Split, ((properStripTuples N Q h w s).card : ℝ) := by
  have hrow (s : Split) :
      (if admissibleSplit s then
        boundedInnerSlice N s.1.val s.2.val (log Q) h w else 0) ≤
        ((sharpTuples N Q w s).card : ℝ) +
        (if admissibleSplit s then
          noncoprimeSlice N s.1.val s.2.val (log Q) h w else 0) +
        ((properStripTuples N Q h w s).card : ℝ) := by
    by_cases hs : admissibleSplit s
    · simpa only [if_pos hs] using
        boundedInnerSlice_le_sharp_add_errors N Q h w hN hd hR hh s hs
    · simp only [if_neg hs]
      positivity
  calc
    _ ≤ ∑ s : Split,
        (((sharpTuples N Q w s).card : ℝ) +
        (if admissibleSplit s then
          noncoprimeSlice N s.1.val s.2.val (log Q) h w else 0) +
        ((properStripTuples N Q h w s).card : ℝ)) :=
      sum_le_sum (fun s _ => hrow s)
    _ = (∑ s : Split, ((sharpTuples N Q w s).card : ℝ)) +
        (∑ s : Split, if admissibleSplit s then
          noncoprimeSlice N s.1.val s.2.val (log Q) h w else 0) +
        ∑ s : Split, ((properStripTuples N Q h w s).card : ℝ) := by
      simp only [sum_add_distrib]
    _ ≤ _ :=
      add_le_add_right (add_le_add_right (sharp_count_le_ordinaryBad N Q w hd) _) _

end
end ImbalancedChen.P2FiniteMarkedGamma5InnerComparison
