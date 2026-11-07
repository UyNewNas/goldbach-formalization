import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40ListFold
import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
SOURCEONLY / UNCOMPILED / NOT PASS / OPEN30.
The first import is the proposed installation name for the sibling
All40ListFold.lean.txt. Query arithmetic and the y-All40 table are unchanged.
This extends that batch API with integer weights and order-preserving filters.
-/

namespace P0QueryBatchRefinementAPI

open ImbalancedChen P0All40ListFold
open ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly

abbrev Query := Int × Int

def ValidQuery (q : Query) : Prop :=
  0 < q.2 ∧ 2*q.2 ≤ q.1 ∧ q.1 ≤ 12*q.2

def integerWeightedLo (read : Nat → OriginalNode) (coeff : Query → Int)
    (qs : List Query) : Int :=
  listSum (fun q => coeff q * readQueryLo160 read q.1 q.2) qs

def integerWeightedHi (read : Nat → OriginalNode) (coeff : Query → Int)
    (qs : List Query) : Int :=
  listSum (fun q => coeff q * readQueryHi160 read q.1 q.2) qs

noncomputable def actualMass (coeff : Query → Int) (qs : List Query) : Real :=
  listSum (weightedActualQuery (fun q => (coeff q : Real))) qs

/-- Moving the common scale after integer accumulation adds no rounding. -/
theorem integerWeightedLo_normalize (read : Nat → OriginalNode)
    (coeff : Query → Int) (qs : List Query) :
    (integerWeightedLo read coeff qs : Real) / 2^160 =
      listSum (weightedQueryLo read (fun q => (coeff q : Real))) qs := by
  unfold integerWeightedLo
  rw [listSum_int_cast_div]
  apply listSum_congr
  intro q _
  simp only [weightedQueryLo, Int.cast_mul, mul_div_assoc]

theorem integerWeightedHi_normalize (read : Nat → OriginalNode)
    (coeff : Query → Int) (qs : List Query) :
    (integerWeightedHi read coeff qs : Real) / 2^160 =
      listSum (weightedQueryHi read (fun q => (coeff q : Real))) qs := by
  unfold integerWeightedHi
  rw [listSum_int_cast_div]
  apply listSum_congr
  intro q _
  simp only [weightedQueryHi, Int.cast_mul, mul_div_assoc]

theorem checked_integer_weighted_encloses (T : CheckedBlockTable)
    (coeff : Query → Int) (qs : List Query)
    (hcoeff : ∀ q ∈ qs, 0 ≤ coeff q)
    (hvalid : ∀ q ∈ qs, ValidQuery q) :
    (integerWeightedLo (assembledRead T.blocks) coeff qs : Real) / 2^160 ≤
        actualMass coeff qs ∧
      actualMass coeff qs ≤
        (integerWeightedHi (assembledRead T.blocks) coeff qs : Real) / 2^160 := by
  rw [integerWeightedLo_normalize, integerWeightedHi_normalize]
  apply checked_weighted_query_list_encloses
  · intro q hq
    exact Int.cast_nonneg.mpr (hcoeff q hq)
  · exact hvalid

theorem integerWeighted_append (read : Nat → OriginalNode)
    (coeff : Query → Int) (qs rs : List Query) :
    integerWeightedLo read coeff (qs ++ rs) =
        integerWeightedLo read coeff qs + integerWeightedLo read coeff rs ∧
      integerWeightedHi read coeff (qs ++ rs) =
        integerWeightedHi read coeff qs + integerWeightedHi read coeff rs := by
  exact ⟨listSum_append _ qs rs, listSum_append _ qs rs⟩

theorem actualMass_append (coeff : Query → Int) (qs rs : List Query) :
    actualMass coeff (qs ++ rs) = actualMass coeff qs + actualMass coeff rs := by
  exact listSum_append _ qs rs

/-- Independent checked subbatches combine before the common division. -/
theorem checked_append_integer_weighted_encloses (T : CheckedBlockTable)
    (coeff : Query → Int) (qs rs : List Query)
    (hcoeffq : ∀ q ∈ qs, 0 ≤ coeff q)
    (hcoeffr : ∀ q ∈ rs, 0 ≤ coeff q)
    (hvalidq : ∀ q ∈ qs, ValidQuery q)
    (hvalidr : ∀ q ∈ rs, ValidQuery q) :
    ((integerWeightedLo (assembledRead T.blocks) coeff qs +
        integerWeightedLo (assembledRead T.blocks) coeff rs : Int) : Real) /
        2^160 ≤ actualMass coeff qs + actualMass coeff rs ∧
      actualMass coeff qs + actualMass coeff rs ≤
        ((integerWeightedHi (assembledRead T.blocks) coeff qs +
          integerWeightedHi (assembledRead T.blocks) coeff rs : Int) : Real) /
          2^160 := by
  have hq := checked_integer_weighted_encloses T coeff qs hcoeffq hvalidq
  have hr := checked_integer_weighted_encloses T coeff rs hcoeffr hvalidr
  constructor
  · simpa only [Int.cast_add, add_div] using add_le_add hq.1 hr.1
  · simpa only [Int.cast_add, add_div] using add_le_add hq.2 hr.2

/-- These are additive commutative sums: stable filters preserve each
occurrence, while the complementary pieces may interleave in the source. -/
theorem listSum_filter_partition {α β : Type*} [AddCommMonoid β]
    (value : α → β) (keep : α → Bool) (xs : List α) :
    listSum value xs = listSum value (xs.filter keep) +
      listSum value (xs.filter (fun x => !keep x)) := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih =>
      cases hx : keep x <;>
        simpa [listSum, hx, add_assoc, add_left_comm, add_comm] using
          congrArg (fun z => value x + z) ih

/-- Exact integer partition, before casting or normalization. -/
theorem integerWeighted_filter_partition (read : Nat → OriginalNode)
    (coeff : Query → Int) (keep : Query → Bool) (qs : List Query) :
    integerWeightedLo read coeff qs =
        integerWeightedLo read coeff (qs.filter keep) +
          integerWeightedLo read coeff (qs.filter (fun q => !keep q)) ∧
      integerWeightedHi read coeff qs =
        integerWeightedHi read coeff (qs.filter keep) +
          integerWeightedHi read coeff (qs.filter (fun q => !keep q)) := by
  exact ⟨listSum_filter_partition _ keep qs, listSum_filter_partition _ keep qs⟩

theorem actualMass_filter_partition (coeff : Query → Int)
    (keep : Query → Bool) (qs : List Query) :
    actualMass coeff qs = actualMass coeff (qs.filter keep) +
      actualMass coeff (qs.filter (fun q => !keep q)) := by
  exact listSum_filter_partition _ keep qs

/-- Validity and coefficient nonnegativity restrict by membership, so the
stored reader is checked once and consumed for any stable filtered batch. -/
theorem checked_filtered_integer_weighted_encloses (T : CheckedBlockTable)
    (coeff : Query → Int) (keep : Query → Bool) (qs : List Query)
    (hcoeff : ∀ q ∈ qs, 0 ≤ coeff q)
    (hvalid : ∀ q ∈ qs, ValidQuery q) :
    (integerWeightedLo (assembledRead T.blocks) coeff (qs.filter keep) : Real) /
        2^160 ≤ actualMass coeff (qs.filter keep) ∧
      actualMass coeff (qs.filter keep) ≤
        (integerWeightedHi (assembledRead T.blocks) coeff (qs.filter keep) : Real) /
          2^160 := by
  apply checked_integer_weighted_encloses
  · intro q hq
    exact hcoeff q (List.mem_filter.mp hq).1
  · intro q hq
    exact hvalid q (List.mem_filter.mp hq).1

/-- One normalized total may be assembled from two separately accumulated
integer batches, including repeated query requests. -/
theorem checked_filter_partition_encloses (T : CheckedBlockTable)
    (coeff : Query → Int) (keep : Query → Bool) (qs : List Query)
    (hcoeff : ∀ q ∈ qs, 0 ≤ coeff q)
    (hvalid : ∀ q ∈ qs, ValidQuery q) :
    ((integerWeightedLo (assembledRead T.blocks) coeff (qs.filter keep) +
        integerWeightedLo (assembledRead T.blocks) coeff
          (qs.filter (fun q => !keep q)) : Int) : Real) / 2^160 ≤
        actualMass coeff qs ∧
      actualMass coeff qs ≤
        ((integerWeightedHi (assembledRead T.blocks) coeff (qs.filter keep) +
          integerWeightedHi (assembledRead T.blocks) coeff
            (qs.filter (fun q => !keep q)) : Int) : Real) / 2^160 := by
  have hp := integerWeighted_filter_partition (assembledRead T.blocks) coeff keep qs
  rw [← hp.1, ← hp.2]
  exact checked_integer_weighted_encloses T coeff qs hcoeff hvalid

/-- Sum order for a genuine sublist, using the proved nonnegativity of the
actual analytic factor. No positivity of a rounded lower integer is needed. -/
theorem actualMass_sublist_le (coeff : Query → Int) {selected all : List Query}
    (hsub : selected.Sublist all) (hcoeff : ∀ q ∈ all, 0 ≤ coeff q) :
    actualMass coeff selected ≤ actualMass coeff all := by
  unfold actualMass listSum
  apply (hsub.map (weightedActualQuery (fun q => (coeff q : Real)))).sum_le_sum
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨q, hq, rfl⟩
  exact mul_nonneg (Int.cast_nonneg.mpr (hcoeff q hq))
    (actualExtendedThirdLowerFactor_nonneg _)

theorem checked_sublist_integer_weighted_encloses (T : CheckedBlockTable)
    (coeff : Query → Int) {selected all : List Query}
    (hsub : selected.Sublist all)
    (hcoeff : ∀ q ∈ all, 0 ≤ coeff q)
    (hvalid : ∀ q ∈ all, ValidQuery q) :
    (integerWeightedLo (assembledRead T.blocks) coeff selected : Real) / 2^160 ≤
        actualMass coeff selected ∧
      actualMass coeff selected ≤
        (integerWeightedHi (assembledRead T.blocks) coeff selected : Real) / 2^160 := by
  apply checked_integer_weighted_encloses
  · intro q hq
    exact hcoeff q (hsub.subset hq)
  · intro q hq
    exact hvalid q (hsub.subset hq)

/-- A certified selected-batch lower bound also bounds the full actual sum;
the full upper bound applies to every selected subbatch. -/
theorem checked_sublist_cross_bounds (T : CheckedBlockTable)
    (coeff : Query → Int) {selected all : List Query}
    (hsub : selected.Sublist all)
    (hcoeff : ∀ q ∈ all, 0 ≤ coeff q)
    (hvalid : ∀ q ∈ all, ValidQuery q) :
    (integerWeightedLo (assembledRead T.blocks) coeff selected : Real) / 2^160 ≤
        actualMass coeff all ∧
      actualMass coeff selected ≤
        (integerWeightedHi (assembledRead T.blocks) coeff all : Real) / 2^160 := by
  have hselected := checked_sublist_integer_weighted_encloses T coeff hsub hcoeff hvalid
  have hall := checked_integer_weighted_encloses T coeff all hcoeff hvalid
  have hmono := actualMass_sublist_le coeff hsub hcoeff
  exact ⟨hselected.1.trans hmono, hmono.trans hall.2⟩

/-- The omitted contribution is exactly the complementary stable filter. -/
theorem actualMass_omitted_eq (coeff : Query → Int) (keep : Query → Bool)
    (qs : List Query) :
    actualMass coeff qs - actualMass coeff (qs.filter keep) =
      actualMass coeff (qs.filter (fun q => !keep q)) := by
  rw [actualMass_filter_partition coeff keep qs]
  exact add_sub_cancel_left _ _

theorem checked_omitted_mass_encloses (T : CheckedBlockTable)
    (coeff : Query → Int) (keep : Query → Bool) (qs : List Query)
    (hcoeff : ∀ q ∈ qs, 0 ≤ coeff q)
    (hvalid : ∀ q ∈ qs, ValidQuery q) :
    (integerWeightedLo (assembledRead T.blocks) coeff
        (qs.filter (fun q => !keep q)) : Real) / 2^160 ≤
        actualMass coeff qs - actualMass coeff (qs.filter keep) ∧
      actualMass coeff qs - actualMass coeff (qs.filter keep) ≤
        (integerWeightedHi (assembledRead T.blocks) coeff
          (qs.filter (fun q => !keep q)) : Real) / 2^160 := by
  rw [actualMass_omitted_eq]
  exact checked_filtered_integer_weighted_encloses T coeff (fun q => !keep q)
    qs hcoeff hvalid

end P0QueryBatchRefinementAPI
