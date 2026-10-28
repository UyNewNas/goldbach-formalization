import ImbalancedChen.OriginalPairedN48ArchivedOwnership
import ImbalancedChen.P2N48ActualGeometricKeyDecoder
import ImbalancedChen.P1AdoptedE0E1ActualSupport

/-!
SOURCE ONLY; uncompiled.  The 512 pair cells and the anisotropic n48
parents overlap many-to-many.  This file binds each ACTUAL fibre point
to its original archived high parent, rather than inventing a map from
one complete fine rectangle to one coarse parent.

The fibre lies in the DELETED last-pair region. It is disjoint from the
retained selectedParent(...,actualMask). The relevant source parent is
fullParent, restricted by intersection with the deleted fibre.
-/

namespace ImbalancedChen.P2FullMaskN48DeletedOwner

noncomputable section

open Set
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open OriginalPairedV2NativeN48Owner OriginalPairedN48ArchivedOwnership
open OriginalPairedN48ArchiveData
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P5Z.U11Integral P5Z.U11Canonical

abbrev ArchivedRow := ↥archivedRows

def tLo (i : Fin 48) : ℚ := Certificates.PairedV2.h +
  (Certificates.PairedV2.d - Certificates.PairedV2.h) * (i.val : ℚ) / 48
def tHi (i : Fin 48) : ℚ := Certificates.PairedV2.h +
  (Certificates.PairedV2.d - Certificates.PairedV2.h) * ((i.val : ℚ) + 1) / 48
def uLo (i : Fin 48) : ℚ := Certificates.PairedV2.a +
  (Certificates.PairedV2.h - Certificates.PairedV2.a) * (i.val : ℚ) / 48
def uHi (i : Fin 48) : ℚ := Certificates.PairedV2.a +
  (Certificates.PairedV2.h - Certificates.PairedV2.a) * ((i.val : ℚ) + 1) / 48

def pairOverlaps (r : Row) (i j : Fin 48) : Prop :=
  max (tLower (indices r).1) (tLo i) < min (tUpper (indices r).1) (tHi i) ∧
    max (uLower (indices r).2) (uLo j) < min (uUpper (indices r).2) (uHi j)

instance (r : Row) (i j : Fin 48) : Decidable (pairOverlaps r i j) := by
  unfold pairOverlaps
  infer_instance

/-- A primitive exact interval-incidence check against the ORIGINAL
literal projected xy list; no methods/floors, mean or count bound occurs. -/
def actualProjectedPairCheck : Bool := decide
  (∀ r : Row, ∀ i j : Fin 48, pairOverlaps r i j → (i, j) ∈ rawProjectedPairs)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Closed finite source proposal, NOT EXECUTED. -/
theorem actualProjectedPairCheck_true : actualProjectedPairCheck = true := by
  decide +kernel

theorem overlap_in_actual_projected_pairs (r : Row) (i j : Fin 48)
    (ho : pairOverlaps r i j) : (i, j) ∈ rawProjectedPairs := by
  have hc : ∀ r : Row, ∀ i j : Fin 48, pairOverlaps r i j → (i, j) ∈ rawProjectedPairs :=
    of_decide_eq_true actualProjectedPairCheck_true
  exact hc r i j ho

private theorem native_tLo (i : Fin 48) :
    logPrimeMeshPoint (nativeLower 0) (nativeUpper 0) 47 i.val = (tLo i : ℝ) := by
  norm_num [logPrimeMeshPoint, logPrimeMeshStep, nativeLower, nativeUpper, tLo,
    Certificates.PairedV2.h, Certificates.PairedV2.d]
    <;> push_cast <;> ring
private theorem native_tHi (i : Fin 48) :
    logPrimeMeshPoint (nativeLower 0) (nativeUpper 0) 47 (i.val + 1) = (tHi i : ℝ) := by
  norm_num [logPrimeMeshPoint, logPrimeMeshStep, nativeLower, nativeUpper, tHi,
    Certificates.PairedV2.h, Certificates.PairedV2.d]
    <;> push_cast <;> ring
private theorem native_uLo (i : Fin 48) :
    logPrimeMeshPoint (nativeLower 1) (nativeUpper 1) 47 i.val = (uLo i : ℝ) := by
  norm_num [logPrimeMeshPoint, logPrimeMeshStep, nativeLower, nativeUpper, uLo,
    Certificates.PairedV2.a, Certificates.PairedV2.h]
    <;> push_cast <;> ring
private theorem native_uHi (i : Fin 48) :
    logPrimeMeshPoint (nativeLower 1) (nativeUpper 1) 47 (i.val + 1) = (uHi i : ℝ) := by
  norm_num [logPrimeMeshPoint, logPrimeMeshStep, nativeLower, nativeUpper, uHi,
    Certificates.PairedV2.a, Certificates.PairedV2.h]
    <;> push_cast <;> ring

theorem point_forces_pair_overlap {r : Row} {x : Fin 4 → ℝ} {j : NativeIndex}
    (hf : x ∈ FullMask.support r) (hn : x ∈ nativeCell j) : pairOverlaps r (j 0) (j 1) := by
  have h0 := mem_logPrimeBox.mp hn 0
  have h1 := mem_logPrimeBox.mp hn 1
  rw [native_tLo, native_tHi] at h0
  rw [native_uLo, native_uHi] at h1
  constructor
  · have ht : max (tLower (indices r).1 : ℝ) (tLo (j 0) : ℝ) <
        min (tUpper (indices r).1 : ℝ) (tHi (j 0) : ℝ) :=
      (max_le hf.1.le h0.1).trans_lt (lt_min hf.2.1 h0.2)
    exact_mod_cast ht
  · have hu : max (uLower (indices r).2 : ℝ) (uLo (j 1) : ℝ) <
        min (uUpper (indices r).2 : ℝ) (uHi (j 1) : ℝ) :=
      (max_le hf.2.2.1.le h1.1).trans_lt (lt_min hf.2.2.2.1 h1.2)
    exact_mod_cast hu

theorem fibre_mem_full_high_domain {r : Row} {x : Fin 4 → ℝ}
    (hf : x ∈ FullMask.support r) : x ∈ originalDomain ∅ := by
  obtain ⟨haw, hwz, hzu, huh, hht, htd, _⟩ := row_fibre_argument r hf
  norm_num [Certificates.PairedV2.a, Certificates.PairedV2.h, Certificates.PairedV2.d]
    at haw huh hht htd
  exact ⟨haw.le, hwz, hzu, huh, hht.le, htd, by simp⟩

theorem fibre_pair_in_deleted_mask {r : Row} {x : Fin 4 → ℝ}
    (hf : x ∈ FullMask.support r) : (x 0, x 1) ∈ actualMask := by
  change ∃ q : Row, (x 0, x 1) ∈ P1E0E1.pairCell q
  exact ⟨r, hf.1.le, hf.2.1, hf.2.2.1.le, hf.2.2.2.1⟩

/-- Genuine source-grid identity, with high width420 and low width343.
Method, saving and ordinal are not used to define the geometric box. -/
theorem nativeCell_eq_source_nativeBox (s : SourceRow) (hs : s.term.val = 1) :
    nativeCell (rowNativeIndex s) = nativeBox s := by
  have hl (i : Fin 4) :
      logPrimeMeshPoint (nativeLower i) (nativeUpper i) 47 ((rowNativeIndex s i).val) =
        (leftEnd s i : ℝ) / 240000 := by
    fin_cases i <;>
      norm_num [logPrimeMeshPoint, logPrimeMeshStep, nativeLower, nativeUpper, rowNativeIndex,
        leftEnd, lowLo, highLo, Certificates.PairedV2.a, Certificates.PairedV2.h,
        Certificates.PairedV2.d, hs] <;> push_cast <;> ring
  have hh (i : Fin 4) :
      logPrimeMeshPoint (nativeLower i) (nativeUpper i) 47 ((rowNativeIndex s i).val + 1) =
        (rightEnd s i : ℝ) / 240000 := by
    fin_cases i <;>
      norm_num [logPrimeMeshPoint, logPrimeMeshStep, nativeLower, nativeUpper, rowNativeIndex,
        leftEnd, rightEnd, width, lowLo, highLo, Certificates.PairedV2.a,
        Certificates.PairedV2.h, Certificates.PairedV2.d, hs] <;> push_cast <;> ring
  simp only [nativeCell, nativeBox, hl, hh]

theorem exists_archived_full_parent {r : Row} {x : Fin 4 → ℝ}
    (hf : x ∈ FullMask.support r) : ∃ s : ArchivedRow, x ∈ fullParent s.val := by
  have hv : (![x 0, x 1, x 2, x 3] : Fin 4 → ℝ) = x := by
    funext i
    fin_cases i <;> rfl
  have ho := actual_v2_unique_native_parent r hf
  rw [hv] at ho
  obtain ⟨j, ⟨hj, h32, h21⟩, _hunique⟩ := ho
  have hxy := overlap_in_actual_projected_pairs r (j 0) (j 1)
    (point_forces_pair_overlap hf hj)
  obtain ⟨s, hs, hix, hiy, hiz, hiw⟩ := projected_key_has_actual_saved_record
    (j 0, j 1) hxy (j 2) (j 3) h32 h21
  have hsr : s ∈ archivedRows := List.mem_toFinset.mpr hs
  have hterm := (archived_row_facts s hsr).1
  have hindex : rowNativeIndex s = j := by
    funext i
    fin_cases i
    · simpa [rowNativeIndex] using hix
    · simpa [rowNativeIndex] using hiy
    · simpa [rowNativeIndex] using hiz
    · simpa [rowNativeIndex] using hiw
  have hb : x ∈ nativeBox s := by
    rw [← nativeCell_eq_source_nativeBox s hterm, hindex]
    exact hj
  refine ⟨⟨s, hsr⟩, ?_⟩
  have ht0 : s.term.val ≠ 0 := by omega
  simpa only [fullParent, if_neg ht0] using And.intro hb (fibre_mem_full_high_domain hf)

theorem archived_full_parent_unique {s t : ArchivedRow} {x : Fin 4 → ℝ}
    (hs : x ∈ fullParent s.val) (ht : x ∈ fullParent t.val) : s = t := by
  have hsf := archived_row_facts s.val s.property
  have htf := archived_row_facts t.val t.property
  have hsn : x ∈ nativeCell (rowNativeIndex s.val) := by
    rw [nativeCell_eq_source_nativeBox s.val hsf.1]
    exact hs.1
  have htn : x ∈ nativeCell (rowNativeIndex t.val) := by
    rw [nativeCell_eq_source_nativeBox t.val htf.1]
    exact ht.1
  have hi := nativeCell_unique hsn htn
  have hterm : s.val.term = t.val.term := Fin.ext (by omega)
  have hix : s.val.ix = t.val.ix := by simpa [rowNativeIndex] using congrFun hi 0
  have hiy : s.val.iy = t.val.iy := by simpa [rowNativeIndex] using congrFun hi 1
  have hiz : s.val.iz = t.val.iz := by simpa [rowNativeIndex] using congrFun hi 2
  have hiw : s.val.iw = t.val.iw := by simpa [rowNativeIndex] using congrFun hi 3
  apply Subtype.ext
  exact rawSelectedRows_rowKey_injective s.val t.val (List.mem_toFinset.mp s.property)
    (List.mem_toFinset.mp t.property) (by simp only [rowKey, hterm, hix, hiy, hiz, hiw])

/-- These are archived method/priority FACTS, not the analytic validity of
the old switched saving floor. That separate row-certificate remains open. -/
theorem archived_source_method_and_priority (s : ArchivedRow) :
    s.val.method = 0 ∧ 0 < s.val.floorQ ∧ s.val.ordinal ∉ priorityOrdinals := by
  have h := archived_row_is_positive_unreplaced_method0 s.val s.property
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The retained complement is the WRONG target of the fibre map. This
disjointness prevents silently identifying deleted and retained domains. -/
theorem fibre_disjoint_retained_parent (r : Row) (s : ArchivedRow) :
    Disjoint (FullMask.support r) (selectedParent s.val actualMask) := by
  apply Set.disjoint_left.mpr
  intro x hf hs
  have hterm := (archived_row_facts s.val s.property).1
  have ht0 : s.val.term.val ≠ 0 := by omega
  have hd : x ∈ originalDomain actualMask :=
    (show x ∈ nativeBox s.val ∩ originalDomain actualMask by
      simpa only [selectedParent, if_neg ht0] using hs).2
  obtain ⟨_ha, _hwz, _hzu, _huh, _hht, _htd, hnot⟩ := hd
  exact hnot (fibre_pair_in_deleted_mask hf)

end

end ImbalancedChen.P2FullMaskN48DeletedOwner
