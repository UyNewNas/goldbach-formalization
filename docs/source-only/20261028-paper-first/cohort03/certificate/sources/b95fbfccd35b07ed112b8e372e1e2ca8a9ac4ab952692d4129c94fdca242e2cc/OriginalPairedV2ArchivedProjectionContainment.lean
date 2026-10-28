import ImbalancedChen.OriginalPairedN48ArchivedOwnership
import ImbalancedChen.Certificates.PairedV2FullMaskGeometry

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / UNEXECUTED finite proposal.
-- This is pointwise containment of each ACTUAL inner fibre point. An outer
-- pair512 rectangle is allowed to meet several original n48 parent cells.
-- Geometric half-open ownership is distinct from the saved method/priority
-- policy; the latter is consumed only through Phase3's UNEXECUTED proposals.
namespace ImbalancedChen.OriginalPairedV2ArchivedProjectionContainment
open Certificates.PairedV2
open Certificates.PairedV2.FullMask
open OriginalPairedV2NativeN48Owner
open OriginalPairedN48ArchiveData
open OriginalPairedN48ArchivedOwnership
open P2N48SavedParentRowRecost

-- Literal original n48 U11 endpoint formulas in rational exponent units.
def nativeXLo (i : Fin 48) : ℚ := h+(d-h)*i.val/48
def nativeXHi (i : Fin 48) : ℚ := h+(d-h)*(i.val+1)/48
def nativeYLo (i : Fin 48) : ℚ := a+(h-a)*i.val/48
def nativeYHi (i : Fin 48) : ℚ := a+(h-a)*(i.val+1)/48

-- Each original strip consists of consecutive u bins firstU,...,511.
-- The four cross inequalities encode positive-area intersection of its
-- whole outer strip with a native (ix,iy) projection. No inner z/w box,
-- saved floor, priority flag or estimator is evaluated by this predicate.
def stripCrosses (s : Fin 186) (ix iy : Fin 48) : Prop :=
  tLower (326+s.val)<nativeXHi ix ∧ nativeXLo ix<tUpper (326+s.val) ∧
    uLower (firstU s)<nativeYHi iy ∧ nativeYLo iy<h

def stripInventoryCheck : Bool := decide
  (∀ s : Fin 186,∀ ix iy : Fin 48,stripCrosses s ix iy→(ix,iy)∈rawProjectedPairs)

-- This is a CLOSED proof-source proposal, NEVER run by the author.
-- It compares186 literal strips and the original48-bin projections to
-- the hash-bound archive inventory. No JSON PASS/count field is an input.
theorem proposed_stripInventoryCheck : stripInventoryCheck=true := by
  decide

theorem stripCrosses_mem_inventory (s : Fin 186) (ix iy : Fin 48)
    (hc : stripCrosses s ix iy) : (ix,iy)∈rawProjectedPairs := by
  have hall : ∀ s : Fin 186,∀ ix iy : Fin 48,
      stripCrosses s ix iy→(ix,iy)∈rawProjectedPairs :=
    of_decide_eq_true proposed_stripInventoryCheck
  exact hall s ix iy hc

noncomputable section
open Set
open scoped Classical

theorem nativeXLo_cast (i : Fin 48) :
    (nativeXLo i : ℝ)=logPrimeMeshPoint (h : ℝ) (d : ℝ) 47 i := by
  norm_num [nativeXLo,logPrimeMeshPoint,logPrimeMeshStep] <;> ring

theorem nativeXHi_cast (i : Fin 48) :
    (nativeXHi i : ℝ)=logPrimeMeshPoint (h : ℝ) (d : ℝ) 47 (i.val+1) := by
  norm_num [nativeXHi,logPrimeMeshPoint,logPrimeMeshStep] <;> ring

theorem nativeYLo_cast (i : Fin 48) :
    (nativeYLo i : ℝ)=logPrimeMeshPoint (a : ℝ) (h : ℝ) 47 i := by
  norm_num [nativeYLo,logPrimeMeshPoint,logPrimeMeshStep] <;> ring

theorem nativeYHi_cast (i : Fin 48) :
    (nativeYHi i : ℝ)=logPrimeMeshPoint (a : ℝ) (h : ℝ) 47 (i.val+1) := by
  norm_num [nativeYHi,logPrimeMeshPoint,logPrimeMeshStep] <;> ring

-- No ordering wall is discarded: a point equal to a native lower face
-- still lies strictly below that cell's upper face and gives strict cross
-- inequalities with the OPEN pair512 rectangle containing that point.
theorem actual_fibre_point_stripCrosses (r : Row) {j : NativeIndex}
    {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w)
    (hj : (![t,u,z,w] : Fin 4→ℝ)∈nativeCell j) :
    stripCrosses r.1 (j 0) (j 1) := by
  have htN : (nativeXLo (j 0) : ℝ)≤t ∧ t<(nativeXHi (j 0) : ℝ) := by
    rw [nativeXLo_cast,nativeXHi_cast]
    simpa [nativeCell,nativeLower,nativeUpper] using (mem_logPrimeBox.mp hj 0)
  have huN : (nativeYLo (j 1) : ℝ)≤u ∧ u<(nativeYHi (j 1) : ℝ) := by
    rw [nativeYLo_cast,nativeYHi_cast]
    simpa [nativeCell,nativeLower,nativeUpper] using (mem_logPrimeBox.mp hj 1)
  have ht : (tLower (326+r.1.val) : ℝ)<t ∧ t<(tUpper (326+r.1.val) : ℝ) := by
    simpa only [indices] using And.intro hs.1 hs.2.1
  have hfirst : firstU r.1≤(indices r).2 := by simp [indices]
  have hUQ : uLower (firstU r.1)≤uLower (indices r).2 := by
    have hcast : (firstU r.1 : ℚ)≤((indices r).2 : ℚ) := by exact_mod_cast hfirst
    norm_num [uLower,a,h]
    linarith only [hcast]
  have hUR : (uLower (firstU r.1) : ℝ)≤(uLower (indices r).2 : ℝ) := by
    exact_mod_cast hUQ
  have huL : (uLower (firstU r.1) : ℝ)<u := hUR.trans_lt hs.2.2.1
  obtain ⟨_,_,_,huH,_,_,_⟩ := row_fibre_argument r hs
  unfold stripCrosses
  refine ⟨?_,?_,?_,?_⟩
  · have hh : (tLower (326+r.1.val) : ℝ)<(nativeXHi (j 0) : ℝ) := ht.1.trans htN.2
    exact_mod_cast hh
  · have hh : (nativeXLo (j 0) : ℝ)<(tUpper (326+r.1.val) : ℝ) := htN.1.trans_lt ht.2
    exact_mod_cast hh
  · have hh : (uLower (firstU r.1) : ℝ)<(nativeYHi (j 1) : ℝ) := huL.trans huN.2
    exact_mod_cast hh
  · have hh : (nativeYLo (j 1) : ℝ)<(h : ℝ) := huN.1.trans_lt huH
    exact_mod_cast hh

-- Every actual native owner of a fibre point lies in the ORIGINAL combined
-- E0/E1 projected-parent inventory, rather than a fresh optimized mask.
theorem actual_fibre_native_projection_mem (r : Row) {j : NativeIndex}
    {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w)
    (hj : (![t,u,z,w] : Fin 4→ℝ)∈nativeCell j) :
    (j 0,j 1)∈rawProjectedPairs :=
  stripCrosses_mem_inventory r.1 (j 0) (j 1) (actual_fibre_point_stripCrosses r hs hj)

-- Compose actual point geometry with the Phase3 proposed complete ordered
-- key lookup. The saved method/positive-floor/priority facts remain guarded
-- by Phase3's closed UNEXECUTED proposal, not by an hOwner assumption.
theorem actual_fibre_point_has_archived_saved_parent (r : Row)
    {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w) :
    ∃ p∈archivedRows, (![t,u,z,w] : Fin 4→ℝ)∈nativeCell (rowNativeIndex p) ∧
      p.method=0 ∧ 0<p.floorQ ∧ p.ordinal∉priorityOrdinals := by
  obtain ⟨j,hj,_hunique⟩ := actual_v2_unique_native_parent r hs
  have hxy := actual_fibre_native_projection_mem r hs hj.1
  obtain ⟨p,hp,hx,hy,hz,hw⟩ := projected_key_has_actual_saved_record
    (j 0,j 1) hxy (j 2) (j 3) hj.2.1 hj.2.2
  have hpF : p∈archivedRows := List.mem_toFinset.mpr hp
  have hkey : rowNativeIndex p=j := by
    funext i
    fin_cases i <;> simp [rowNativeIndex,hx,hy,hz,hw]
  obtain ⟨hm,hpos,hprior,_⟩ := archived_row_is_positive_unreplaced_method0 p hpF
  refine ⟨p,hpF,?_,hm,hpos,hprior⟩
  simpa only [hkey] using hj.1

-- Saved records need not be called unique here. Their GEOMETRIC native
-- index is unique at each point, independently of archive parser identity.
theorem archived_parents_same_geometric_owner {p q : SourceRow} {x : Fin 4→ℝ}
    (hp : x∈nativeCell (rowNativeIndex p)) (hq : x∈nativeCell (rowNativeIndex q)) :
    rowNativeIndex p=rowNativeIndex q := nativeCell_unique hp hq

end
end ImbalancedChen.OriginalPairedV2ArchivedProjectionContainment