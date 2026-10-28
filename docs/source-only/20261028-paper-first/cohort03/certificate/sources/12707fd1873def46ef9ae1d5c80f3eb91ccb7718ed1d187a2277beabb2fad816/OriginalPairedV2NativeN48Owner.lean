import ImbalancedChen.LogPrimeBoxMesh
import ImbalancedChen.Certificates.PairedV2FullMaskGeometry

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Genuine anisotropic ORIGINAL n48 U11 parent coordinates, NOT the later
-- uniform rational-grid surrogate. The first slot uses [h,d), the other
-- slots use [a,h). Common faces have one half-open owner; tied inner bins
-- are retained. This does not identify a parent with its saved witness row,
-- certify method0/priority exclusion, or recover upper22 history payloads.
namespace ImbalancedChen.OriginalPairedV2NativeN48Owner
noncomputable section
open Set
open scoped Classical
open Certificates.PairedV2
open Certificates.PairedV2.FullMask

abbrev NativeIndex := Fin 4 → Fin 48

def nativeLower (i : Fin 4) : ℝ := if i=0 then (h : ℝ) else (a : ℝ)
def nativeUpper (i : Fin 4) : ℝ := if i=0 then (d : ℝ) else (h : ℝ)

def nativeCell (j : NativeIndex) : Set (Fin 4 → ℝ) :=
  logPrimeBox (fun i => logPrimeMeshPoint (nativeLower i) (nativeUpper i) 47 (j i))
    (fun i => logPrimeMeshPoint (nativeLower i) (nativeUpper i) 47 ((j i).val+1))

theorem nativeLower_lt_nativeUpper (i : Fin 4) : nativeLower i<nativeUpper i := by
  fin_cases i <;> norm_num [nativeLower,nativeUpper,a,h,d]

-- Explicit interval construction gives an owner without an hOwner premise.
theorem exists_nativeCell {x : Fin 4 → ℝ}
    (hx : ∀ i, nativeLower i≤x i ∧ x i<nativeUpper i) :
    ∃ j : NativeIndex,x∈nativeCell j := by
  choose j hj using fun i => exists_logPrimeMeshInterval
    (nativeLower i) (nativeUpper i) 47 (hx i)
  exact ⟨j,mem_logPrimeBox.mpr hj⟩

theorem nativeCell_unique {j k : NativeIndex} {x : Fin 4 → ℝ}
    (hj : x∈nativeCell j) (hk : x∈nativeCell k) : j=k := by
  funext i
  have hxj := mem_logPrimeBox.mp hj i
  have hxk := mem_logPrimeBox.mp hk i
  have hab := (nativeLower_lt_nativeUpper i).le
  rcases lt_trichotomy (j i) (k i) with hlt | heq | hgt
  · have hsep := logPrimeMeshPoint_mono hab 47
      (show (j i).val+1≤(k i).val from hlt)
    exact False.elim ((not_lt_of_ge hsep) (hxk.1.trans_lt hxj.2))
  · exact heq
  · have hsep := logPrimeMeshPoint_mono hab 47
      (show (k i).val+1≤(j i).val from hgt)
    exact False.elim ((not_lt_of_ge hsep) (hxj.1.trans_lt hxk.2))

-- Ordered exponents may belong to the SAME inner bin; no strict bin
-- inequality or fictitious permutation factor is inserted.
theorem inner_bin_order {j : NativeIndex} {x : Fin 4 → ℝ}
    (hx : x∈nativeCell j) {i k : Fin 4} (hi : i≠0) (hk : k≠0)
    (hik : x i<x k) : j i≤j k := by
  by_contra hn
  have hki : j k<j i := lt_of_not_ge hn
  have hsep := logPrimeMeshPoint_mono
    (show (a : ℝ)≤(h : ℝ) by norm_num [a,h]) 47
    (show (j k).val+1≤(j i).val from hki)
  have hxi := mem_logPrimeBox.mp hx i
  have hxk := mem_logPrimeBox.mp hx k
  simp only [nativeLower,nativeUpper,if_neg hi,if_neg hk] at hxi hxk
  exact (not_lt_of_ge hsep) ((hxi.1.trans_lt hik).trans hxk.2)

-- The actual SAME paired mask point has one original native parent.
-- Coordinate order here is (t,u,z,w)=(p4,p3,p2,p1), exactly as the
-- archived U11 rows [term,ix,iy,iz,iw,method,floor_Q].
theorem actual_v2_unique_native_parent (r : Row) {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w) :
    ∃! j : NativeIndex, ![t,u,z,w]∈nativeCell j ∧ j 3≤j 2 ∧ j 2≤j 1 := by
  obtain ⟨haw,hwz,hzu,huh,hht,htd,_⟩ := row_fibre_argument r hs
  have hbox : ∀ i : Fin 4,nativeLower i≤(![t,u,z,w] : Fin 4→ℝ) i ∧
      (![t,u,z,w] : Fin 4→ℝ) i<nativeUpper i := by
    intro i
    fin_cases i
    · simpa [nativeLower,nativeUpper] using And.intro hht.le htd
    · simpa [nativeLower,nativeUpper] using And.intro ((haw.trans hwz).trans hzu).le huh
    · simpa [nativeLower,nativeUpper] using And.intro (haw.trans hwz).le (hzu.trans huh)
    · simpa [nativeLower,nativeUpper] using And.intro haw.le ((hwz.trans hzu).trans huh)
  obtain ⟨j,hj⟩ := exists_nativeCell hbox
  refine ⟨j,⟨hj,?_,?_⟩,?_⟩
  · exact inner_bin_order hj (by decide : (3 : Fin 4)≠0)
      (by decide : (2 : Fin 4)≠0) (by simpa using hwz)
  · exact inner_bin_order hj (by decide : (2 : Fin 4)≠0)
      (by decide : (1 : Fin 4)≠0) (by simpa using hzu)
  · intro k hk
    exact nativeCell_unique hk.1 hj

end
end ImbalancedChen.OriginalPairedV2NativeN48Owner