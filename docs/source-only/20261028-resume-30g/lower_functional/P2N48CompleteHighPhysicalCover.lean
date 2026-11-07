import ImbalancedChen.P2N48PriorityHalfGridDictionary

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual high U11 domain coverage by all original n48 geometric keys.
The geometry carrier has placeholder method/floor fields; it is NOT the
original payload and supplies NO saving. A peer literal rowAtKey must be
attached by independent field identities before any numerical use.
No finite coverage checker is invoked: real floor inequalities prove cover.
-/
namespace ImbalancedChen.P2N48CompleteHighPhysicalCover
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P5Z.U11Canonical P5Z.U1011OriginalSixteenU10Geometry

abbrev HighKey := Fin 48×Fin 48×Fin 48×Fin 48

def highGeometryRow (k : HighKey) : SourceRow :=
  ⟨highOrdinalOfKey (1,k.1,k.2.1,k.2.2.1,k.2.2.2),1,
    k.1,k.2.1,k.2.2.1,k.2.2.2,0,0⟩

def highKeyOrdered (k : HighKey) : Prop := k.2.2.2≤k.2.2.1 ∧ k.2.2.1≤k.2.1

instance (k : HighKey) : Decidable (highKeyOrdered k) := by
  unfold highKeyOrdered
  infer_instance

def highKeys : Finset HighKey := Finset.univ.filter highKeyOrdered
def highGeometryRows : Finset SourceRow := highKeys.image highGeometryRow

private theorem original_grid_interval_cover (A D : ℕ) (hD : 0<D) {x : ℝ}
    (hx : (A : ℝ)/240000≤x ∧ x<((A+48*D : ℕ) : ℝ)/240000) :
    ∃ i : Fin 48,((A+D*i.val : ℕ) : ℝ)/240000≤x ∧
      x<((A+D*i.val+D : ℕ) : ℝ)/240000 := by
  let X : ℝ := (240000*x-A)/D
  let k : ℤ := ⌊X⌋
  have hDr : (0 : ℝ)<D := by exact_mod_cast hD
  have hX0 : 0≤X := by dsimp [X]; apply div_nonneg <;> linarith [hx.1]
  have hX48 : X<48 := by
    apply (div_lt_iff₀ hDr).2
    have hh := hx.2
    push_cast at hh
    dsimp [X]
    linarith
  have hk0 : 0≤k := Int.floor_nonneg.mpr hX0
  have hkL : (k : ℝ)≤X := Int.floor_le X
  have hkU : X<(k : ℝ)+1 := Int.lt_floor_add_one X
  have hk48 : k<48 := by exact_mod_cast hkL.trans_lt hX48
  have hkN : k.toNat<48 := by omega
  let i : Fin 48 := ⟨k.toNat,hkN⟩
  have hcast : (i.val : ℝ)=(k : ℝ) := by
    dsimp [i]
    exact_mod_cast Int.toNat_of_nonneg hk0
  refine ⟨i,?_,?_⟩
  · have h := (le_div_iff₀ hDr).mp hkL
    dsimp [X] at h
    push_cast
    rw [hcast]
    linarith
  · have h := (div_lt_iff₀ hDr).mp hkU
    dsimp [X] at h
    push_cast
    rw [hcast]
    linarith

private theorem low_grid_index_order (i j : Fin 48) {x y : ℝ}
    (hx : ((20016+343*i.val : ℕ) : ℝ)/240000≤x ∧
      x<((20016+343*i.val+343 : ℕ) : ℝ)/240000)
    (hy : ((20016+343*j.val : ℕ) : ℝ)/240000≤y ∧
      y<((20016+343*j.val+343 : ℕ) : ℝ)/240000)
    (hyx : y<x) : j≤i := by
  by_contra hn
  have hij : i.val+1≤j.val := by omega
  have hNat : 20016+343*i.val+343≤20016+343*j.val := by omega
  have hSep : ((20016+343*i.val+343 : ℕ) : ℝ)/240000≤
      ((20016+343*j.val : ℕ) : ℝ)/240000 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hNat) (by norm_num)
  linarith only [hx.2,hy.1,hSep,hyx]

/-- Genuine physical coverage, including arbitrary points on grid walls.
The half-open convention chooses one original bin without discarding it. -/
theorem actual_high_domain_has_grid_key {v : LogFour} (hv : v∈originalDomain actualMask) :
    ∃ k∈highKeys,v∈selectedParent (highGeometryRow k) actualMask := by
  obtain ⟨ha,h32,h21,h1,h0l,h0u,hm⟩ := hv
  have hu0 : (20016 : ℝ)/240000≤v 1 := by linarith
  have hz0 : (20016 : ℝ)/240000≤v 2 := by linarith
  have hw0 : (20016 : ℝ)/240000≤v 3 := by norm_num at ha ⊢; linarith
  have hu1 : v 1<((20016+48*343 : ℕ) : ℝ)/240000 := by norm_num; linarith
  have hz1 : v 2<((20016+48*343 : ℕ) : ℝ)/240000 := by norm_num; linarith
  have hw1 : v 3<((20016+48*343 : ℕ) : ℝ)/240000 := by norm_num; linarith
  obtain ⟨it,ht⟩ := original_grid_interval_cover 36480 420 (by omega)
    (show (36480 : ℝ)/240000≤v 0 ∧ v 0<((36480+48*420 : ℕ) : ℝ)/240000 by
      norm_num; exact ⟨h0l,h0u⟩)
  obtain ⟨iu,hu⟩ := original_grid_interval_cover 20016 343 (by omega) ⟨hu0,hu1⟩
  obtain ⟨iz,hz⟩ := original_grid_interval_cover 20016 343 (by omega) ⟨hz0,hz1⟩
  obtain ⟨iw,hw⟩ := original_grid_interval_cover 20016 343 (by omega) ⟨hw0,hw1⟩
  let k : HighKey := (it,iu,iz,iw)
  have hk : highKeyOrdered k :=
    ⟨low_grid_index_order iz iw hz hw h32,low_grid_index_order iu iz hu hz h21⟩
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩,?_,?_⟩
  · apply mem_logPrimeBox.mpr
    intro j
    fin_cases j
    · simpa [highGeometryRow,k,nativeBox,leftEnd,rightEnd,width,lowLo,highLo] using ht
    · simpa [highGeometryRow,k,nativeBox,leftEnd,rightEnd,width,lowLo,highLo] using hu
    · simpa [highGeometryRow,k,nativeBox,leftEnd,rightEnd,width,lowLo,highLo] using hz
    · simpa [highGeometryRow,k,nativeBox,leftEnd,rightEnd,width,lowLo,highLo] using hw
  · simpa [highGeometryRow] using
      (show v∈originalDomain actualMask from ⟨ha,h32,h21,h1,h0l,h0u,hm⟩)

theorem complete_high_selected_union : selectedUnion highGeometryRows=originalDomain actualMask := by
  ext v
  constructor
  · intro hv
    obtain ⟨r,hr⟩ := mem_iUnion.mp hv
    obtain ⟨hrRows,hrv⟩ := mem_iUnion.mp hr
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hrRows
    simpa [selectedParent,highGeometryRow] using hrv.2
  · intro hv
    obtain ⟨k,hk,hkv⟩ := actual_high_domain_has_grid_key hv
    exact mem_iUnion.mpr ⟨highGeometryRow k,mem_iUnion.mpr
      ⟨Finset.mem_image.mpr ⟨k,hk,rfl⟩,hkv⟩⟩

theorem complete_high_distinct_keys : DistinctGeometricKeys highGeometryRows := by
  intro r hr s hs hkey
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hs
  have hkl : k=l := by
    simpa only [rowKey,highGeometryRow] using congrArg Prod.snd hkey
  exact congrArg highGeometryRow hkl

theorem complete_high_uncovered_is_low : uncoveredDomain highGeometryRows=domain10 := by
  rw [uncoveredDomain,complete_high_selected_union]
  ext v
  constructor
  · rintro ⟨hv,hnot⟩
    exact hv.elim id (fun h => False.elim (hnot h))
  · intro hv
    exact ⟨Or.inl hv,fun hh => Set.disjoint_left.mp
      (domain10_disjoint_originalDomain actualMask) hv hh⟩

theorem whole_actual_coefficient_complete_high_grid :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient=
      (∑ r∈highGeometryRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask))+
        ∫ v in domain10,actualKernel v := by
  rw [actualSelectedCoefficient_eq_rows_add_uncovered highGeometryRows complete_high_distinct_keys]
  unfold uncoveredCost
  rw [complete_high_uncovered_is_low]

end
end ImbalancedChen.P2N48CompleteHighPhysicalCover
