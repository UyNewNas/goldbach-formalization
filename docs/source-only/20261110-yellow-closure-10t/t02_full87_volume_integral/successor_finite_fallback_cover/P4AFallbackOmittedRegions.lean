import ImbalancedChen.P4AFallbackJointFiniteCover

/-! SOURCE_ONLY / UNCOMPILED.
Unresolved canonical boxes are inherited. The second uncovered set is
contained in its ORIGINAL omitted trim strip. The third uncovered TRUE
physical kernel is paid by the ORIGINAL total-testIntegral trim loss;
its existing weighted integral limit is reused, not reproved.
Actual prime-strip lifting, policy changes and compiler payment belong
to the downstream transport and are not identified with these integrals.
-/
namespace ImbalancedChen.P4AFallbackOmittedRegions
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P4AFallbackCanonicalBanks P4AFallbackOriginalCompactTrims P4AFallbackJointFiniteCover
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P4AOriginalThirdFallbackArchive (Cell)
open P4AOriginalThirdFallbackChartIntegral (kernel)
open P4AOriginalThirdFallbackJacobian (region)
open P4AOriginalThirdFallbackRegions (region_guard region_measurable)
open P4AOriginalThirdFallbackPrimeTests

def covered2 (m : ℕ) : Set (Point 2) := ⋃ j : Label 2 m,⋃ _h : good2 m j,
  logPrimeMeshCell 0 (19/96) m j
def covered3 (m : ℕ) : Set (Point 3) := ⋃ j : Label 3 m,⋃ _h : good3 m j,
  logPrimeMeshCell 0 (19/96) m j

theorem covered3_measurable (m : ℕ) : MeasurableSet (covered3 m) :=
  MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => measurableSet_logPrimeMeshCell 0 (19/96) m j))
theorem covered2_measurable (m : ℕ) : MeasurableSet (covered2 m) :=
  MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => measurableSet_logPrimeMeshCell 0 (19/96) m j))

theorem mem_covered2_iff (m : ℕ) (t : Point 2) : t∈covered2 m ↔ ∃ c : ℚ,read m (bank m).second t=some c := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    obtain ⟨hg,ht⟩ := mem_iUnion.mp hj
    exact ⟨level2 m j,read_some_iff.mpr ⟨j,ht,(second_some_iff m j _).mpr ⟨hg,rfl⟩⟩⟩
  · rintro ⟨c,hc⟩
    obtain ⟨j,ht,hj⟩ := read_some_iff.mp hc
    have hg := ((second_some_iff m j c).mp hj).1
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hg,ht⟩⟩

theorem mem_covered3_iff (m : ℕ) (t : Point 3) : t∈covered3 m ↔ ∃ c : ℚ,read m (bank m).third t=some c := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    obtain ⟨hg,ht⟩ := mem_iUnion.mp hj
    exact ⟨level3 m j,read_some_iff.mpr ⟨j,ht,(third_some_iff m j _).mpr ⟨hg,rfl⟩⟩⟩
  · rintro ⟨c,hc⟩
    obtain ⟨j,ht,hj⟩ := read_some_iff.mp hc
    have hg := ((third_some_iff m j c).mp hj).1
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hg,ht⟩⟩

/-- No extra unresolved second points are created inside the original
compact trim. Its already-paid boundary strip is the only uncovered set.
-/
theorem second_uncovered_outside_original_trim (delta : ℝ) (hd : 0<delta) :
    ∃ m0 : ℕ,2≤m0 ∧ ∀ m : ℕ,m0≤m → ∀ t : Point 2,t∉covered2 m →
      (t 0,t 1)∉P4AOriginalSecondResidualSupplier.trimmedRegion delta := by
  obtain ⟨m0,hm0,hM⟩ := exists_second_core_owners delta hd
  refine ⟨m0,hm0,?_⟩
  intro m hm t hn ht
  have hK : t∈secondCore delta := by
    refine ⟨(t 0,t 1),ht,?_⟩
    funext i
    fin_cases i <;> rfl
  obtain ⟨j,hj,_⟩ := hM m hm t hK
  exact hn ((mem_covered2_iff m t).mpr ⟨level2 m j,read_some_iff.mpr ⟨j,hj.1,hj.2⟩⟩)

theorem thirdCore_covered (r : ℕ) :
    ∃ m0 : ℕ,2≤m0 ∧ ∀ m : ℕ,m0≤m → thirdCore r⊆covered3 m := by
  obtain ⟨m0,hm0,hM⟩ := exists_third_core_owners r
  refine ⟨m0,hm0,?_⟩
  intro m hm t ht
  obtain ⟨j,hj,_⟩ := hM m hm t ht
  exact (mem_covered3_iff m t).mpr ⟨level3 m j,read_some_iff.mpr ⟨j,hj.1,hj.2⟩⟩

theorem test_zero_outside_covered (r m : ℕ) (hcover : thirdCore r⊆covered3 m)
    (t : Point 3) (ht : t∉covered3 m) (c : Cell) : test r c t=0 := by
  have hcombined : combined r t=0 := Classical.byContradiction (fun h => ht (hcover (third_combined_support r t h)))
  have hle : test r c t≤combined r t :=
    Finset.single_le_sum (fun d _ => (test_bounds r d t).1) (Finset.mem_univ c)
  rw [hcombined] at hle
  exact le_antisymm hle (test_bounds r c t).1

private theorem region_subset_cube (c : Cell) : region c⊆cube :=
  fun _ ht => guard_cube (region_guard ht)

theorem integrable_kernel_region (c : Cell) : IntegrableOn kernel (region c) := by
  have h := (integrableOn_logPrimeBox_test_cube cut_pos profile continuous_profile.continuousOn).mono_set (region_subset_cube c)
  apply h.congr
  filter_upwards [ae_restrict_mem (region_measurable c)] with t ht
  exact kernel_density (region_guard ht)

private theorem cellTestIntegral_eq_region (r : ℕ) (c : Cell) :
    cellTestIntegral r c=∫ t in region c,test r c t*(∏ i,1/t i) := by
  let f := fun t : Point 3 => test r c t*(∏ i,1/t i)
  have he : f=(region c).indicator f := by
    funext t
    by_cases ht : t∈region c
    · exact (indicator_of_mem ht f).symm
    · have hz : test r c t=0 := Classical.byContradiction (fun hn => ht (region_of_ne hn))
      simp [f,ht,hz]
  calc
    cellTestIntegral r c=∫ t in cube,(region c).indicator f t := by
      change (∫ t in cube,f t)=_
      rw [←he]
    _ = ∫ t in region c,f t := by
      rw [setIntegral_indicator (region_measurable c),inter_eq_right.mpr (region_subset_cube c)]

def lostThird (m : ℕ) : ℝ := ∑ c : Cell,∫ t in region c\covered3 m,kernel t

/-- Actual physical omitted-kernel mass. The old continuous trim pays
the entire omission because its support lies in the retained finite bank.
-/
theorem lostThird_le_old_trim (r m : ℕ) (hcover : thirdCore r⊆covered3 m) :
    lostThird m≤total-testIntegral r := by
  have hrow (c : Cell) :
      (∫ t in region c\covered3 m,kernel t)≤(∫ t in region c,kernel t)-cellTestIntegral r c := by
    have hk := integrable_kernel_region c
    have ht := (integrableOn_logPrimeBox_test_cube cut_pos (test r c) (continuous_test r c).continuousOn).mono_set (region_subset_cube c)
    have hleft := hk.indicator ((covered3_measurable m).compl)
    have hpoint (t : Point 3) (hp : t∈region c) :
        ((covered3 m)ᶜ).indicator kernel t≤kernel t-test r c t*(∏ i,1/t i) := by
      have hpos (i : Fin 3) : 0<t i := cut_pos.trans_le (mem_logPrimeBox.mp (guard_cube (region_guard hp)) i).1
      have hd : 0≤∏ i : Fin 3,1/t i := Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hpos i)).le)
      have hbound := mul_le_mul_of_nonneg_right (test_bounds r c t).2 hd
      rw [kernel_density (region_guard hp)] at hbound
      by_cases hcov : t∈covered3 m
      · rw [indicator_of_notMem (by simpa using hcov)]
        linarith
      · rw [indicator_of_mem (by simpa using hcov),test_zero_outside_covered r m hcover t hcov c,zero_mul,sub_zero]
    have hb := integral_mono_ae hleft (hk.sub ht) (by
      filter_upwards [ae_restrict_mem (region_measurable c)] with t hp
      exact hpoint t hp)
    have he : (∫ t in region c,((covered3 m)ᶜ).indicator kernel t)=∫ t in region c\covered3 m,kernel t := by
      change (∫ t in region c,((covered3 m)ᶜ).indicator kernel t)=
        ∫ t in region c∩(covered3 m)ᶜ,kernel t
      exact setIntegral_indicator ((covered3_measurable m).compl)
    rw [he,integral_sub hk ht,←cellTestIntegral_eq_region r c] at hb
    exact hb
  have hsum : (∑ c : Cell,cellTestIntegral r c)=testIntegral r := by
    unfold testIntegral combined cellTestIntegral
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun c _ => integrableOn_logPrimeBox_test_cube cut_pos (test r c)
      (continuous_test r c).continuousOn)]
  calc
    lostThird m≤∑ c : Cell,((∫ t in region c,kernel t)-cellTestIntegral r c) := Finset.sum_le_sum (fun c _ => hrow c)
    _ = total-testIntegral r := by rw [Finset.sum_sub_distrib,hsum];rfl

/-- The original integral_limit selects the trim first; one finite
family is then frozen before omega, compiler precision and the target.
-/
theorem exists_arbitrarily_small_third_omission (epsilon : ℝ) (heps : 0<epsilon)
    (mMin : ℕ) :
    ∃ r m0 : ℕ,mMin≤m0 ∧ ∀ m : ℕ,m0≤m → lostThird m<epsilon := by
  obtain ⟨r,hr⟩ := (Metric.tendsto_nhds.mp integral_limit epsilon heps).exists
  have herror : total-testIntegral r<epsilon := by
    rw [Real.dist_eq] at hr
    have hh := (abs_lt.mp hr).1
    linarith
  obtain ⟨m0,_,hM⟩ := thirdCore_covered r
  refine ⟨r,max mMin m0,le_max_left _ _,?_⟩
  intro m hm
  exact (lostThird_le_old_trim r m (hM m ((le_max_right _ _).trans hm))).trans_lt herror

end
end ImbalancedChen.P4AFallbackOmittedRegions
