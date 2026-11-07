import ImbalancedChen.P5ZU1011OriginalSixteenOscillation
import ImbalancedChen.AffinePrimeWallReserve

/-!
The SIX literal geometric source walls, with all properness and local
snap stability proved from their actual coefficients. Arbitrary moving
last-pair masks are evaluated on the original prime tuple and are never
snapped at a mesh corner. Only the source's geometric inequalities are
snapped. The actual arithmetic thin-strip reserve precedes all keep masks.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSourceGeometryMesh

open Set Filter Topology
open Classical
open U11Integral U1011OriginalSixteenOscillation
open scoped BigOperators

noncomputable section

def sourceDomain : Set LogFour := originalDomain ∅

def sourceForms : Fin 6→LogFour→L[ℝ] ℝ :=
  ![-ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 3-ContinuousLinearMap.proj 2,
    ContinuousLinearMap.proj 2-ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 1,-ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 0]

def sourceBounds : Fin 6→ℝ := ![-(417/5000:ℝ),0,0,19/125,-(19/125:ℝ),59/250]

def sourceCoefficients : Fin 6→Fin 4→ℝ :=
  ![![0,0,0,-1],![0,0,-1,1],![0,-1,1,0],![0,1,0,0],![-1,0,0,0],![1,0,0,0]]

theorem sourceForms_apply (i : Fin 6) (v : LogFour) :
    sourceForms i v=∑ j : Fin 4,sourceCoefficients i j*v j := by
  fin_cases i <;> simp [sourceForms,sourceCoefficients,Fin.sum_univ_succ] <;> ring

theorem sourceCoefficients_abs_le_one (i : Fin 6) (j : Fin 4) :
    |sourceCoefficients i j|≤1 := by
  fin_cases i <;> fin_cases j <;> norm_num [sourceCoefficients]

theorem sourceForms_ne_zero (i : Fin 6) : sourceForms i≠0 := by
  intro hz
  have he := congrArg (fun F : LogFour→L[ℝ]ℝ=>F ![1,2,3,4]) hz
  fin_cases i <;> norm_num [sourceForms] at he

def sourceGap (i : Fin 6) (v : LogFour) : ℝ := sourceForms i v-sourceBounds i

theorem sourceGap_abs_sub_le (i : Fin 6) (v w : LogFour) :
    |sourceGap i v-sourceGap i w|≤l1Delta v w := by
  have heq : sourceGap i v-sourceGap i w=
      ∑ j : Fin 4,sourceCoefficients i j*(v j-w j) := by
    simp only [sourceGap,sourceForms_apply,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ ∑ j : Fin 4,|sourceCoefficients i j*(v j-w j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ l1Delta v w := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (sourceCoefficients_abs_le_one i j) (abs_nonneg (v j-w j))

/-- Two original source walls are weak and four are strict, exactly as
in the original selector. No boundary convention is silently changed. -/
theorem mem_sourceDomain_iff (v : LogFour) :
    v∈sourceDomain ↔ ∀ i : Fin 6,
      if i=0 ∨ i=4 then sourceGap i v≤0 else sourceGap i v<0 := by
  constructor
  · rintro ⟨ha,h32,h21,hy,hxl,hxu,hm⟩ i
    fin_cases i <;> norm_num [sourceGap,sourceForms,sourceBounds] <;> linarith
  · intro h
    have h0:=h 0
    have h1:=h 1
    have h2:=h 2
    have h3:=h 3
    have h4:=h 4
    have h5:=h 5
    norm_num [sourceGap,sourceForms,sourceBounds] at h0 h1 h2 h3 h4 h5
    exact ⟨by linarith,by linarith,by linarith,by linarith,
      by linarith,by linarith,by simp⟩

def sourceStrip (delta : ℝ) : Set LogFour := primeAffineWallStrip sourceForms sourceBounds delta

private theorem scalar_relations_stable (x y : ℝ) (h : |x-y|<|x|) :
    (x<0 ↔ y<0) ∧ (x≤0 ↔ y≤0) := by
  have hx0 : x≠0 := by
    intro hx
    rw [hx,abs_zero] at h
    exact (not_lt_of_ge (abs_nonneg _)) h
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · have hy : y<0 := by
      rw [abs_of_neg hx] at h
      have hh := (abs_lt.mp h).1
      linarith
    exact ⟨⟨fun _=>hy,fun _=>hx⟩,⟨fun _=>hy.le,fun _=>hx.le⟩⟩
  · have hy : 0<y := by
      rw [abs_of_pos hx] at h
      have hh := (abs_lt.mp h).2
      linarith
    exact ⟨⟨by intro h;linarith,by intro h;linarith⟩,
      ⟨by intro h;linarith,by intro h;linarith⟩⟩

/-- Actual geometric source membership is stable off the six paid walls.
The arbitrary gainmask is absent here because it remains at the original tuple. -/
theorem sourceDomain_stable (v w : LogFour) (delta : ℝ) (hd : 0<delta)
    (hoff : v∉sourceStrip delta) (hclose : l1Delta v w≤delta/2) :
    (v∈sourceDomain ↔ w∈sourceDomain) := by
  have hrel (i : Fin 6) :
      (sourceGap i v<0 ↔ sourceGap i w<0) ∧ (sourceGap i v≤0 ↔ sourceGap i w≤0) := by
    have hsep : delta<|sourceGap i v| := by
      apply lt_of_not_ge
      intro hnear
      exact hoff ⟨i,hnear⟩
    have hosc := sourceGap_abs_sub_le i v w
    exact scalar_relations_stable _ _ (by linarith)
  rw [mem_sourceDomain_iff,mem_sourceDomain_iff]
  apply forall_congr'
  intro i
  by_cases hi : i=0 ∨ i=4
  · simpa only [if_pos hi] using (hrel i).2
  · simpa only [if_neg hi] using (hrel i).1

/-- One actual arithmetic source-strip reserve, chosen before every
moving tuple mask and every narrower width. Endpoint atoms are retained. -/
theorem exists_uniform_source_strip_reserve (epsilon : ℝ) (he : 0<epsilon) :
    ∃ delta : ℝ,0<delta ∧ ∃ N0 : ℕ,2≤N0 ∧ ∀ N : ℕ,N0≤N →
      ∀ (keep : (Fin 4→ℕ)→Prop) (d : ℝ),0≤d → d≤delta →
        (∑ p∈(actualPrimeBoxTuples N (fun _ : Fin 4=>(417/5000:ℝ))
          (fun _=>(59/250:ℝ))).filter
          (fun p=>keep p ∧ actualPrimeTupleLog N p∈sourceStrip d),
            ∏ i,1/((p i:ℝ)-1))<epsilon := by
  obtain ⟨delta,hd,N0,hN0,hpay⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0:ℝ)<417/5000) (by norm_num : (417/5000:ℝ)<59/250)
    sourceForms sourceBounds sourceForms_ne_zero epsilon he
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro N hN keep d hd0 hsmall
  apply lt_of_le_of_lt _ (hpay N hN)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hkeep,i,hi⟩:=Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,i,hi.trans hsmall⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

end

end ImbalancedChen.P5Z.U1011OriginalSourceGeometryMesh
