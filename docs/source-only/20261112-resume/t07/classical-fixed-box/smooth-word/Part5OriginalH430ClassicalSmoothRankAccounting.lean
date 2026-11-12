import ImbalancedChen.Part5OriginalH430ClassicalSmoothRankSupport

/-! Exact same coefficients in the ordinary smooth mass and in the
tested prime sum. A collar is counted on the entire rank before any
dyadic partition or individual occurrence is introduced. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothRankAccounting
noncomputable section
open Filter Finset Real Wu2008DoubleSieve
open Part5OriginalH430ClassicalSmallSwitchedIntegers (testWeight)
open Part5OriginalH430ClassicalFixedClampMarks (marks letters)
open Part5OriginalH430ClassicalFixedClampGeometry (expanded prefix_data)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalRadialTupleCount (bandTuples)
open Part5OriginalH430ClassicalRadialMarkedRanks (vectors vector_spec)
open Part5OriginalH430ClassicalProperWallMarkedOutputs (properTuples)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankSupport
open scoped Classical Topology BigOperators

def sharpRank (tested : Bool) (N : ℕ) (ν κ : ℝ) (cs : List ℕ) (k : ℕ) : ℝ :=
  ∑ t∈vectors N ν κ cs k,testWeight tested N 1 (Part3.labelledProduct t)

def smoothRank (tested : Bool) (N : ℕ) (ν δ h c : ℝ) (cs : List ℕ) (r : ℕ) : ℝ :=
  ∑ t∈Part3.labelledPrimeTuples (rank cs.length r) (2*N),
    W cs t ν δ h c*testWeight tested N 1 (Part3.labelledProduct t)

def collar (N k : ℕ) (ν δ h c : ℝ) : ℝ :=
  ((bandTuples N k (1-2*h) (1+2*h)).card:ℝ)+((properTuples N k ν δ).card:ℝ)+
    ((bandTuples N k 0 c).card:ℝ)

def tails (s : ℕ) := (range 201).filter (fun r => rank s r≤200)

theorem restore_ranks (tested : Bool) {N : ℕ} {ν κ : ℝ} (hN : 1<N)
    (hν : 1/3+7/128≤ν) (cs : List ℕ) :
    (∑ r∈tails cs.length,sharpRank tested N ν κ cs (rank cs.length r))=
      ∑ k∈range 201,sharpRank tested N ν κ cs k := by
  let I := (tails cs.length).image (rank cs.length)
  have hinj : Set.InjOn (rank cs.length) (tails cs.length) := by
    intro a _ b _ he
    dsimp only [rank] at he
    omega
  have hsub : I⊆range 201 := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (by have hh := (mem_filter.mp hr).2; omega)
  have hzero (k : ℕ) (hk : k∈range 201) (hkI : k∉I) : sharpRank tested N ν κ cs k=0 := by
    have hl : k<cs.length+1 := by
      by_contra! h
      apply hkI
      let r := k-(cs.length+1)
      have he : rank cs.length r=k := by dsimp only [rank,r]; omega
      have hk' := mem_range.mp hk
      exact mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_range.mpr (by dsimp only [r]; omega),by omega⟩,he⟩
    have hem : vectors N ν κ cs k=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨u,hu,_⟩ := mem_image.mp ht
      obtain ⟨hm,hlen⟩ := mem_filter.mp hu
      have hp := (prefix_data hN hν hm).1
      simp only [expanded,List.length_append,hp] at hlen
      omega
    simp [sharpRank,hem]
  calc
    _ = ∑ k∈I,sharpRank tested N ν κ cs k := (sum_image hinj).symm
    _ = _ := sum_subset hsub hzero

theorem collar_sum (N s : ℕ) (ν δ h c : ℝ) :
    (∑ r∈tails s,collar N (rank s r) ν δ h c)≤∑ k : Fin 201,collar N k.val ν δ h c := by
  let I := (tails s).image (rank s)
  have hinj : Set.InjOn (rank s) (tails s) := by
    intro a _ b _ he
    dsimp only [rank] at he
    omega
  have hsub : I⊆range 201 := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (by have hh := (mem_filter.mp hr).2; omega)
  calc
    _ = ∑ k∈I,collar N k ν δ h c := (sum_image hinj).symm
    _ ≤ ∑ k∈range 201,collar N k ν δ h c := sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => by unfold collar; positivity)
    _ = _ := by rw [Fin.sum_univ_eq_sum_range]

theorem sharp_le_smooth (tested : Bool) {N : ℕ} {ν κ δ h c : ℝ} {cs : List ℕ}
    (j : Fin 13) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hd : 0<δ) (hh : 0<h) (r : ℕ) :
    sharpRank tested N ν κ cs (rank cs.length r)≤smoothRank tested N ν δ h c cs r := by
  let k := rank cs.length r
  let V := vectors N ν κ cs k
  let S := Part3.labelledPrimeTuples k (2*N)
  have hsub : V⊆S := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ht
    exact (vector_spec j hc hN hν hν' hk hu).2.1
  calc
    _ = ∑ t∈V,W cs t ν δ h c*testWeight tested N 1 (Part3.labelledProduct t) := sum_congr rfl
      (fun t ht => by rw [original_one t j hc hN hν hν' hk hd hh ht,one_mul])
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => mul_nonneg (W_bounds cs t ν δ h c).1
      (by cases tested <;> simp only [testWeight,Bool.false_eq_true,if_false,if_true] <;> split_ifs <;> norm_num))

theorem smooth_ordinary_le {N : ℕ} {ν κ δ h c : ℝ} {cs : List ℕ}
    (j : Fin 13) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc0 : 0<c) (hc' : c≤1/8)
    (hlower : (N:ℝ)^(1-κ)≤(c/2)*(N:ℝ)) (hz : cut N≤(N:ℝ)^(1/90:ℝ)/2) (r : ℕ) :
    smoothRank false N ν δ h c cs r≤sharpRank false N ν κ cs (rank cs.length r)+
      collar N (rank cs.length r) ν δ h c := by
  let k := rank cs.length r
  let V := vectors N ν κ cs k
  let S := Part3.labelledPrimeTuples k (2*N)
  let A := bandTuples N k (1-2*h) (1+2*h)
  let P := properTuples N k ν δ
  let T := bandTuples N k 0 c
  let U := V∪A∪P∪T
  have hz0 (t) (ht : t∈S) (hu : t∉U) : W cs t ν δ h c=0 := by
    by_contra hn
    have hnot : t∉V := fun hv => hu (mem_union_left _ (mem_union_left _ (mem_union_left _ hv)))
    rcases support_outside_original t j hc hN hν hν' hk hd hh hh' hc0 hc' hlower hz ht hnot hn
      with ht | ha | hp
    · exact hu (mem_union_right _ ht)
    · exact hu (mem_union_left _ (mem_union_left _ (mem_union_right _ ha)))
    · exact hu (mem_union_left _ (mem_union_right _ hp))
  have he : (∑ t∈S.filter (·∈U),W cs t ν δ h c)=∑ t∈S,W cs t ν δ h c :=
    sum_subset (filter_subset _ _) (fun t ht hn => hz0 t ht (fun hu => hn (mem_filter.mpr ⟨ht,hu⟩)))
  have hf : S.filter (·∈U)⊆U := fun t ht => (mem_filter.mp ht).2
  have hcard : U.card≤V.card+A.card+P.card+T.card :=
    (card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _)) _)
  have hw := sum_le_sum (s:=S.filter (·∈U)) (fun t _ => (W_bounds cs t ν δ h c).2)
  simp only [sum_const,nsmul_eq_mul,mul_one] at hw
  have hh' : ((S.filter (·∈U)).card:ℝ)≤(V.card:ℝ)+((A.card:ℝ)+(P.card:ℝ)+(T.card:ℝ)) := by
    have h' : ((S.filter (·∈U)).card:ℝ)≤(V.card:ℝ)+(A.card:ℝ)+(P.card:ℝ)+(T.card:ℝ) := by
      exact_mod_cast (card_le_card hf).trans hcard
    linarith only [h']
  rw [he] at hw
  simpa only [smoothRank,sharpRank,testWeight,Bool.false_eq_true,if_false,mul_one,sum_const,
    nsmul_eq_mul,collar,k,S,V,A,P,T] using hw.trans hh'

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothRankAccounting

