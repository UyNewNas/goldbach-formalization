import ImbalancedChen.Part5OriginalH430ClassicalRadialTupleCount

/-! Exact native rank-by-rank prime vectors for the original clamp.
A bounded coordinate used off support agrees with every true prime on
support. The 20 original word occurrences stay outside the rank split. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRadialMarkedRanks
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedNonunitLabelGeometry (label_data)
open P2SeedOmegaLiteralFibre (a0)
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum)
open Part5OriginalH430ClassicalSmallSwitchedIntegers (testWeight)
open Part5OriginalH430ClassicalFixedClampMarks
open Part5OriginalH430ClassicalFixedClampGeometry
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalRadialTupleCount (bandTuples)
open scoped Classical Topology BigOperators

def rankMarks (N : ℕ) (ν κ : ℝ) (cs : List ℕ) (k : ℕ) :=
  (marks 1 N ν κ cs).filter (fun u => (expanded u).length=k)

def slot (N k : ℕ) (u : Mark) (i : Fin k) : Fin (2*N+1) :=
  ⟨min ((expanded u).getD i.val 0) (2*N),Nat.lt_succ_of_le (min_le_right _ _)⟩

def vectors (N : ℕ) (ν κ : ℝ) (cs : List ℕ) (k : ℕ) :=
  (rankMarks N ν κ cs k).image (slot N k)

/-- The genuine slot floor has room for a factor-two smoothing transition. -/
theorem prime_floor {N : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark} (j : Fin 13)
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hu : u∈marks 1 N ν κ cs) : ∀ q∈expanded u,(N:ℝ)^(1/90:ℝ)≤(q:ℝ) := by
  obtain ⟨hp,hqs,_⟩ := flags.mp hu
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hg := expanded_geometry j hc hN hν hν' hk hu
  have hscale := (platform hN hν hp).1
  let qs := u.2.1
  have hfloor (q : ℕ) (h : q∈qs) : (N:ℝ)^(1/90:ℝ)≤(q:ℝ) := by
    calc
      _ ≤ (N:ℝ)^((7/128)*a0) := rpow_le_rpow_of_exponent_le hNr.le (by norm_num [a0])
      _ ≤ ((N:ℝ)^ν/(u.1:ℝ))^a0 := by
        rw [rpow_mul h0.le]
        exact rpow_le_rpow (rpow_nonneg h0.le _) hscale (by norm_num [a0])
      _ ≤ _ := (mem_primeWindow.mp ((label_data hqs).2.2.1 q h)).2.2.1
  have hcs : 3≤cs.length := by
    fin_cases j <;> norm_num [secondFunctionalMotherGammaWords] at hc <;> aesop
  have hl : qs.length=cs.length := (label_data hqs).1
  have hi : qs.length-2<qs.length := by omega
  have hpen : qs.getD (qs.length-2) 0∈qs := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · rcases List.mem_cons.mp h with he | hq
    · rw [he]
      exact (rpow_le_rpow_of_exponent_le hNr.le (by norm_num [clampStart] : (1/90:ℝ)≤clampStart)).trans
        (mem_primeWindow.mp hp).2.2.1
    · exact hfloor _ hq
  · exact (hfloor _ hpen).trans (by exact_mod_cast hg.2.1 q h)

theorem transition_floor :
    ∀ᶠ N : ℕ in atTop,cut N≤(N:ℝ)^(1/90:ℝ)/2 := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/90-1/96)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop 2,eventually_gt_atTop (0:ℕ)] with N h2 hN
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hh := mul_le_mul_of_nonneg_left h2 (rpow_nonneg h0.le (1/96:ℝ))
  rw [←rpow_add h0,show (1/96:ℝ)+(1/90-1/96)=1/90 by ring] at hh
  exact (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr hh

private theorem slot_value {N k : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark} (j : Fin 13)
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hu : u∈rankMarks N ν κ cs k) (i : Fin k) :
    (slot N k u i).val=(expanded u).getD i.val 0 ∧ (slot N k u i).val∈expanded u := by
  obtain ⟨hm,hl⟩ := mem_filter.mp hu
  have hi : i.val<(expanded u).length := hl.symm ▸ i.isLt
  let q := (expanded u).getD i.val 0
  have hq : q∈expanded u := by
    dsimp only [q]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hprod := (expanded_geometry j hc hN hν hν' hk hm).2.2.1
  have hgeom := prefix_data hN hν hm
  have hdiv : q∣product u := hprod ▸ List.dvd_prod hq
  have hle : q≤N := (Nat.le_of_dvd hgeom.2.2.2.2.1 hdiv).trans hgeom.2.2.2.2.2.1
  have he : (slot N k u i).val=q := min_eq_left (by omega)
  exact ⟨he,by rw [he]; exact hq⟩

theorem vector_spec {N k : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark} (j : Fin 13)
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hu : u∈rankMarks N ν κ cs k) :
    List.ofFn (fun i : Fin k => (slot N k u i).val)=expanded u ∧
      slot N k u∈Part3.labelledPrimeTuples k (2*N) ∧
      Part3.labelledProduct (slot N k u)=product u ∧
      ∀ i : Fin k,(N:ℝ)^(1/90:ℝ)≤((slot N k u i).val:ℝ) := by
  obtain ⟨hm,hl⟩ := mem_filter.mp hu
  have hh := slot_value j hc hN hν hν' hk hu
  have hg := expanded_geometry j hc hN hν hν' hk hm
  have hlist : List.ofFn (fun i : Fin k => (slot N k u i).val)=expanded u := by
    apply HighNonunit.list_eq_of_getD (by simp : (List.ofFn (fun i : Fin k => (slot N k u i).val)).length=k) hl
    funext i
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]
    exact (hh i).1
  refine ⟨hlist,mem_filter.mpr ⟨mem_univ _,fun i => (hg.2.2.2.1 _ (hh i).2).1⟩,?_,
    fun i => prime_floor j hc hN hν hν' hk hm _ (hh i).2⟩
  have he := congrArg List.prod hlist
  rw [List.prod_ofFn,hg.2.2.1] at he
  exact he

private theorem slot_injective {N k : ℕ} {ν κ : ℝ} {cs : List ℕ} (j : Fin 13)
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112) :
    Set.InjOn (slot N k) (rankMarks N ν κ cs k : Set Mark) := by
  rintro ⟨p,qs,m⟩ hu ⟨p',qs',m'⟩ hv he
  have hs := vector_spec j hc hN hν hν' hk hu
  have hs' := vector_spec j hc hN hν hν' hk hv
  have hL := hs.1.symm.trans ((congrArg (fun t : Fin k → Fin (2*N+1) =>
    List.ofFn (fun i => (t i).val)) he).trans hs'.1)
  have hl := (prefix_data hN hν (mem_filter.mp hu).1).1
  have hl' := (prefix_data hN hν (mem_filter.mp hv).1).1
  have take {u : Mark} (h : (letters u).length=cs.length+1) :
      (expanded u).take (cs.length+1)=letters u := by
    rw [←h,expanded] <;> simp
  have hpairs := congrArg (List.take (cs.length+1)) hL
  rw [take hl,take hl'] at hpairs
  change p::qs=p'::qs' at hpairs
  obtain ⟨he_p,he_q⟩ := List.cons.inj hpairs
  subst p'
  subst qs'
  have ho := (congrArg Part3.labelledProduct he)
  rw [hs.2.2.1,hs'.2.2.1] at ho
  have hem := Nat.eq_of_mul_eq_mul_left (prefix_data hN hν (mem_filter.mp hu).1).2.1 ho
  subst m'
  rfl

/-- One exact finite native rank sum per original occurrence. No division
by permutations or by the number of colour labels. -/
theorem native_rank_count {N : ℕ} {ν κ : ℝ} (hN : 1<N) (hν : 1/3+7/128≤ν)
    (hν' : ν≤1/2) (hk : κ≤1/112) (tested : Bool) :
    count tested 1 N ν κ=wordsSum (fun cs => ∑ k∈range 201,∑ t∈vectors N ν κ cs k,
      testWeight tested N 1 (Part3.labelledProduct t)) := by
  apply sum_congr rfl
  intro j _
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs hc
  let S := marks 1 N ν κ cs
  let W := fun u : Mark => testWeight tested N (u.1*u.2.1.prod) u.2.2
  have hF := sum_fiberwise_of_maps_to (s:=S) (t:=range 201) (g:=fun u => (expanded u).length)
    (fun u hu => mem_range.mpr (by have h:=(expanded_geometry j hc hN hν hν' hk hu).2.2.2.2.2; omega)) W
  change (∑ u∈S,W u)=_
  rw [←hF]
  apply sum_congr rfl
  intro k _
  rw [vectors,sum_image (slot_injective j hc hN hν hν' hk)]
  apply sum_congr rfl
  intro u hu
  have hM := (vector_spec j hc hN hν hν' hk hu).2.2.1
  rw [hM]
  cases tested <;> simp [W,testWeight,product]

end
end ImbalancedChen.Part5OriginalH430ClassicalRadialMarkedRanks
