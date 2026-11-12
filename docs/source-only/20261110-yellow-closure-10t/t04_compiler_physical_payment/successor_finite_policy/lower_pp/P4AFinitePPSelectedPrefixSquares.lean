import ImbalancedChen.P4AFinitePPLastOddSupport
import ImbalancedChen.P5ZU1011OriginalFifteenJointSelectedSupport
import ImbalancedChen.P5SelectedRealEndpointSupport
import Mathlib.Data.Finset.Sort

namespace ImbalancedChen.P4AFinitePPSelectedPrefixSquares
noncomputable section
open scoped Classical BigOperators

def selected {k : ℕ} (I : Finset (Fin k)) (p : Fin k→ℕ) := I.sort.map p

theorem partition {k : ℕ} (I : Finset (Fin k)) (p : Fin k→ℕ) :
    (selected I p++selected Iᶜ p).Perm (List.ofFn p) := by
  have hnd : (I.sort++Iᶜ.sort).Nodup := by
    rw [List.nodup_append']
    refine ⟨I.sort_nodup _,Iᶜ.sort_nodup _,?_⟩
    intro i hi hi'
    have hI : i∈I := by simpa using hi
    have hnot : i∉I := by simpa using hi'
    exact hnot hI
  have h : (I.sort++Iᶜ.sort).Perm (List.finRange k) := by
    apply (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange _)).mpr
    intro i; by_cases h : i∈I <;> simp [h]
  simpa [selected,List.ofFn_eq_map] using h.map p

private theorem prior_slots {k : ℕ} (I : Finset (Fin k)) (i : ℕ) (hi : i<Iᶜ.sort.length) :
    (Iᶜ.sort.take i).toFinset=Finset.univ.filter (fun j => j<Iᶜ.sort[i] ∧ j∉I) := by
  let K := Iᶜ.sort
  have hs : K.Pairwise (·<·) := Iᶜ.sortedLT_sort.pairwise
  ext j
  simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hj
    obtain ⟨a,ha,eq⟩ := List.mem_iff_getElem.mp hj
    have hai : a<i := lt_of_lt_of_le ha (by simp)
    have hak : a<K.length := hai.trans hi
    have hh : K[a]=j := by simpa only [List.getElem_take] using eq
    refine ⟨hh ▸ List.pairwise_iff_getElem.mp hs a i hak hi hai,?_⟩
    have hx : K[a]∈K := List.getElem_mem hak
    rw [hh] at hx
    simpa [K] using hx
  · rintro ⟨hlt,hni⟩
    have hj : j∈K := by simpa [K] using hni
    obtain ⟨a,ha,haj⟩ := List.mem_iff_getElem.mp hj
    have hai : a<i := by
      rcases lt_trichotomy a i with h|h|h
      · exact h
      · subst a; rw [←haj] at hlt; exact (lt_irrefl _ hlt).elim
      · have hr := List.pairwise_iff_getElem.mp hs i a hi ha h
        rw [haj] at hr
        exact (not_lt_of_ge hr.le hlt).elim
    refine List.mem_iff_getElem.mpr ⟨a,by simp [hai,ha],?_⟩
    simpa only [List.getElem_take] using haj

theorem exponent_product {k N : ℕ} (hN : 1<N) (I : Finset (Fin k)) (p : Fin k→ℕ)
    (hp : ∀ i,0<p i) :
    (N:ℝ)^(∑ i∈I,actualPrimeTupleLog N p i)=((selected I p).prod:ℝ) := by
  rw [Real.rpow_sum_of_pos (by exact_mod_cast (show 0<N by omega))]
  simp only [actualPrimeTupleLog_rpow hN p hp]
  exact_mod_cast (show (∏ i∈I,p i)=(selected I p).prod by
    simpa [selected] using List.prod_toFinset p (I.sort_nodup _))

/-- Each native complement square has exactly the prefix of the unselected
index list prescribed by the original mask, for every finite arity. -/
theorem finite {k N : ℕ} (hN : 1<N) (I : Finset (Fin k)) (p : Fin k→ℕ)
    (hp : ∀i,0<p i) (M : ℝ)
    (hg : ∀ j∉I,selectedSquareExpr I (actualPrimeTupleLog N p) j≤M) :
    actualDwellSupport (((N:ℝ)^M)/((selected I p).prod:ℝ)) (selected Iᶜ p) := by
  let K := Iᶜ.sort
  let t := actualPrimeTupleLog N p
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsel := exponent_product hN I p hp
  have hpos : (0:ℝ)<(selected I p).prod := hsel ▸ Real.rpow_pos_of_pos hn _
  intro i hi
  have hK : i<K.length := by simpa [selected,K] using hi
  let j := K[i]
  have hj : j∉I := by
    have H : j∈K := List.getElem_mem hK
    simpa [K] using H
  have hprior : ((K.take i).map t).sum=∑ a∈Finset.univ.filter (fun a => a<j ∧ a∉I),t a := by
    rw [←prior_slots I i hK]
    exact (List.sum_toFinset t ((Iᶜ.sort_nodup _).sublist (List.take_sublist i K))).symm
  have hpre : (N:ℝ)^((K.take i).map t).sum=(((K.take i).map (fun a => (p a:ℝ))).prod) := by
    simpa only [t,actualPrimeTupleLog_rpow hN p hp] using
      (P5Z.SelectedRealEndpointSupport.endpoint_list_product hN t (K.take i)).symm
  have hsq : (N:ℝ)^(2*t j)=(p j:ℝ)^2 := by
    rw [two_mul,Real.rpow_add hn,show (N:ℝ)^t j=(p j:ℝ) from actualPrimeTupleLog_rpow hN p hp j,pow_two]
  have hle := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le : 1≤(N:ℝ)) (hg j hj)
  unfold selectedSquareExpr at hle
  change (N:ℝ)^((∑ a∈I,t a)+(∑ a∈Finset.univ.filter (fun a => a<j ∧ a∉I),t a)+2*t j)≤_ at hle
  rw [←hprior,Real.rpow_add hn,Real.rpow_add hn,hpre,hsel,hsq] at hle
  apply (le_div_iff₀ hpos).mpr
  simpa only [selected,K,←List.map_take,List.map_map,Function.comp_def,List.getElem_map,j,
    mul_assoc,mul_comm,mul_left_comm] using hle

/-- After the selected prefix every remaining square is the full original
square at that slot, by the product of the mask and complement. -/
theorem complete {k N : ℕ} (hN : 1<N) (I : Finset (Fin k)) (p : Fin k→ℕ)
    (hp : ∀i,0<p i) (tail : List ℕ) (M : ℝ)
    (hfull : actualDwellSupport ((N:ℝ)^M) (List.ofFn p++tail))
    (hg : ∀ j∉I,selectedSquareExpr I (actualPrimeTupleLog N p) j≤M) :
    actualDwellSupport (((N:ℝ)^M)/((selected I p).prod:ℝ)) (selected Iᶜ p++tail) := by
  let S := selected I p
  let T := selected Iᶜ p
  let Q := (N:ℝ)^M
  have hfront : (List.ofFn p).prod=S.prod*T.prod := by simpa [S,T] using (partition I p).prod_eq.symm
  have hS : (0:ℝ)<S.prod := by rw [←exponent_product hN I p hp]; positivity
  have hT : (0:ℝ)<T.prod := by rw [←exponent_product hN Iᶜ p hp]; positivity
  have ht := actualDwell_selected_prefix_budget (List.ofFn p) tail (by
    rw [hfront]; exact Nat.mul_pos (by exact_mod_cast hS) (by exact_mod_cast hT)) hfull
  apply P5Z.U1011OriginalFifteenJointSelectedSupport.append_square_support T tail
    (finite hN I p hp M hg) ht
  rw [hfront,Nat.cast_mul]
  exact le_of_eq (by field_simp [hS.ne',hT.ne'])

end
end ImbalancedChen.P4AFinitePPSelectedPrefixSquares
