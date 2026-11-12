import ImbalancedChen.Part5OriginalH430ClassicalProperWallPairs
import ImbalancedChen.P5U7ActualRoughTargetExclusion

/-! Every true ordered vector in a proper wall strip maps to a covered
integer. Two distinct positions may carry the very same prime. After their
removal at least one actual prime remains, including at that coincidence. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalProperWallMarkedOutputs
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open Part5OriginalH430ClassicalFixedClampGeometry (prime_divisor_floor)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalProperWallPairs
open scoped Classical Topology BigOperators

def onWall {N k : ℕ} (ν δ : ℝ) (t : Fin k → Fin (2*N+1)) :=
  ∃ i j : Fin k,i≠j ∧ near N ν δ ![(t i).val,(t j).val]

def properTuples (N k : ℕ) (ν δ : ℝ) :=
  (Part3.labelledPrimeTuples k (2*N)).filter (fun t =>
    3≤k ∧ (∀ i,cut N≤((t i).val:ℝ)) ∧
    (Part3.labelledProduct t:ℝ)≤2*(N:ℝ) ∧ onWall ν δ t)

def bad (N : ℕ) := p5U7ActualBadRough N (2*(N:ℝ)) (cut N)
def cover (N : ℕ) (ν δ : ℝ) := outputs N ν δ ∪ bad N

theorem output_mem {N k : ℕ} {ν δ : ℝ} {t : Fin k → Fin (2*N+1)}
    (hN : 2<N) (ht : t∈properTuples N k ν δ) :
    Part3.labelledProduct t∈cover N ν δ := by
  obtain ⟨hpr,hk,hfloor,hcap,i,j,hij,hwall⟩ := mem_filter.mp ht
  let f := fun l : Fin k => (t l).val
  let M := Part3.labelledProduct t
  have hp (l : Fin k) : (f l).Prime := (mem_filter.mp hpr).2 l
  have hM : 0<M := Finset.prod_pos (fun l _ => (hp l).pos)
  have hfdiv (l : Fin k) : f l∣M := dvd_prod_of_mem f (mem_univ l)
  let L := List.ofFn f
  have hlist : ∀ q∈L,q.Prime ∧ cut N≤(q:ℝ) := by
    intro q hq
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨hp l,hfloor l⟩
  have hLM : L.prod=M := by simp only [L,List.prod_ofFn,M,Part3.labelledProduct,f]
  have hrough : Rough (cut N) M := fun q hq hd => prime_divisor_floor hlist q hq (hLM.symm ▸ hd)
  apply mem_union.mpr
  by_cases hcop : M.Coprime N
  · left
    let v : Pair := ![f i,f j]
    have hNr : (2:ℝ)<N := by exact_mod_cast hN
    have h0 := (by norm_num : (0:ℝ)<2).trans hNr
    have hlt (l : Fin k) : (f l:ℝ)<(N:ℝ)^(2:ℝ) := by
      have hl : f l≤2*N := Nat.lt_succ_iff.mp (t l).isLt
      have hl' : (f l:ℝ)≤2*(N:ℝ) := by exact_mod_cast hl
      rw [rpow_two]
      exact hl'.trans_lt (by nlinarith only [mul_pos h0 (sub_pos.mpr hNr)])
    have hin (l : Fin k) : (f l).Prime ∧ ¬f l∣N ∧ cut N≤(f l:ℝ) ∧ (f l:ℝ)<(N:ℝ)^(2:ℝ) :=
      ⟨hp l,(hp l).coprime_iff_not_dvd.mp (hcop.of_dvd_left (hfdiv l)),hfloor l,hlt l⟩
    have hpairs : v∈pairs N ν δ := by
      apply mem_filter.mpr
      refine ⟨mem_actualPrimeBoxTuples_iff.mpr ?_,hwall⟩
      intro l
      fin_cases l
      · exact hin i
      · exact hin j
    let U := (univ:Finset (Fin k)).erase i
    let V := U.erase j
    let m := ∏ l∈V,f l
    have hj : j∈U := mem_erase.mpr ⟨hij.symm,mem_univ _⟩
    have hi : i∈(univ:Finset (Fin k)) := mem_univ _
    have hpart₁ : (∏ l∈U,f l)*f i=M := prod_erase_mul univ f hi
    have hpart₂ : m*f j=∏ l∈U,f l := prod_erase_mul U f hj
    have heq : f i*f j*m=M := by rw [←hpart₁,←hpart₂]; ac_rfl
    have hm : 0<m := Finset.prod_pos (fun l _ => (hp l).pos)
    have hsize : V.card=k-1-1 := by
      rw [show V.card=U.card-1 from card_erase_of_mem hj,
        show U.card=(univ:Finset (Fin k)).card-1 from card_erase_of_mem hi,
        card_univ,Fintype.card_fin]
    obtain ⟨l,hl⟩ := card_pos.mp (show 0<V.card by omega)
    have hrest : 1<m := (hp l).one_lt.trans_le (Nat.le_of_dvd hm (dvd_prod_of_mem f hl))
    have hmdiv : m∣M := heq ▸ dvd_mul_left m (f i*f j)
    have hden : (0:ℝ)<(f i*f j:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos (hp i).pos (hp j).pos)
    have hmc : (m:ℝ)≤2*(N:ℝ)/((f i*f j:ℕ):ℝ) := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ = (M:ℝ) := by rw [←heq]; push_cast <;> ring
        _ ≤ _ := hcap
    have hqm : m∈quotient N v := mem_erase.mpr ⟨ne_of_gt hrest,
      mem_roughNumbers.mpr ⟨hm,hmc,fun q hq hd => hrough q hq (hd.trans hmdiv)⟩⟩
    exact mem_image.mpr ⟨⟨v,m⟩,mem_sigma.mpr ⟨hpairs,hqm⟩,heq⟩
  · right
    exact mem_filter.mpr ⟨mem_roughNumbers.mpr ⟨hM,hcap,hrough⟩,hcop⟩

theorem rank_bound {N : ℕ} (hN : 2<N) (k : ℕ) (ν δ : ℝ) :
    ((properTuples N k ν δ).card:ℝ)≤
      ((k^k:ℕ):ℝ)*(((outputs N ν δ).card:ℝ)+((bad N).card:ℝ)) := by
  let S := properTuples N k ν δ
  have hsub : S⊆Part3.labelledPrimeTuples k (2*N) := filter_subset _ _
  have hc : S.card=∑ m∈cover N ν δ,(S.filter (fun t => Part3.labelledProduct t=m)).card :=
    Finset.card_eq_sum_card_fiberwise (fun t ht => output_mem hN ht)
  have hcover : ((cover N ν δ).card:ℝ)≤((outputs N ν δ).card:ℝ)+((bad N).card:ℝ) := by
    exact_mod_cast card_union_le (outputs N ν δ) (bad N)
  change (S.card:ℝ)≤_
  rw [hc,Nat.cast_sum]
  calc
    _ ≤ ∑ _m∈cover N ν δ,((k^k:ℕ):ℝ) :=
      sum_le_sum (fun m _ => by exact_mod_cast p5z_marked_prime_product_fibre_card_le S hsub m)
    _ = ((k^k:ℕ):ℝ)*((cover N ν δ).card:ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcover (Nat.cast_nonneg _)

end
end ImbalancedChen.Part5OriginalH430ClassicalProperWallMarkedOutputs

