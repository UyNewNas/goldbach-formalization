import ImbalancedChen.P4AOriginalFiniteFallbackSecondCompactPayment

namespace ImbalancedChen.P4AOriginalFiniteFallbackSecondTail
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples)
open P4ACatalogFiveSmallThirdMass (tailBox)
open P4ACatalogFiveSmallThirdEndpointTail (tupleGuard)
open P4AOriginalFiniteFallbackBank (read)
open P4AOriginalFiniteFallbackPolicy (choose)
open P4AOriginalFiniteFallbackOwnCubeRows (old secondRow pairPoint)
open P4AOriginalFiniteFallbackCanonical (selected_second)
open P4AOriginalFiniteFallbackSmallThird (diff small floorLevel total uniform)
open P4AOriginalFiniteFallbackSecondEndpoint (row guard_iff)
open P4AOriginalFiniteFallbackSecondWalls (W)
open P4AFallbackCanonicalBanks (bank)

def low (d : OriginalData) (h : ℝ) (N : ℕ) :=
  (candidateTuples d N).filter (fun p => actualPrimeTupleLog N p 2<h)

def activeLow (d : OriginalData) (h : ℝ) (N : ℕ) := (low d h N).filter (tupleGuard N)

def cap2 (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) :=
  choose (read m (bank m).second (pairPoint N p)) (old d w N p)

theorem row_eq (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) :
    secondRow m d w N p=diff N p (old d w N p) (cap2 m d w N p) := by
  cases h : read m (bank m).second (pairPoint N p) <;> simp [secondRow,cap2,h,choose,diff]

theorem miss (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) (hg : ¬tupleGuard N p) :
    row N p=0 ∧ secondRow m d w N p=0 := by
  refine ⟨if_neg hg,?_⟩
  cases h : read m (bank m).second (pairPoint N p) with
  | none => simp [secondRow,h]
  | some c => exact (hg ((guard_iff N p).mpr (selected_second h).1)).elim

theorem safe_cap (m : ℕ) (d : OriginalData) (he : (d.e:ℝ)≤1/2048) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) :
    floorLevel≤old d w N p ∧ floorLevel≤cap2 m d w N p := by
  have ho := P4AOriginalFiniteFallbackFirstInterval.lower_floor he d.m w N (HistoricalThirdCoarse.P1ActualTuple.history p)
  refine ⟨ho,?_⟩
  cases h : read m (bank m).second (pairPoint N p) with
  | none => simpa [cap2,h,choose] using ho
  | some c =>
    have hh := (selected_second h).2.2.2.2.1
    simp only [cap2,h,choose]
    dsimp [floorLevel]; linarith

theorem small_payment (eps : ℝ) (heps : 0<eps) :
    ∃ h0 : ℝ,0<h0 ∧ h0≤small ∧ ∀ h : ℝ,0<h → h≤h0 →
      ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ m : ℕ,∀ d : OriginalData,(d.e:ℝ)≤1/2048 →
      ∀ w : ℝ, ∑ p∈low d h N,W p*(row N p-secondRow m d w N p)<eps := by
  obtain ⟨D,hD,H⟩ := uniform
  have ht : 0<small := by norm_num [small]
  refine ⟨min small (eps/(2*D)),lt_min ht (by positivity),min_le_left _ _,?_⟩
  intro h hh hle
  obtain ⟨N0,hN0,hs⟩ := H h hh (hle.trans (min_le_left _ _))
  refine ⟨N0,hN0,?_⟩
  intro N hN hEven m d he w
  let S := activeLow d h N
  have sub : S⊆tailBox N h := by
    intro p hp
    obtain ⟨hl,hg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hc,hz⟩ := Finset.mem_filter.mp hl
    exact P4ACatalogFiveSmallThirdPayment.guarded_small_candidate_mem_tailBox d N (by omega) h p hc hg hz
  let a (p : Fin 3 → ℕ) := v (actualPrimeTupleLog N p 0)
  let b (p : Fin 3 → ℕ) := v (actualPrimeTupleLog N p 1)
  have safe (p : Fin 3 → ℕ) (hp : p∈S) : floorLevel≤a p ∧ floorLevel≤b p := by
    have hg := (guard_iff N p).mp (Finset.mem_filter.mp hp).2
    have hx := P5OriginalAboveMuThirdLowerPhysicalCoefficient.above_mu_old_cap_gt_cube hg.1 hg.2.1
    have hy := (P5OriginalAboveMuThirdLowerPhysicalCoefficient.second_initial_physical_gates hg).2.2.2
    have hmu := hg.1
    dsimp only [a,b,floorLevel] at *
    dsimp only [mu] at hmu
    constructor <;> linarith
  have h1 := hs N hN hEven S sub a b safe
  have h2 := hs N hN hEven S sub (old d w N) (cap2 m d w N) (fun p _ => safe_cap m d he w N p)
  have heq : (∑ p∈low d h N,W p*(row N p-secondRow m d w N p))=
      ∑ p∈S,W p*(row N p-secondRow m d w N p) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hg : ¬tupleGuard N p := fun hg => hn (Finset.mem_filter.mpr ⟨hp,hg⟩)
    rw [(miss m d w N p hg).1,(miss m d w N p hg).2,sub_self,mul_zero]
  rw [heq]
  have hle' : (∑ p∈S,W p*(row N p-secondRow m d w N p))≤total N h S a b+total N h S (old d w N) (cap2 m d w N) := by
    unfold total
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hg := (Finset.mem_filter.mp hp).2
    rw [row,if_pos hg,row_eq,←mul_add]
    exact mul_le_mul_of_nonneg_left (by
      change diff N p (a p) (b p)-diff N p (old d w N p) (cap2 m d w N p)≤_
      linarith only [le_abs_self (diff N p (a p) (b p)),neg_le_abs (diff N p (old d w N p) (cap2 m d w N p))])
      (actualPrimeBoxWeight_nonneg (sub hp))
  have hc := (le_div_iff₀ (by positivity : 0<2*D)).mp (hle.trans (min_le_right _ _))
  linarith only [hle',h1,h2,show D*h+D*h≤eps by nlinarith only [hc]]

end
end ImbalancedChen.P4AOriginalFiniteFallbackSecondTail
