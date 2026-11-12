import ImbalancedChen.Part5OriginalH430ClassicalSmoothGateStrips

/-! Pointwise majorization and excess support for the physical ranked sums.
The original additive primality test is independent of the enlargement. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothRankSupport
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open Part5OriginalH430ClassicalFixedClampMarks (product)
open Part5OriginalH430ClassicalFixedClampGeometry (prefix_data)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalRadialTupleCount (bandTuples)
open Part5OriginalH430ClassicalRadialMarkedRanks (vectors vector_spec)
open Part5OriginalH430ClassicalProperWallMarkedOutputs (properTuples)
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothWordPhysical (logPoint)
open Part5OriginalH430ClassicalSmoothSharpGates (code code_bounds physicalProduct exact_sharp)
open Part5OriginalH430ClassicalSmoothOuterWeight
open Part5OriginalH430ClassicalSmoothRankCoordinates
open Part5OriginalH430ClassicalSmoothGateStrips (paid_strip)
open scoped Classical Topology BigOperators

def W {r N : ℕ} (cs : List ℕ) (t : Fin (rank cs.length r) → Fin (2*N+1)) (ν δ h c : ℝ) :=
  let f := fun i => (t i).val
  physicalWeight cs N (first f) (qVec f) (rVec f) ν δ h c

theorem W_bounds {r N : ℕ} (cs : List ℕ) (t : Fin (rank cs.length r) → Fin (2*N+1))
    (ν δ h c : ℝ) : 0≤W cs t ν δ h c ∧ W cs t ν δ h c≤1 := outer_bounds _ _ _ _ _ _ _ _

theorem original_one {N r : ℕ} {ν κ δ h c : ℝ} {cs : List ℕ}
    (t : Fin (rank cs.length r) → Fin (2*N+1))
    (j : Fin 13) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hd : 0<δ) (hh : 0<h) (ht : t∈vectors N ν κ cs (rank cs.length r)) :
    W cs t ν δ h c=1 := by
  let f := fun i => (t i).val
  have hsh := (original_rank_iff t j hc hN hν hν' hk).mp ht
  obtain ⟨u,hu,ht'⟩ := mem_image.mp ht
  obtain ⟨_,hpr,hprod,hfloor⟩ := vector_spec j hc hN hν hν' hk hu
  rw [ht'] at hpr hprod hfloor
  have hprime (i) : (f i).Prime := (mem_filter.mp hpr).2 i
  have hacc := (exact_sharp j hc hN (hprime 0) (fun i => hprime (qi i)) (fun i => hprime (ri i))).mp hsh
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hA : (0:ℝ)<(N:ℝ)^(1/90:ℝ) := rpow_pos_of_pos h0 _
  have hr (i) : 1≤(f i:ℝ)/(N:ℝ)^(1/90:ℝ) := (one_le_div hA).mpr (hfloor i)
  apply outer_one hd hh (hr 0) (fun i => hr (qi i)) (fun i => hr (ri i)) hacc.1
  exact (div_le_one h0).mpr (Nat.cast_le.mpr hacc.2.2)

theorem support_outside_original {N r : ℕ} {ν κ δ h c : ℝ} {cs : List ℕ}
    (t : Fin (rank cs.length r) → Fin (2*N+1))
    (j : Fin 13) (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc0 : 0<c) (hc' : c≤1/8)
    (hlower : (N:ℝ)^(1-κ)≤(c/2)*(N:ℝ)) (hz : cut N≤(N:ℝ)^(1/90:ℝ)/2)
    (hpr : t∈Part3.labelledPrimeTuples (rank cs.length r) (2*N))
    (hout : t∉vectors N ν κ cs (rank cs.length r)) (hpos : W cs t ν δ h c≠0) :
    t∈bandTuples N (rank cs.length r) 0 c ∨
      t∈bandTuples N (rank cs.length r) (1-2*h) (1+2*h) ∨
      t∈properTuples N (rank cs.length r) ν δ := by
  let f := fun i => (t i).val
  let M := physicalProduct (first f) (qVec f) (rVec f)
  let y := (M:ℝ)/(N:ℝ)
  let z := ratioPoint N (first f) (qVec f) (rVec f)
  let x := logPoint N (first f) (qVec f) (rVec f)
  have hm : Part3.labelledProduct t=M := entire_product t
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hprime (i) : (f i).Prime := (mem_filter.mp hpr).2 i
  have hM0 : 0<Part3.labelledProduct t := prod_pos (fun i _ => (hprime i).pos)
  have hW : outerWeight (code cs) ν δ h c x z y≠0 := hpos
  have hF : allFloors z≠0 := (mul_ne_zero_iff.mp hW).1
  obtain ⟨hP,hQ,hR⟩ := floors_of_nonzero hF
  have hA : (0:ℝ)<(N:ℝ)^(1/90:ℝ) := rpow_pos_of_pos h0 _
  have low {v : ℕ} (h : 1/2<(v:ℝ)/(N:ℝ)^(1/90:ℝ)) : cut N≤(v:ℝ) := by
    have h' := (lt_div_iff₀ hA).mp h
    linarith only [hz,h']
  have floor (i) : cut N≤(f i:ℝ) := by
    have hi : f i∈List.ofFn f := List.mem_ofFn.mpr ⟨i,rfl⟩
    rw [all_slots f,List.mem_cons,List.mem_append] at hi
    rcases hi with hi | hi | hi
    · rw [hi]; exact low hP
    · obtain ⟨l,hl⟩ := List.mem_ofFn.mp hi
      rw [←hl]; exact low (hQ l)
    · obtain ⟨l,hl⟩ := List.mem_ofFn.mp hi
      rw [←hl]; exact low (hR l)
  have hcap := radial_support hh hc0 hc' hW
  have hMcap : (Part3.labelledProduct t:ℝ)<(1+h)*(N:ℝ) := by
    rw [hm]
    exact (div_lt_iff₀ h0).mp hcap
  by_cases hthin : y≤c
  · left
    exact mem_filter.mpr ⟨hpr,floor,by rw [zero_mul]; exact Nat.cast_pos.mpr hM0,
      by rw [hm]; exact (div_le_iff₀ h0).mp hthin⟩
  · right
    have hlarge := lt_of_not_ge hthin
    by_cases hhi : 1≤y
    · left
      have hML := (le_div_iff₀ h0).mp hhi
      have hR : 0<h*(N:ℝ) := mul_pos hh h0
      rw [one_mul,←hm] at hML
      exact mem_filter.mpr ⟨hpr,floor,by linarith only [hML,hR],by linarith only [hMcap,hR]⟩
    · right
      have hsmall : (N:ℝ)^(1-κ)<(M:ℝ) := by
        have hy := (lt_div_iff₀ h0).mp hlarge
        linarith only [hlower,hy,mul_pos hc0 h0]
      have hMN : M≤N := Nat.cast_le.mp ((div_lt_one h0).mp (lt_of_not_ge hhi)).le
      have hfailed : ¬accepted (code cs) ν x := by
        intro ha
        apply hout
        apply (original_rank_iff t j hc hN hν hν' hk).mpr
        apply (exact_sharp j hc hN (hprime 0) (fun i => hprime (qi i)) (fun i => hprime (ri i))).mpr
        exact ⟨ha,hsmall,hMN⟩
      have hweight := (positive_outside_thin hc0 hlarge.le hW).1
      have hs := (code_bounds j hc).1
      have hsize : 3≤rank cs.length r := by dsimp only [rank]; omega
      refine mem_filter.mpr ⟨hpr,hsize,floor,?_,paid_strip (by omega) (code cs) hd t hfailed hweight⟩
      rw [hm]
      exact (Nat.cast_le.mpr hMN).trans (by linarith only [h0])

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothRankSupport

