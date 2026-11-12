import ImbalancedChen.Part5OriginalH430ClassicalSmoothPrimorialEnvelope

/-! All nonzero integer tuples in the actual positive family: a polynomial
slot floor and a physical complete-product cap independent of the target test. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothPhysicalRoughMass
noncomputable section
open Finset Real
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalSmoothSharpGates (code physicalProduct)
open Part5OriginalH430ClassicalSmoothOuterWeight
open Part5OriginalH430ClassicalSmoothWordPhysical (logPoint)
open Part5OriginalH430ClassicalSmoothRankCoordinates
open Part5OriginalH430ClassicalSmoothRankSupport (W W_bounds)
open scoped Classical BigOperators

theorem nonzero_slots {N r : ℕ} {ν δ h c : ℝ} {cs : List ℕ}
    (t : Fin (rank cs.length r) → Fin (2*N+1)) (hN : 0<N)
    (hz : cut N≤(N:ℝ)^(1/90:ℝ)/2) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
    (hw : W cs t ν δ h c≠0) :
    (∀ i,cut N≤((t i).val:ℝ)) ∧ Part3.labelledProduct t≤2*N := by
  let f := fun i => (t i).val
  let M := physicalProduct (first f) (qVec f) (rVec f)
  let z := ratioPoint N (first f) (qVec f) (rVec f)
  let x := logPoint N (first f) (qVec f) (rVec f)
  have hW : outerWeight (code cs) ν δ h c x z ((M:ℝ)/(N:ℝ))≠0 := hw
  have hF : allFloors z≠0 := (mul_ne_zero_iff.mp hW).1
  obtain ⟨hP,hQ,hR⟩ := floors_of_nonzero hF
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hA : (0:ℝ)<(N:ℝ)^(1/90:ℝ) := rpow_pos_of_pos h0 _
  have low {v : ℕ} (hv : 1/2<(v:ℝ)/(N:ℝ)^(1/90:ℝ)) : cut N≤(v:ℝ) := by
    have h' := (lt_div_iff₀ hA).mp hv
    linarith only [hz,h']
  constructor
  · intro i
    have hi : f i∈List.ofFn f := List.mem_ofFn.mpr ⟨i,rfl⟩
    rw [all_slots f,List.mem_cons,List.mem_append] at hi
    change cut N≤(f i:ℝ)
    rcases hi with hi | hi | hi
    · rw [hi]; exact low hP
    · obtain ⟨l,hl⟩ := List.mem_ofFn.mp hi
      rw [←hl]; exact low (hQ l)
    · obtain ⟨l,hl⟩ := List.mem_ofFn.mp hi
      rw [←hl]; exact low (hR l)
  · have hcap := (div_lt_iff₀ h0).mp (radial_support hh hc hc' hW)
    have hh2 : 1+h≤2 := by linarith only [hh']
    have hl := hcap.le.trans (mul_le_mul_of_nonneg_right hh2 h0.le)
    have hm : Part3.labelledProduct t=M := entire_product t
    rw [hm]
    exact_mod_cast hl

/-- The only filter in this mass computation removes zero weights. -/
theorem row_mass {N r : ℕ} (cs : List ℕ) (ν δ h c : ℝ) (hN : 0<N)
    (hz : cut N≤(N:ℝ)^(1/90:ℝ)/2) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8) :
    let k := rank cs.length r
    p5z_labelledMass (Part3.labelledPrimeTuples k (2*N)) (fun t => W cs t ν δ h c)≤
      ((k^k:ℕ):ℝ)*(3*(N:ℝ)) := by
  let k := rank cs.length r
  let S := Part3.labelledPrimeTuples k (2*N)
  let w := fun t : Fin k → Fin (2*N+1) => W cs t ν δ h c
  let A := S.filter (fun t => w t≠0)
  have hcap (t) (ht : t∈A) : Part3.labelledProduct t≤2*N :=
    (nonzero_slots t hN hz hh hh' hc hc' (mem_filter.mp ht).2).2
  have heq : p5z_labelledMass S w=∑ t∈A,w t := (sum_filter_ne_zero S).symm
  have hf := p5z_markedProductWeight_sum A w hcap (fun _ => (1:ℝ))
  simp only [mul_one] at hf
  change p5z_labelledMass S w≤_
  rw [heq,←hf]
  have hb (m : ℕ) : p5z_markedProductWeight A w m≤((k^k:ℕ):ℝ) := by
    simpa only [one_mul] using p5z_markedProductWeight_le A (filter_subset _ S) w 1
      zero_le_one (fun t _ => (W_bounds cs t ν δ h c).2) m
  calc
    _ ≤ ∑ _m∈range (2*N+1),((k^k:ℕ):ℝ) := sum_le_sum (fun m _ => hb m)
    _ = ((k^k:ℕ):ℝ)*((2*N+1:ℕ):ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast (show 2*N+1≤3*N by omega)) (Nat.cast_nonneg _)

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothPhysicalRoughMass

