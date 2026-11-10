import ImbalancedChen.P4AOriginalSavedSixthHistoricalOwner
import ImbalancedChen.P4AOriginalSavedSixthFrontier

/-! At an admitted six-prime word the odd fifth cube is already valid
at its own physical level. It supplies the lower endpoint of every
subsequent sixth residual, including tuples outside a compact trim. -/
namespace ImbalancedChen.P4AOriginalSixthResidualFloor
noncomputable section
open scoped Classical BigOperators
open P4AOriginalSavedSixthSigned (pre old)
open P4AOriginalSavedSixthHistoricalOwner (pre_list)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87DataPolicy (fifthPolicy)
open Certificates.P2OriginalSixthElevenLogSemantics (H5 S5 S6)

theorem own_fifth_cube (p : Fin 6 → ℕ) (Q : ℝ) (hp : ∀ j,(p j).Prime) (ho : StrictAnti p)
    (h : ordinaryRosserPrefixAdmissible false Q (pre p)) :
    (([p 4,p 3,p 2,p 1,p 0].prod:ℕ):ℝ)*(p 4:ℝ)^2<Q := by
  have hpr : ∀ x∈pre p,x.Prime := by
    rw [pre_list]
    intro x hx
    simp only [List.mem_cons,List.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> exact hp _
  have hsort : (pre p).Pairwise (·<·) := by
    rw [pre,List.pairwise_reverse]
    exact List.pairwise_ofFn.mpr ho
  rw [pre_list] at h hpr hsort
  have h5 := ordinaryRosserPrefixAdmissible_of_append false Q [p 5] [p 4,p 3,p 2,p 1,p 0] hpr hsort h
  exact ((ordinaryRosserPrefixAdmissible_upper_five_iff Q (p 0) (p 1) (p 2) (p 3) (p 4)
    (hp 4).pos (ho (by decide)) (ho (by decide)) (ho (by decide)) (ho (by decide))).mp h5).2.2

theorem last_prime_lt_quotient (p : Fin 6 → ℕ) (Q : ℝ) (hp : ∀ j,(p j).Prime) (ho : StrictAnti p)
    (h : ordinaryRosserPrefixAdmissible false Q (pre p)) :
    (p 5:ℝ)<Q/((∏ j,p j:ℕ):ℝ) := by
  let b : ℝ := ([p 4,p 3,p 2,p 1,p 0].prod:ℕ)
  have hbp : 0<[p 4,p 3,p 2,p 1,p 0].prod := by
    exact Nat.mul_pos (hp 4).pos (Nat.mul_pos (hp 3).pos (Nat.mul_pos (hp 2).pos
      (Nat.mul_pos (hp 1).pos (Nat.mul_pos (hp 0).pos Nat.zero_lt_one))))
  have hb : 0<b := by exact_mod_cast hbp
  have hpro : 0<((∏ j,p j:ℕ):ℝ) := by exact_mod_cast Finset.prod_pos (fun j (_ : j∈(Finset.univ : Finset (Fin 6))) => (hp j).pos)
  have hr : (p 5:ℝ)<p 4 := by exact_mod_cast ho (by decide : (4:Fin 6)<5)
  have hp5r : (0:ℝ)≤p 5 := Nat.cast_nonneg _
  have hp4r : (0:ℝ)<p 4 := by exact_mod_cast (hp 4).pos
  have hs : (p 5:ℝ)^2<(p 4:ℝ)^2 := by nlinarith only [sq_nonneg ((p 4:ℝ)-p 5),mul_pos (sub_pos.mpr hr) (add_pos_of_pos_of_nonneg hp4r hp5r)]
  apply (lt_div_iff₀ hpro).mpr
  calc
    (p 5:ℝ)*((∏ j,p j:ℕ):ℝ) = b*(p 5:ℝ)^2 := by
      simp [b,Fin.prod_univ_succ,pow_two, mul_comm,mul_left_comm,mul_assoc]
    _ < b*(p 4:ℝ)^2 := mul_lt_mul_of_pos_left hs hb
    _ < Q := own_fifth_cube p Q hp ho h

theorem history_and_wedge (N : ℕ) (hN : 1<N) (p : Fin 6 → ℕ) (P : ℝ)
    (hp : ∀ j,(p j).Prime) (ho : StrictAnti p)
    (h : ordinaryRosserPrefixAdmissible false ((N:ℝ)^P) (pre p)) :
    let t := actualPrimeTupleLog N p
    H5 t<P ∧ 2*(t 4-t 5)<P-S6 t-t 5 := by
  let t := actualPrimeTupleLog N p
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans hNr
  have hu (j : Fin 6) : (N:ℝ)^t j=(p j:ℝ) := actualPrimeTupleLog_rpow hN p (fun j => (hp j).pos) j
  have hc : (N:ℝ)^(3*t 4)=(p 4:ℝ)^3 := by
    rw [mul_comm,Real.rpow_mul_natCast hN0.le,hu]
  have hgate := own_fifth_cube p ((N:ℝ)^P) hp ho h
  have hRN : (N:ℝ)^(H5 t)<(N:ℝ)^P := by
    simp only [H5,Real.rpow_add hN0,hu,hc]
    convert hgate using 1 <;> simp [pow_succ,mul_comm,mul_left_comm,mul_assoc]
  have hH : H5 t<P := by
    by_contra h
    exact (not_lt_of_ge (Real.rpow_le_rpow_of_exponent_le hNr.le (le_of_not_gt h))) hRN
  refine ⟨hH,?_⟩
  dsimp only [H5] at hH
  dsimp only [S6,S5]
  linarith only [hH]

theorem actual_fifth_frontier (n : ℕ) (d : OriginalData) (N cap : ℕ) (w z : ℝ)
    (weight : ℕ→ℝ) (state : FirstExitDepthState ℕ)
    (hf : state∈firstExitDepthFrontier 6 (fifthPolicy n d N) weight [] true 1 (roughPrimeUniverse N cap w z))
    (p : Fin 6→ℕ) (hpre : pre p=state.selectedPrefix) (hp : ∀ j,(p j).Prime) (ho : StrictAnti p)
    (hN : 1<N) :
    let L := old n d N (pre p)
    let t := actualPrimeTupleLog N p
    H5 t<L ∧ 2*(t 4-t 5)<L-S6 t-t 5 ∧ (p 5:ℝ)<(N:ℝ)^L/((∏ j,p j:ℕ):ℝ) := by
  have ha := P4AOriginalSavedSixthFrontier.actual_fifth_at_six n d N cap w z weight state hf
  rw [←hpre] at ha
  obtain ⟨hh,hg⟩ := history_and_wedge N hN p (old n d N (pre p)) hp ho ha
  exact ⟨hh,hg,last_prime_lt_quotient p _ hp ho ha⟩

end
end ImbalancedChen.P4AOriginalSixthResidualFloor
