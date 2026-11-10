import ImbalancedChen.P4AOriginalSavedSixthFrontier
import ImbalancedChen.P4AOriginalFull87PolicyReverseAdmission
import ImbalancedChen.P4AOriginalNewFifthPhysical

/-! The sixth word on the common enlarged fifth frontier follows from
its original first label, third seed, the three strict odd cube tests and
the inherited fifth level. These premises are only arithmetic and
individual ancestor tests, usable on distinct original source families. -/
namespace ImbalancedChen.P4AOriginalSixthTupleReverse
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalFull87DataPolicy (fifthPolicy fifth_even level5Exponent)

theorem from_own_root (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1<N)
    (p : Fin 6 → ℕ) (hp : ∀ j,(p j).Prime) (ho : StrictAnti p) (L : ℝ)
    (hstop : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m (N:ℝ) [p 0])
    (hseed : originalSeed d (N:ℝ) [p 2,p 1,p 0]=L)
    (hini : L ≤ HistoricalThirdCoarse.initial (d.e:ℝ))
    (hfirst : 3*actualPrimeTupleLog N p 0 < L)
    (hthird : Certificates.P2OriginalSixthElevenLogSemantics.H3 (actualPrimeTupleLog N p)<L)
    (hfifth : Certificates.P2OriginalSixthElevenLogSemantics.H5 (actualPrimeTupleLog N p)<L)
    (hinherit : L ≤ level5Exponent n d (N:ℝ) [p 4,p 3,p 2,p 1,p 0]) :
    FirstExitValidSelection (fifthPolicy n d (N:ℝ)) [] true (List.ofFn p) := by
  let t := actualPrimeTupleLog N p
  have hpos (j) := (hp j).pos
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans hNr
  have hr (j : Fin 6) : (N:ℝ)^t j=(p j:ℝ) := actualPrimeTupleLog_rpow hN p hpos j
  have cube (j : Fin 6) : (N:ℝ)^(3*t j)=(p j:ℝ)^3 := by
    rw [mul_comm,Real.rpow_mul_natCast hN0.le,hr]
  have h1 : (p 0:ℝ)^3 < (N:ℝ)^L := by
    simpa only [cube] using Real.rpow_lt_rpow_of_exponent_lt hNr (show 3*t 0<L from hfirst)
  have h3 : (p 0:ℝ)*p 1*(p 2:ℝ)^3 < (N:ℝ)^L := by
    simpa only [Certificates.P2OriginalSixthElevenLogSemantics.H3,Real.rpow_add hN0,hr,cube] using
      Real.rpow_lt_rpow_of_exponent_lt hNr (show Certificates.P2OriginalSixthElevenLogSemantics.H3 t<L from hthird)
  have h5 : (([p 4,p 3,p 2,p 1,p 0].prod:ℕ):ℝ)*(p 4:ℝ)^2 < (N:ℝ)^L := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hNr (show Certificates.P2OriginalSixthElevenLogSemantics.H5 t<L from hfifth)
    simp only [Certificates.P2OriginalSixthElevenLogSemantics.H5,Real.rpow_add hN0,hr,cube] at h
    convert h using 1 <;> simp [pow_succ,mul_comm,mul_left_comm,mul_assoc]
  have a5 := (ordinaryRosserPrefixAdmissible_upper_five_iff ((N:ℝ)^L) (p 0) (p 1) (p 2)
    (p 3) (p 4) (hpos 4) (ho (by decide)) (ho (by decide)) (ho (by decide)) (ho (by decide))).mpr ⟨h1,h3,h5⟩
  have hprime : ∀ x ∈ [p 4,p 3,p 2,p 1,p 0],x.Prime := by
    intro x hx
    simp only [List.mem_cons,List.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> exact hp _
  have hsort : (List.ofFn p).reverse.Pairwise (· < ·) := by
    rw [List.pairwise_reverse]; exact List.pairwise_ofFn.mpr ho
  have hrev : (List.ofFn p).reverse=[p 5,p 4,p 3,p 2,p 1,p 0] := by simp [List.ofFn_succ]
  rw [hrev] at hsort
  have hs5 := (List.pairwise_cons.mp hsort).2
  have a3 := ordinaryRosserPrefixAdmissible_of_append false ((N:ℝ)^L) [p 4,p 3]
    [p 2,p 1,p 0] hprime hs5 a5
  have a1 := ordinaryRosserPrefixAdmissible_of_append false ((N:ℝ)^L) [p 4,p 3,p 2,p 1]
    [p 0] hprime hs5 a5
  have a1' := ordinaryRosserPrefixAdmissible_mono false _ (Real.rpow_le_rpow_of_exponent_le hNr.le hini) a1
  have test1 : old3 d (N:ℝ) false [p 0]=true := by
    rw [old3,HistoricalThirdCoarse.policy_through_two _ _ _ _ _ _ _ (by simp)]
    simp [HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy,a1',hstop]
  have test3 : old3 d (N:ℝ) false [p 2,p 1,p 0]=true := by
    rw [old3_after_two d _ _ _ (by simp),hseed]
    simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using a3
  have a5' := ordinaryRosserPrefixAdmissible_mono false _ (Real.rpow_le_rpow_of_exponent_le hNr.le hinherit) a5
  have f1 : fifthPolicy n d (N:ℝ) false [p 0]=true := by
    simp [fifthPolicy,firstExitDepthSplicePolicy,common3,test1]
  have f3 : fifthPolicy n d (N:ℝ) false [p 2,p 1,p 0]=true := by
    simp [fifthPolicy,firstExitDepthSplicePolicy,common3,test3]
  have f5 : fifthPolicy n d (N:ℝ) false [p 4,p 3,p 2,p 1,p 0]=true := by
    simpa [fifthPolicy,firstExitDepthSplicePolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,
      rosserAncestor,ordinaryParityRosserPolicy,oddFirstExitPolicy] using a5'
  rw [show List.ofFn p=[p 0,p 1,p 2,p 3,p 4,p 5] by simp [List.ofFn_succ]]
  simp only [FirstExitValidSelection,Bool.not_true,Bool.not_false]
  exact ⟨f1,fifth_even n d _ _,f3,fifth_even n d _ _,f5,fifth_even n d _ _,trivial⟩

end
end ImbalancedChen.P4AOriginalSixthTupleReverse
