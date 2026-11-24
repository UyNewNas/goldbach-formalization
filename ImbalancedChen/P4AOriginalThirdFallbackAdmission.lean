import ImbalancedChen.P4AOriginalThirdFallbackPrimeTests
import ImbalancedChen.P4ACatalogFiveOmittedOrderPayment
import ImbalancedChen.P4AActualRefinableArchivePayment

/-! Coverage of the true before-third carrier by the separated G6 tests.
The original historical label, its first stop, both own old cubes,
and the enabled p3 cutoff are established on the very same tuple. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackAdmission
noncomputable section
open Set Filter
open scoped Classical BigOperators
open P4AOriginalThirdFallbackPrimeTests
open P4AOriginalThirdFallbackOccurrence (saving active)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalNewFifthUnion (data)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples carrier weight)
open P4ACatalogFiveHistoricalCoverage (exists_uniform_historical_owner_threshold)
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P5OriginalCommonFourthSourceNavigation (firstCoordinate)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (ThirdRegion thirdGuard rho thirdQ original_first_cube_from_stop)
open P4AOriginalRankThreeRestorationSource (beforeThirdPolicy)
open HistoricalThirdCoarse.P1ActualTuple (history history_log cube_tests_iff_log parent_two_iff active_iff_log)
open VariableEnvelope (v)

def Hit (d : OriginalData) (N : ℕ) (p : Fin 3 → ℕ) : Prop :=
  active d (N : ℝ) (history p) ∧ old3 d (N : ℝ) false (history p)=true

theorem pre_eq (p : Fin 3 → ℕ) : (List.ofFn p).reverse=history p := by simp [List.ofFn_succ,history]
theorem self (p : Fin 3 → ℕ) : rosserAncestor 3 (history p)=history p :=
  rosserAncestor_self_of_length 3 _ (by simp [history])
theorem guard_eq (N : ℕ) (p : Fin 3 → ℕ) :
    thirdGuard (N : ℝ) (history p) ↔ ThirdRegion (actualPrimeTupleLog N p 0)
      (actualPrimeTupleLog N p 1) (actualPrimeTupleLog N p 2) := by
  rw [thirdGuard,self,history_log]
theorem first_eq (N : ℕ) (p : Fin 3 → ℕ) :
    firstCoordinate (N : ℝ) (history p) = actualPrimeTupleLog N p 0 := by
  simp [firstCoordinate,history,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]
theorem raw_eq (d : OriginalData) (N : ℕ) (p : Fin 3 → ℕ) :
    HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) (history p) =
      (N : ℝ) ^ originalSeed d (N : ℝ) (history p) := by
  have hh := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
    (d.e : ℝ) d.chi d.m d.omega (N : ℝ) (history p)
  simpa only [HistoricalThirdCoarse.frozenLevel,self,originalSeed] using hh
theorem third_eq (N : ℕ) (p : Fin 3 → ℕ) :
    thirdQ (N : ℝ) (history p) = (N : ℝ)^v (actualPrimeTupleLog N p 1+actualPrimeTupleLog N p 2) := by
  rw [thirdQ,history_log]

theorem hit_in_box (d : OriginalData) {N : ℕ} (hN : 1<N) {p : Fin 3 → ℕ}
    (hp : p ∈ candidateTuples d N) (hh : Hit d N p) : p ∈ primes N := by
  have hg := (guard_eq N p).mp hh.1.2
  exact P4ACatalogFiveOmittedOrderPayment.candidate_cutoff_mem_box d cut N hN p hp
    ((mem_logPrimeBox.mp (guard_cube hg) 2).1)

theorem exists_trim_admission (r : ℕ) (e : ℚ) (he : 0 < (e : ℝ)) (hewidth : (e : ℝ) < width r/10) :
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ,q0 ≤ q → ∀ a : ℝ,a ≤ 1/800 →
      ∀ N : ℕ,1 < N → ∀ p ∈ primes N,combined r (actualPrimeTupleLog N p) ≠ 0 →
        p ∈ candidateTuples (data e q a) N ∧ Hit (data e q a) N p := by
  have hd := width_pos r
  obtain ⟨m0,hM⟩ := exists_uniform_historical_owner_threshold (width r) ((e : ℝ)/20) hd (by positivity)
  obtain ⟨q0,hq0,_,hQ⟩ := P4AActualRefinableArchivePayment.exists_actual_refinement_threshold
    1 (by norm_num) 0 m0
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha N hN p hp hn
  let d := data e q a
  let t := actualPrimeTupleLog N p
  obtain ⟨hg,hclr⟩ := region_clearance_of_combined_ne hn
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i,0 < p i := fun i => (hpi i).1.pos
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have ht : t ∈ logPrimeBox (fun _ => 0) (fun _ => (19/96:ℝ)) := by
    have hh := mem_logPrimeBox.mp (guard_cube hg)
    exact mem_logPrimeBox.mpr (fun i => ⟨cut_pos.le.trans (hh i).1,(hh i).2⟩)
  have hxy : width r < t 0-t 1 := hclr 1
  have hyz : width r < t 1-t 2 := hclr 2
  have hstop0 : width r < rho-t 0 := hclr 0
  have hstop : t 0 ≤ extendedFirstStop-width r := by
    change width r < 19/96-t 0 at hstop0
    unfold extendedFirstStop
    linarith
  obtain ⟨j,⟨hj,hcell⟩,_⟩ := hM d.m (hQ q hq).1 (e : ℝ) he.le
    (by linarith only [hewidth,hd] : 4*(e : ℝ) ≤ width r/2) t ht hxy.le hyz.le hstop
  have hhist : primeHistoryLogCoordinates (N : ℝ) 3 (history p) ∈ logPrimeMeshCell 0 (19/96) d.m j := by
    rwa [history_log]
  have haL : a ≤ t 2 := by have hb := (mem_logPrimeBox.mp (guard_cube hg) 2).1; dsimp [cut] at hb; linarith
  have hrough := (active_iff_log hN a p hpos).mpr haL
  have hsup : selectedThird d (N : ℝ) (history p) := by
    unfold selectedThird P1ThirdFallbackSupport.frozenSupported
    rw [self]
    exact ⟨hrough,j,hj,hhist⟩
  have hmu : VariableEnvelope.mu < firstCoordinate (N : ℝ) (history p) := by rw [first_eq]; exact hg.1
  have hhseed := (originalSeed_supported_interval d he.le (N : ℝ) (history p) (by simp [history]) hsup hmu).1
  rw [first_eq] at hhseed
  have hseed : v (t 0) - (3/2*((e : ℝ)/20)+2*(e : ℝ)) ≤ originalSeed d (N : ℝ) (history p) := hhseed
  have hf : 3*t 0 < HistoricalThirdCoarse.initial (e : ℝ) := original_first_cube_from_stop he.le
    (by linarith only [hstop,hewidth,hd])
  have hxold : width r < v (t 0)-3*t 0 := hclr 3
  have hzold : width r < v (t 0)-t 0-t 1-3*t 2 := hclr 4
  have hc := (cube_tests_iff_log hN (HistoricalThirdCoarse.initial (e : ℝ))
    (originalSeed d (N : ℝ) (history p)) p hpos).mpr
    ⟨hf,by linarith only [hxold,hewidth,hseed,hd],by linarith only [hzold,hewidth,hseed,hd]⟩
  have hpar := (parent_two_iff (e : ℝ) d.chi d.m a (N : ℝ) p (hpos 0)).mpr
    ⟨hc.1,HistoricalThirdCoarse.firstStop_of_triple_cell (e : ℝ) d.chi d.m (N : ℝ)
      (p 0) (p 1) (p 2) j hj hhist⟩
  have horder : StrictAnti t := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i
    · linarith
    · linarith
  have hporder := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp horder
  have hret : old3 d (N : ℝ) false (history p)=true := by
    apply (HistoricalThirdCoarse.policy_third_iff (e : ℝ) d.chi d.m a (N : ℝ)
      (p 0) (p 1) (p 2) (hpos 2) (hporder (by decide : (1:Fin 3)<2)) (hporder (by decide : (0:Fin 3)<1))).mpr
    change (p 0 : ℝ)^3 < HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) (history p) ∧
      (p 0 : ℝ)*p 1*(p 2 : ℝ)^3 < _
    rw [raw_eq]
    exact hc.2
  have hvalid : FirstExitValidSelection (beforeThirdPolicy (old3 d (N : ℝ))) [] true (List.ofFn p) := by
    simpa [List.ofFn_succ,FirstExitValidSelection,beforeThirdPolicy,firstExitDepthSplicePolicy,old3] using hpar
  have hcap : (N : ℝ)^rho ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num [rho] : rho ≤ 1)
  refine ⟨(mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 3 (beforeThirdPolicy (old3 d (N : ℝ)))
    N N 0 ((N : ℝ)^rho) hcap p).mpr
    ⟨hporder,fun i => ⟨(hpi i).1,(hpi i).2.1,Nat.cast_nonneg _,(hpi i).2.2.2⟩,hvalid⟩,
    ⟨hsup,(guard_eq N p).mpr hg⟩,hret⟩

end
end ImbalancedChen.P4AOriginalThirdFallbackAdmission

