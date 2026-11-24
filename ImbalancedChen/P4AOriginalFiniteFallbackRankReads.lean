import ImbalancedChen.P4AOriginalFiniteFallbackPrograms
import ImbalancedChen.P4AOriginalFiniteFallbackRange

namespace ImbalancedChen.P4AOriginalFiniteFallbackRankReads
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy
open P4AOriginalFiniteFallbackPrograms (code two three switch_eval readP_eval)
open P4AOrderedThirdRectangleRate (Stage index position)
open P4AOrderedThirdRankReads (admit)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler (universe)
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AFull87ActualAffineDeletion (coords canonical_coords)
open P4AFull87OrdinaryAdmissionDeletion (reversed_prefix)
open P4AFull87SamePieceCapVariation (coord_ancestor)

theorem coord {N x r k : ℕ} (hr : r≤x.primeFactorsList.length) (hk : k≤r) :
    point (N:ℝ) k (rosserAncestor r x.primeFactorsList)=coords N k x.primeFactorsList.reverse := by
  rw [point,rosserAncestor_nested k r hk,coord_ancestor (hk.trans hr) N,canonical_coords N k x (hk.trans hr)]

theorem seed_on {d : OriginalData} {N cap x r : ℕ} {w z : ℝ} (hx : x∈universe N cap w z)
    (hr : r≤x.primeFactorsList.length) (h3 : 3≤r) :
    (P4AOrderedThirdStaticRootPrograms.seed d).eval (coords N 3 x.primeFactorsList.reverse)=
      (P4AOriginalOrderedThirdFullPolicy.current d 0 N (rosserAncestor r x.primeFactorsList)).scalar := by
  let p := rosserAncestor r x.primeFactorsList
  have hA : rosserAncestor 3 p=rosserAncestor 3 x.primeFactorsList := rosserAncestor_nested 3 r h3 _
  have hl : (rosserAncestor 3 p).length=3 := by rw [hA]; simp [Nat.min_eq_left (h3.trans hr)]
  have hs := (List.take_sublist 3 _).trans (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hx).1
  rw [← canonicalPrefix_ofFn (h3.trans hr)] at hs
  have hp : 0<primeHistoryTuple 3 (rosserAncestor 3 p) 2 := by
    rw [hA,← reversed_prefix x 3 (h3.trans hr)]
    simpa [primeHistoryTuple] using (mem_roughPrimeUniverse_prime
      (hs.subset (List.mem_ofFn.mpr ⟨(2:Fin 3),rfl⟩))).pos
  rw [← coord (N:=N) hr h3]
  exact (P4AOrderedThirdStaticRootPrograms.static_root d N p hl hp).1

theorem read (B : Bank) (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (N cap : ℕ) (hN : 1<N)
    (w z : ℝ) (x : ℕ) (hx : x∈universe N cap w z) (r : ℕ) (hr : r≤x.primeFactorsList.length)
    (ho : polarityAfter true r=false) :
    index (position r)+1≤r ∧ F B delta n d 0 N (rosserAncestor r x.primeFactorsList)=
      admit N ((code B delta n d (position r)).eval (coords N _ x.primeFactorsList.reverse))
        (rosserAncestor r x.primeFactorsList) := by
  let p := rosserAncestor r x.primeFactorsList
  let t (k : ℕ) := coords N k x.primeFactorsList.reverse
  have hlen : p.length=r := by simp [p,Nat.min_eq_left hr]
  obtain ⟨hi,hold⟩ := P4AOrderedThirdRectangleRate.read delta hd n d N cap hN w z x hx r hr ho
  refine ⟨hi,?_⟩
  have hfirst : high N p ↔ VariableEnvelope.mu<t 1 0 := by
    rw [high,coord hr (by omega : 1≤r)]
  have h1 : r=1 ∨ 3≤r := by
    by_cases hh : 3≤r
    · exact Or.inr hh
    · have hr2 : r≤2 := by omega
      interval_cases r <;> simp [polarityAfter] at ho ⊢
  rcases h1 with h1|h3
  · subst r
    by_cases H : high N (rosserAncestor 1 x.primeFactorsList)
    all_goals
      have hl : (rosserAncestor 1 x.primeFactorsList).length=1 := by simp [Nat.min_eq_left hr]
      simpa [F,policy,dispatch,H,upper,position,code,P4AOrderedThirdRectangleRate.code,
        P4AOrderedThirdRoughCutTransport.F,P4AOriginalOrderedThirdFullPolicy.policy,
        P4AOriginalOrderedThirdFullPolicy.eight,P4AOriginalOrderedThirdFullPolicy.six,
        P4AOriginalOrderedThirdFullPolicy.five,P4AOriginalOrderedThirdFullPolicy.common,
        P4AOriginalOrderedThirdFullPolicy.base,firstExitDepthSplicePolicy,hl] using hold
  · have hseed := seed_on (d:=d) hx hr h3
    have twoE : (two B d).eval (t 3)=secondLevel B d 0 N p := by
      rw [two,readP_eval,secondLevel,coord hr (by omega : 2≤r),←hseed]
      rfl
    have threeE : (three B d).eval (t 3)=P4AOriginalFiniteFallbackPolicy.choose
        (P4AOriginalFiniteFallbackBank.read B.mesh B.third (point N 3 p)) (secondLevel B d 0 N p) := by
      rw [three,readP_eval,coord hr h3]
      exact congrArg _ twoE
    change F B delta n d 0 N p=admit N ((code B delta n d (position r)).eval (t _)) p
    change P4AOrderedThirdRoughCutTransport.F delta n d 0 N p=
      admit N ((P4AOrderedThirdRectangleRate.code delta n d (position r)).eval (t _)) p at hold
    have hs3 : position r=.third → r=3 := by
      intro h
      by_contra hh
      simp only [position,if_neg (show ¬r≤1 by omega),if_neg (show ¬r≤3 by omega)] at h
      split_ifs at h <;> contradiction
    have hn1 : position r≠.first := by
      simp only [position,if_neg (by omega : ¬r≤1)]
      split_ifs <;> decide
    cases hs : position r <;> rw [hs] at hold
    case first => exact (hn1 hs).elim
    case third =>
      have hl3 := hs3 hs
      by_cases H : high N p
      · simp only [code,switch_eval,if_pos (hfirst.mp H),F,policy,dispatch,if_pos H,upper,
          if_neg (by omega : ¬p.length≤2),ordinaryParityRosserPolicy,oddFirstExitPolicy,level,
          if_pos (by omega : p.length≤3),admit,twoE]
      · simpa only [F,policy,dispatch,if_neg H,code,switch_eval,if_neg (fun hh => H (hfirst.mpr hh))] using hold
    all_goals
      have hh : 3<r := by
        by_contra! hh
        have eq3 : r=3 := by omega
        simp [eq3,position] at hs
      by_cases H : high N p
      · simp only [code,switch_eval,if_pos (hfirst.mp H),F,policy,dispatch,if_pos H,upper,
          if_neg (by omega : ¬p.length≤2),ordinaryParityRosserPolicy,oddFirstExitPolicy,admit,
          P1FiniteAffineDecisionProgram.Program.eval_pull,level,if_neg (by omega : ¬p.length≤3)]
        exact congrArg (fun a : ℝ => decide (ordinaryRosserPrefixAdmissible false ((N:ℝ)^a) p)) threeE.symm
      · simpa only [F,policy,dispatch,if_neg H,code,switch_eval,if_neg (fun hh => H (hfirst.mpr hh))] using hold

end
end ImbalancedChen.P4AOriginalFiniteFallbackRankReads
