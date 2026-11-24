import ImbalancedChen.P4AOrderedThirdGlobalRange
import ImbalancedChen.P4AOrderedThirdPrefixDeletion

namespace ImbalancedChen.P4AOrderedThirdRankReads
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy
open P4AOrderedThirdStaticRootPrograms (seed mode native static_root mode_at common_exact tent_eval)
open P4AFull87NativeThirdProgram (tent)
open P4AOrderedThirdStaticSixthPrograms (atFive atSix p5_exact p6_exact own_five after_exact)
open P4AFull87VariableSeedHistory (liftSeed liftSeed_exact baseValue)
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (secondGuard SecondRegion)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AUpperTaggedParityCompiler P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AFull87ActualAffineDeletion (coords canonical_coords)
open P4AFull87OrdinaryAdmissionDeletion (reversed_prefix)
open P4AFull87SamePieceCapVariation (coord_ancestor)

def oneTests (d : OriginalData) (j : Fin (d.m+1)) : List (Gate 1) :=
  let a := logPrimeMeshPoint 0 (19/96) d.m j.val
  let b := logPrimeMeshPoint 0 (19/96) d.m (j.val+1)
  [LE (atom (K a)) (atom (X 0)),LT (atom (X 0)) (atom (K b))] ++
  static (b≤extendedFirstStop-4*(d.e:ℝ))

def first (d : OriginalData) : List (Fin (d.m+1)) → Program 1
  | [] => atom (K 0)
  | j::js => allGates (oneTests d j) (atom (K (HistoricalThirdCoarse.initial (d.e:ℝ)))) (first d js)

def firstP (d : OriginalData) := first d Finset.univ.toList

theorem firstP_exact (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    (firstP d).eval (primeHistoryLogCoordinates N 1 pre)=
      if HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m N pre then HistoricalThirdCoarse.initial (d.e:ℝ) else 0 := by
  let t := primeHistoryLogCoordinates N 1 pre
  have run (xs : List (Fin (d.m+1))) : (first d xs).eval t=
      if ∃ j∈xs,Passed t (oneTests d j) then HistoricalThirdCoarse.initial (d.e:ℝ) else 0 := by
    induction xs with
    | nil => simp [first,Program.eval]
    | cons j js ih =>
      rw [first,eval_allGates]
      by_cases h : Passed t (oneTests d j)
      · rw [if_pos h,if_pos (show ∃ i∈j::js,Passed t (oneTests d i) from ⟨j,List.mem_cons_self,h⟩)]
        simp [Program.eval]
      · rw [if_neg h,ih]; simp [List.mem_cons,h]
  rw [firstP,run]
  simp [oneTests,t,HistoricalThirdCoarse.firstStop,and_assoc,Program.eval]

def thirdP (d : OriginalData) : Program 3 :=
  .sup (seed d) (allGates (P4AFull87NativeThirdProgram.common (X 1)) (tent (X 1)) (seed d))

def eighthP (delta : ℝ) (n : ℕ) (d : OriginalData) : Program 8 :=
  P4AOrderedThirdEighthSelectionProgram.finish delta n
    ((atSix n d).pull (fun j => j.castLE (by decide : 6≤8)))

def admit (N : ℝ) (a : ℝ) (p : List ℕ) : Bool := decide (ordinaryRosserPrefixAdmissible false (N^a) p)

theorem admit_max (N : ℝ) (hN : 1≤N) (a b : ℝ) (p : List ℕ) :
    admit N (max a b) p=(admit N a p || admit N b p) := by
  by_cases h : a≤b
  · rw [max_eq_right h]
    have hmono := ordinaryRosserPrefixAdmissible_mono false p (Real.rpow_le_rpow_of_exponent_le hN h)
    by_cases ha : ordinaryRosserPrefixAdmissible false (N^a) p
    · simp [admit,ha,hmono ha]
    · simp [admit,ha]
  · rw [max_eq_left (le_of_not_ge h)]
    have hmono := ordinaryRosserPrefixAdmissible_mono false p
      (Real.rpow_le_rpow_of_exponent_le hN (le_of_not_ge h))
    by_cases hb : ordinaryRosserPrefixAdmissible false (N^b) p
    · simp [admit,hb,hmono hb]
    · simp [admit,hb]

theorem native_modes (d : OriginalData) (N : ℝ) (p : List ℕ)
    (hlen : (rosserAncestor 3 p).length=3) (hp : 0<primeHistoryTuple 3 (rosserAncestor 3 p) 2) :
    let R := current d 0 N p
    baseValue (seed d) N p=R.scalar ∧
    (1≤baseValue (mode d) N p ↔ R.lower) ∧ baseValue (native d) N p=third R N p := by
  obtain ⟨hs,hm,hb⟩ := static_root d N p hlen hp
  refine ⟨hs,?_,hb⟩
  change 1≤(mode d).eval _ ↔ _
  rw [← hm,mode_at]
  split_ifs <;> norm_num

theorem five_exact (n : ℕ) (d : OriginalData) (N : ℝ) (p : List ℕ)
    (hl : p.length=5) (hp : 0<primeHistoryTuple 3 (rosserAncestor 3 p) 2) :
    let R := current d 0 N p
    (atFive n d).eval (primeHistoryLogCoordinates N 5 p)=
      if R.lower then cap5 R d N n p else fifth R d N p := by
  let R := current d 0 N p
  obtain ⟨hs,hm,hb⟩ := native_modes d N p (by simp [hl]) hp
  simp only [atFive,Program.eval,Affine.eval_const,liftSeed_exact _ _ _ N p hl,
    show (1≤baseValue (mode d) N p) ↔ R.lower from hm,
    p5_exact R n d _ _ N p hl hs hb,own_five R d _ N p hl hb]

theorem six_exact (n : ℕ) (d : OriginalData) (N : ℝ) (p : List ℕ)
    (hl : p.length=6) (hp : 0<primeHistoryTuple 3 (rosserAncestor 3 p) 2) :
    let R := current d 0 N p
    (atSix n d).eval (primeHistoryLogCoordinates N 6 p)=
      if R.lower then cap6 R d N n p else after R d N p 8 := by
  let R := current d 0 N p
  obtain ⟨hs,hm,hb⟩ := native_modes d N p (by simp [hl]) hp
  simp only [atSix,Program.eval,Affine.eval_const,liftSeed_exact _ _ _ N p hl,
    show (1≤baseValue (mode d) N p) ↔ R.lower from hm,
    p6_exact R n d _ _ N p hl hs hb,after_exact R d _ N p hl hb 8]

section Actual

variable (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (N cap : ℕ) (hN : 1<N)
  (w z : ℝ) (x : ℕ) (hx : x∈universe N cap w z)

private theorem coord {j : ℕ} (h : j≤x.primeFactorsList.length) :
    coords N j x.primeFactorsList.reverse=
      primeHistoryLogCoordinates (N:ℝ) j (rosserAncestor j x.primeFactorsList) := by
  rw [canonical_coords N j x h,coord_ancestor h N]

include hx

private theorem prime_pos {r : ℕ} (h : r≤x.primeFactorsList.length) (i : Fin r) : 0<canonicalPrefix r x i := by
  have hp := (List.take_sublist r _).trans (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hx).1
  rw [← canonicalPrefix_ofFn h] at hp
  exact (mem_roughPrimeUniverse_prime (hp.subset (List.mem_ofFn.mpr ⟨i,rfl⟩))).pos

private theorem positive3 (h : 3≤x.primeFactorsList.length) :
    0<primeHistoryTuple 3 (rosserAncestor 3 x.primeFactorsList) 2 := by
  rw [← reversed_prefix x 3 h]
  simpa [primeHistoryTuple] using prime_pos N cap w z x hx h (2:Fin 3)

include hN

theorem read_one (h : 1≤x.primeFactorsList.length) :
    let p := rosserAncestor 1 x.primeFactorsList
    policy delta n d 0 N false p=admit N ((firstP d).eval (coords N 1 x.primeFactorsList.reverse)) p := by
  let p := rosserAncestor 1 x.primeFactorsList
  have hl : p.length=1 := by simp [p,h]
  have hprod : (1:ℝ)≤(p.prod:ℝ) := by
    rw [show p=(List.ofFn (canonicalPrefix 1 x)).reverse from (reversed_prefix x 1 h).symm,List.prod_reverse]
    simpa [List.ofFn_succ] using (show (1:ℝ)≤canonicalPrefix 1 x 0 by exact_mod_cast prime_pos N cap w z x hx h (0:Fin 1))
  have hf : ¬ordinaryRosserPrefixAdmissible false ((N:ℝ)^(0:ℝ)) p :=
    fun hh => (not_lt_of_ge hprod) (by simpa using hh.1)
  rw [coord N x h,firstP_exact]
  change policy delta n d 0 N false p=_
  by_cases H : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m (N:ℝ) p <;>
    simp [policy,eight,six,five,common,base,firstExitDepthSplicePolicy,hl,
      HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy,admit,H,hf]

theorem read_three (h : 3≤x.primeFactorsList.length) :
    let p := rosserAncestor 3 x.primeFactorsList
    policy delta n d 0 N false p=admit N ((thirdP d).eval (coords N 3 x.primeFactorsList.reverse)) p := by
  let p := rosserAncestor 3 x.primeFactorsList
  let R := current d 0 N p
  let t := primeHistoryLogCoordinates (N:ℝ) 3 p
  have hl : p.length=3 := by simp [p,h]
  have self : rosserAncestor 3 p=p := rosserAncestor_self_of_length _ _ hl
  have h2 (i : Fin 2) := primeHistoryLogCoordinates_ancestor (N:ℝ) hl (by decide : 2≤3) i
  have gs : Passed t (P4AFull87NativeThirdProgram.common (X 1)) ↔ secondGuard N p := by
    rw [common_exact]
    simp [secondGuard,SecondRegion,t,h2]
  have hs : (seed d).eval t=R.scalar := by
    have hp := positive3 N cap w z x hx h
    simpa only [R,t,self] using (static_root d N p (by rw [self,hl]) (by simpa only [self] using hp)).1
  rw [coord N x h]
  change policy delta n d 0 N false p=admit N ((thirdP d).eval t) p
  simp only [thirdP,Program.eval,eval_allGates,tent_eval,Affine.eval_coord,hs,
    show (∀ g∈P4AFull87NativeThirdProgram.common (X 1),g.holds t) ↔ secondGuard N p from gs,
    admit_max N (by exact_mod_cast (show 1≤N by omega))]
  by_cases H : secondGuard N p <;>
    simp [policy,eight,six,five,common,base,firstExitDepthSplicePolicy,hl,H,
      ordinaryParityRosserPolicy,oddFirstExitPolicy,admit,R,t,h2]

theorem read_five {r : ℕ} (h : r≤x.primeFactorsList.length) (hlo : 4<r) (hhi : r≤6) :
    let p := rosserAncestor r x.primeFactorsList
    policy delta n d 0 N false p=admit N ((atFive n d).eval (coords N 5 x.primeFactorsList.reverse)) p := by
  let p := rosserAncestor r x.primeFactorsList
  let h5 := rosserAncestor 5 x.primeFactorsList
  have hl : p.length=r := by simp [p,Nat.min_eq_left h]
  have hp : rosserAncestor 5 p=h5 := rosserAncestor_nested 5 r (by omega) _
  have h5len : h5.length=5 := by simp [h5,Nat.min_eq_left (show 5≤x.primeFactorsList.length by omega)]
  have hv := five_exact n d N h5 h5len (by
    rw [show rosserAncestor 3 h5=rosserAncestor 3 x.primeFactorsList from rosserAncestor_nested 3 5 (by decide) _]
    exact positive3 N cap w z x hx (by omega))
  have hR : current d 0 N h5=current d 0 N p := by
    rw [← hp,current_ancestor d 0 N p 5 (by decide)]
  rw [coord N x (show 5≤x.primeFactorsList.length by omega),hv]
  change policy delta n d 0 N false p=_
  simp [policy,eight,six,five,firstExitDepthSplicePolicy,hl,hhi,show r≤8 by omega,show ¬ r≤4 by omega,
    frozenParityRosserPolicy,ancestorFrozenPolicy,hp,hR,admit,ordinaryParityRosserPolicy,oddFirstExitPolicy]

theorem read_six {r : ℕ} (h : r≤x.primeFactorsList.length) (hlo : 6<r) (hhi : r≤8) :
    let p := rosserAncestor r x.primeFactorsList
    policy delta n d 0 N false p=admit N ((atSix n d).eval (coords N 6 x.primeFactorsList.reverse)) p := by
  let p := rosserAncestor r x.primeFactorsList
  let h6 := rosserAncestor 6 x.primeFactorsList
  have hl : p.length=r := by simp [p,Nat.min_eq_left h]
  have hp : rosserAncestor 6 p=h6 := rosserAncestor_nested 6 r (by omega) _
  have h6len : h6.length=6 := by simp [h6,Nat.min_eq_left (show 6≤x.primeFactorsList.length by omega)]
  have hv := six_exact n d N h6 h6len (by
    rw [show rosserAncestor 3 h6=rosserAncestor 3 x.primeFactorsList from rosserAncestor_nested 3 6 (by decide) _]
    exact positive3 N cap w z x hx (by omega))
  have hR : current d 0 N h6=current d 0 N p := by
    rw [← hp,current_ancestor d 0 N p 6 (by decide)]
  rw [coord N x (show 6≤x.primeFactorsList.length by omega),hv]
  change policy delta n d 0 N false p=_
  simp [policy,eight,six,firstExitDepthSplicePolicy,hl,hhi,show ¬ r≤6 by omega,
    frozenParityRosserPolicy,ancestorFrozenPolicy,hp,hR,admit,ordinaryParityRosserPolicy,oddFirstExitPolicy]

include hd

theorem read_eight {r : ℕ} (h : r≤x.primeFactorsList.length) (hlo : 8<r) :
    let p := rosserAncestor r x.primeFactorsList
    policy delta n d 0 N false p=admit N ((eighthP delta n d).eval (coords N 8 x.primeFactorsList.reverse)) p := by
  let p := rosserAncestor r x.primeFactorsList
  have hl : p.length=r := by simp [p,Nat.min_eq_left h]
  have he : rosserAncestor 8 p=rosserAncestor 8 x.primeFactorsList := rosserAncestor_nested 8 r (by omega) _
  have h6 : (rosserAncestor 6 p).length=6 := by simp [hl,Nat.min_eq_left (show 6≤r by omega)]
  have h8 : (rosserAncestor 8 p).length=8 := by simp [hl,Nat.min_eq_left (show 8≤r by omega)]
  have hm : (fun i : Fin 6 => point8 (N:ℝ) p (i.castLE (by decide : 6≤8)))=
      primeHistoryLogCoordinates (N:ℝ) 6 (rosserAncestor 6 p) := by
    funext i
    simpa only [point8,rosserAncestor_nested 6 8 (by decide)] using
      (primeHistoryLogCoordinates_ancestor (N:ℝ) h8 (by decide : 6≤8) i).symm
  have hv := six_exact n d N (rosserAncestor 6 p) h6 (by
    simp only [p,rosserAncestor_nested 3 6 (by decide),rosserAncestor_nested 3 r (by omega)]
    exact positive3 N cap w z x hx (by omega))
  have hv8 := P4AOrderedThirdEighthSelectionProgram.finish_exact delta hd n
    ((atSix n d).pull (fun j => j.castLE (by decide : 6≤8))) (N:ℝ) p (by omega)
  rw [show coords N 8 x.primeFactorsList.reverse=point8 (N:ℝ) p by rw [point8,he,coord N x (by omega)]]
  change policy delta n d 0 N false p=admit N ((eighthP delta n d).eval (point8 (N:ℝ) p)) p
  rw [eighthP,hv8]
  cases H : selectedCap delta n (N:ℝ) p <;>
    simp [policy,eight,six,firstExitDepthSplicePolicy,hl,show ¬r≤8 by omega,show ¬r≤6 by omega,H,
      frozenParityRosserPolicy,ancestorFrozenPolicy,Program.eval_pull,hm,hv,current_ancestor d 0 N p 6 (by decide),
      ordinaryParityRosserPolicy,oddFirstExitPolicy,admit]

end Actual
end
end ImbalancedChen.P4AOrderedThirdRankReads
