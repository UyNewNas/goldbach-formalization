import ImbalancedChen.P4AOrderedThirdStaticRootPrograms
import ImbalancedChen.P1FiniteAffineQuantizerTable

namespace ImbalancedChen.P4AOrderedThirdStaticSixthPrograms
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms P4AOriginalCompleteSixthAffinePrograms
open P4AFull87VariableSeedHistory (baseValue liftSeed liftSeed_exact variableFourthProgram variableFourthProgram_exact
  variableFifthProgram variableFifthProgram_exact variableFifthAtSix variableSavedTests variableSavedProgram
  variableElevenTests variableElevenProgram variableAfterProgram variableSavedTests_exact variableElevenTests_exact)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy
open P4AOrderedThirdStaticRootPrograms (seed mode native static_root)
open P4AOriginalSixthActionBank (Action endpoint selected allActions)
open P1FiniteAffineQuantizerTable (roundedProgram roundedProgram_exact)
open P4AOriginalFull87HistoryCore (width)
open P1GuardFrozenFiniteCapAlgebra (protect rounded)
open P4AOriginalCompleteSixthChronology (applyLater laterEligible)

theorem third_ancestor (R : Root) (N : ℝ) (pre : List ℕ) (k : ℕ) (hk : 3≤k) :
    third R N (rosserAncestor k pre)=third R N pre := by
  simp only [third,P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard,
    P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard,
    rosserAncestor_nested 3 k hk,rosserAncestor_nested 2 k (by omega)]

theorem own_four (R : Root) (d : OriginalData) (b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=4) (hb : baseValue b N pre=third R N pre) :
    (variableFourthProgram d b).eval (primeHistoryLogCoordinates N 4 pre)=fourth R d N pre := by
  rw [variableFourthProgram_exact,fourth,if_pos hl,liftSeed_exact _ _ b N pre hl,hb]

theorem own_five (R : Root) (d : OriginalData) (b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=5) (hb : baseValue b N pre=third R N pre) :
    (variableFifthProgram d b).eval (primeHistoryLogCoordinates N 5 pre)=fifth R d N pre := by
  have h4 : (rosserAncestor 4 pre).length=4 := by simp [hl]
  have h4b : baseValue b N (rosserAncestor 4 pre)=third R N (rosserAncestor 4 pre) := by
    simpa only [baseValue,rosserAncestor_nested 3 4 (by decide),third_ancestor R N pre 4 (by decide)] using hb
  have hc : (fun i : Fin 4 => primeHistoryLogCoordinates N 5 pre i.castSucc)=
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) := by
    funext i; exact (primeHistoryLogCoordinates_ancestor N hl (by decide : 4≤5) i).symm
  rw [variableFifthProgram_exact,hc,own_four R d b N _ h4 h4b,fifth,if_pos hl]

theorem five_at_six (R : Root) (d : OriginalData) (b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=6) (hb : baseValue b N pre=third R N pre) :
    (variableFifthAtSix d b).eval (primeHistoryLogCoordinates N 6 pre)=fifth R d N (rosserAncestor 5 pre) := by
  have h5 : (rosserAncestor 5 pre).length=5 := by simp [hl]
  have h5b : baseValue b N (rosserAncestor 5 pre)=third R N (rosserAncestor 5 pre) := by
    simpa only [baseValue,rosserAncestor_nested 3 5 (by decide),third_ancestor R N pre 5 (by decide)] using hb
  have hc : (fun i : Fin 5 => primeHistoryLogCoordinates N 6 pre i.castSucc)=
      primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) := by
    funext i; exact (primeHistoryLogCoordinates_ancestor N hl (by decide : 5≤6) i).symm
  rw [variableFifthAtSix,Program.eval_pull,hc,own_five R d b N _ h5 h5b]

theorem saved_iff (R : Root) (d : OriginalData) (b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=6) (hb : baseValue b N pre=third R N pre) (i : P4AOriginalSavedSixthArchive.Row) :
    Passed (primeHistoryLogCoordinates N 6 pre) (variableSavedTests d b i) ↔ saved R d N i pre := by
  rw [variableSavedTests_exact,five_at_six R d b N pre hl hb,liftSeed_exact _ _ b N pre hl,hb]
  simp only [saved,hl,true_and]

theorem eleven_iff (R : Root) (d : OriginalData) (b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=6) (hb : baseValue b N pre=third R N pre) (c : ElevenCell) :
    Passed (primeHistoryLogCoordinates N 6 pre) (variableElevenTests d b c) ↔ eleven R d N c pre := by
  rw [variableElevenTests_exact,five_at_six R d b N pre hl hb]
  simp only [eleven,hl,true_and]

theorem after_exact (R : Root) (d : OriginalData) (b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=6) (hb : baseValue b N pre=third R N pre) (j : ℕ) :
    (variableAfterProgram d b j).eval (primeHistoryLogCoordinates N 6 pre)=after R d N pre j := by
  induction j with
  | zero =>
    let t := primeHistoryLogCoordinates N 6 pre
    have H :
        (variableSavedProgram d b).eval t=
          P1OriginalVariableFourthContinuation.finiteMax Finset.univ (fun i => saved R d N i pre)
            (fun i => P4AOriginalSavedSixthArchive.endpoint i t) (fifth R d N (rosserAncestor 5 pre)) := by
      simp only [variableSavedProgram,eval_maxRows,Finset.toList_toFinset,savedEndpoint_exact]
      congr 1
      · funext i; exact propext (saved_iff R d b N pre hl hb i)
      · exact five_at_six R d b N pre hl hb
    simp only [variableAfterProgram,variableElevenProgram,eval_maxRows,elevenNewA_exact,Program.eval,after]
    congr 1
    · funext c; exact propext (eleven_iff R d b N pre hl hb c)
    · exact H
  | succ j ih =>
    simp only [variableAfterProgram,laterStep,eval_maxRows,Finset.toList_toFinset,
      after,applyLater,laterEligible,hl,true_and]
    congr 1
    · funext c; apply propext
      simpa only [ih] using laterTests_exact j (variableAfterProgram d b j) c (primeHistoryLogCoordinates N 6 pre)
    · funext c; exact laterEndpointA_exact c _
    · exact ih

def fullForm {k : ℕ} (i : Fin k) : Affine k :=
  (maskAffine (Finset.univ.filter (· < i))).add ((X i).scale 2)

def compForm {k : ℕ} (I : Finset (Fin k)) (i : Fin k) : Affine k :=
  ((maskAffine I).add (maskAffine (Finset.univ.filter (fun j => j<i ∧ j∉I)))).add ((X i).scale 2)

@[simp] theorem full_eval {k : ℕ} (i : Fin k) (t : Fin k → ℝ) :
    (fullForm i).eval t=prefixSquareExpr t i := by simp [fullForm,prefixSquareExpr]
@[simp] theorem comp_eval {k : ℕ} (I : Finset (Fin k)) (i : Fin k) (t : Fin k → ℝ) :
    (compForm I i).eval t=selectedSquareExpr I t i := by simp [compForm,selectedSquareExpr]

def lowerForm {k : ℕ} (I : Finset (Fin k)) : P1QuantizedActionLicense.Gate k → Affine k
  | none => K (1/2)
  | some (false,j) => fullForm j
  | some (true,j) => if j∈I then K (1/2) else compForm I j

theorem lower_eval {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ) (g : P1QuantizedActionLicense.Gate k) :
    (lowerForm I g).eval t=P1QuantizedActionLicense.gate I t g := by
  rcases g with _ | ⟨b,i⟩
  · simp [lowerForm,P1QuantizedActionLicense.gate]
  · cases b <;> by_cases h : i∈I <;> simp [lowerForm,P1QuantizedActionLicense.gate,h]

def endpointProgram : Action → Program 6
  | .saved i => savedEndpoint i
  | .eleven c => atom (elevenNewA c)
  | .later c => atom (laterEndpointA c)

theorem endpoint_exact (a : Action) (t : Fin 6 → ℝ) : (endpointProgram a).eval t=endpoint a t := by
  cases a <;> simp [endpointProgram,endpoint,Program.eval]

def actionTests (d : OriginalData) (b : Program 3) : Action → List (Gate 6)
  | .saved i => variableSavedTests d b i
  | .eleven c => variableElevenTests d b c
  | .later c => let j := P4AOriginalSixthLaterLiteral.stage c
                laterTests j (variableAfterProgram d b j) c

def licensedTests (n : ℕ) (d : OriginalData) (b : Program 3) (a : Action) : List (Gate 6) :=
  let v := roundedProgram n (endpointProgram a)
  actionTests d b a ++ indexed Finset.univ (fun g => LT (atom (lowerForm (selected a) g)) v) ++
    [LE v (tentProgram (selected a) (width n))]

theorem licensed_iff (R : Root) (n : ℕ) (d : OriginalData) (b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=6) (hb : baseValue b N pre=third R N pre) (a : Action) :
    Passed (primeHistoryLogCoordinates N 6 pre) (licensedTests n d b a) ↔ accepted R d N n pre a := by
  let t := primeHistoryLogCoordinates N 6 pre
  have he : Passed t (actionTests d b a) ↔ eligible R d N pre a := by
    cases a with
    | saved i => exact saved_iff R d b N pre hl hb i
    | eleven c => exact eleven_iff R d b N pre hl hb c
    | later c =>
      simpa only [actionTests,eligible,laterEligible,hl,true_and,after_exact R d b N pre hl hb]
        using laterTests_exact (P4AOriginalSixthLaterLiteral.stage c)
          (variableAfterProgram d b (P4AOriginalSixthLaterLiteral.stage c)) c t
  change Passed t _ ↔ _
  simp only [licensedTests,passed_append,passed_indexed,Finset.mem_univ,true_implies,
    holds_LT,holds_LE,passed_cons,passed_nil,and_true,Program.eval,lower_eval,
    roundedProgram_exact,endpoint_exact,eval_tentProgram,he,accepted,
    P1QuantizedActionLicense.LowerLicense,and_assoc,le_sub_iff_add_le]

def p5 (n : ℕ) (d : OriginalData) (s b : Program 3) : Program 5 :=
  .sup (.sup (liftSeed 5 (by decide) s)
    (roundedProgram n ((variableFourthProgram d b).pull Fin.castSucc))) (roundedProgram n (variableFifthProgram d b))

theorem p5_exact (R : Root) (n : ℕ) (d : OriginalData) (s b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=5) (hs : baseValue s N pre=R.scalar) (hb : baseValue b N pre=third R N pre) :
    (p5 n d s b).eval (primeHistoryLogCoordinates N 5 pre)=cap5 R d N n pre := by
  have h4 : (rosserAncestor 4 pre).length=4 := by simp [hl]
  have h4b : baseValue b N (rosserAncestor 4 pre)=third R N (rosserAncestor 4 pre) := by
    simpa only [baseValue,rosserAncestor_nested 3 4 (by decide),third_ancestor R N pre 4 (by decide)] using hb
  have hc : (fun i : Fin 4 => primeHistoryLogCoordinates N 5 pre i.castSucc)=
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) := by
    funext i; exact (primeHistoryLogCoordinates_ancestor N hl (by decide : 4≤5) i).symm
  simp only [p5,Program.eval,roundedProgram_exact,Program.eval_pull,hc,cap5,protect,
    own_four R d b N _ h4 h4b,own_five R d b N pre hl hb,liftSeed_exact _ _ s N pre hl,hs]

def p6 (n : ℕ) (d : OriginalData) (s b : Program 3) : Program 6 :=
  maxRows (licensedTests n d b) (fun a => roundedProgram n (endpointProgram a)) ((p5 n d s b).pull Fin.castSucc)
    allActions.toList

theorem p6_exact (R : Root) (n : ℕ) (d : OriginalData) (s b : Program 3) (N : ℝ) (pre : List ℕ)
    (hl : pre.length=6) (hs : baseValue s N pre=R.scalar) (hb : baseValue b N pre=third R N pre) :
    (p6 n d s b).eval (primeHistoryLogCoordinates N 6 pre)=cap6 R d N n pre := by
  have h5 : (rosserAncestor 5 pre).length=5 := by simp [hl]
  have h5b : baseValue b N (rosserAncestor 5 pre)=third R N (rosserAncestor 5 pre) := by
    simpa only [baseValue,rosserAncestor_nested 3 5 (by decide),third_ancestor R N pre 5 (by decide)] using hb
  have h5s : baseValue s N (rosserAncestor 5 pre)=R.scalar := by
    simpa only [baseValue,rosserAncestor_nested 3 5 (by decide)] using hs
  have hc : (fun i : Fin 5 => primeHistoryLogCoordinates N 6 pre i.castSucc)=
      primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) := by
    funext i; exact (primeHistoryLogCoordinates_ancestor N hl (by decide : 5≤6) i).symm
  simp only [p6,eval_maxRows,Finset.toList_toFinset,roundedProgram_exact,endpoint_exact,
    Program.eval_pull,hc,p5_exact R n d s b N _ h5 h5s h5b,cap6]
  congr 1
  funext a
  exact propext (licensed_iff R n d b N pre hl hb a)

def atFive (n : ℕ) (d : OriginalData) : Program 5 :=
  .le (atom (K 1)) (liftSeed 5 (by decide) (mode d)) (p5 n d (seed d) (native d)) (variableFifthProgram d (native d))

def atSix (n : ℕ) (d : OriginalData) : Program 6 :=
  .le (atom (K 1)) (liftSeed 6 (by decide) (mode d)) (p6 n d (seed d) (native d)) (variableAfterProgram d (native d) 8)

end
end ImbalancedChen.P4AOrderedThirdStaticSixthPrograms
