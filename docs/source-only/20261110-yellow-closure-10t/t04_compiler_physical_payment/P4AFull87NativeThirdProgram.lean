import ImbalancedChen.P4AFull87DataSeedHistory
import ImbalancedChen.P4AFull87OrdinaryAdmissionDeletion

/-! The complete own-third source program, including the actual half-open
historical Gamma table, its rank-three rough activation, and both corrected
above-mu alternatives. No tag is added to the occupied rectangular cells. -/
namespace ImbalancedChen.P4AFull87NativeThirdProgram
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P5OriginalCommonRefinedConstructor P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4AFull87VariableSeedHistory P4AFull87ActualAffineDeletion
open P4AUpperTaggedParityCompiler P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment

def meshTests (d : OriginalData) (j : HistoricalThirdCoarse.Cell d.m) : List (Gate 3) :=
  [LE (atom (K d.omega)) (atom (X 2))] ++
    halfOpenBox (logPrimeMeshLo 0 (19/96) d.m j) (logPrimeMeshHi 0 (19/96) d.m j)

def meshProgram (d : OriginalData) : List (HistoricalThirdCoarse.Cell d.m) → Program 3
  | [] => atom (K (HistoricalThirdCoarse.initial d.e))
  | j :: js => allGates (meshTests d j)
      (atom (K (HistoricalThirdCoarse.levelExponent d.e (HistoricalThirdCoarse.box d.m j))))
      (meshProgram d js)

private theorem mesh_exact (d : OriginalData) (N : ℝ) (hN : 1 < N)
    (pre : List ℕ) (h3 : (rosserAncestor 3 pre).length=3)
    (hp : 0 < primeHistoryTuple 3 (rosserAncestor 3 pre) 2) :
    (meshProgram d (HistoricalThirdCoarse.cells d.e d.chi d.m).toList).eval
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)) = originalSeed d N pre := by
  let h := rosserAncestor 3 pre
  let t := primeHistoryLogCoordinates N 3 h
  let S := HistoricalThirdCoarse.cells d.e d.chi d.m
  let H (j : HistoricalThirdCoarse.Cell d.m) := Passed t (meshTests d j)
  have hpR : 0 < (primeHistoryTuple 3 h 2 : ℝ) := by exact_mod_cast hp
  have eqpow : N^(t 2) = (primeHistoryTuple 3 h 2 : ℝ) := by
    calc
      _ = Real.exp (Real.log (primeHistoryTuple 3 h 2 : ℝ)) := by
        rw [Real.rpow_def_of_pos (zero_lt_one.trans hN)]
        congr 1
        dsimp only [t,primeHistoryLogCoordinates]
        field_simp [(Real.log_pos hN).ne']
        <;> ring
      _ = _ := Real.exp_log hpR
  have ha : d.omega ≤ t 2 ↔ HistoricalThirdCoarse.active d.omega N h := by
    simp only [HistoricalThirdCoarse.active,show h.length=3 from h3,eq_self_iff_true,true_and]
    rw [← eqpow]
    exact (Real.rpow_le_rpow_left_iff hN).symm
  have htests (j : HistoricalThirdCoarse.Cell d.m) :
      H j ↔ HistoricalThirdCoarse.active d.omega N h ∧
      t ∈ logPrimeMeshCell 0 (19/96) d.m j := by
    simp [H,meshTests,Program.eval,ha,mem_logPrimeMeshCell]
  have val (j : HistoricalThirdCoarse.Cell d.m) (hj : j ∈ S) (ht : H j) :
      HistoricalThirdCoarse.levelExponent d.e (HistoricalThirdCoarse.box d.m j) =
        originalSeed d N pre := by
    obtain ⟨ha,hcell⟩ := (htests j).mp ht
    have hs : P1ThirdFallbackSupport.supported d.e d.chi d.m d.omega N h :=
      ⟨ha,j,hj,hcell⟩
    simp only [originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hs]
    exact (HistoricalThirdCoarse.exponent_on_cell _ _ _ t j hj hcell).symm
  have fallback (hn : ¬∃ j ∈ S, H j) :
      HistoricalThirdCoarse.initial d.e = originalSeed d N pre := by
    have hs : ¬P1ThirdFallbackSupport.supported d.e d.chi d.m d.omega N h := by
      rintro ⟨ha,j,hj,hcell⟩
      exact hn ⟨j,hj,(htests j).mpr ⟨ha,hcell⟩⟩
    simp [originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent,hs]
  have run (xs : List (HistoricalThirdCoarse.Cell d.m)) (hsub : ∀ j ∈ xs, j ∈ S) :
      (meshProgram d xs).eval t =
      if ∃ j ∈ xs, H j then originalSeed d N pre else HistoricalThirdCoarse.initial d.e := by
    induction xs with
    | nil => simp [meshProgram,Program.eval]
    | cons i is ih =>
      rw [meshProgram,eval_allGates]
      by_cases hi : H i
      · rw [if_pos hi,if_pos (show ∃ j ∈ i::is, H j from ⟨i,List.mem_cons_self,hi⟩)]
        exact val i (hsub _ List.mem_cons_self) hi
      · rw [if_neg hi,ih (fun j hj => hsub j (List.mem_cons_of_mem _ hj))]
        simp [List.mem_cons,hi]
  rw [run _ (fun j hj => Finset.mem_toList.mp hj)]
  split_ifs with hex
  · rfl
  · exact fallback (by simpa only [Finset.mem_toList] using hex)

def tent (u : Affine 3) : Program 3 := .inf (atom (ascending u)) (atom (descending u))

private theorem tent_eval (u : Affine 3) (t : Fin 3 → ℝ) :
    (tent u).eval t = VariableEnvelope.v (u.eval t) := by
  simp [tent,Program.eval,VariableEnvelope.v_eq_min]

def common (u : Affine 3) : List (Gate 3) :=
  [LT (atom (K VariableEnvelope.mu)) (atom (X 0)),
   LT (atom (X 0)) (atom (K rho)),
   LT (tent (X 0)) (atom ((u.add (K 1)).scale (1/2))),
   LT (atom u) (atom (X 0))]

def yz : Affine 3 := (X 1).add (X 2)

def threeTests : List (Gate 3) := common yz ++
  [LT (atom (K 0)) (atom (X 2)), LT (atom (X 2)) (atom (X 1)),
   LE (atom (yz.scale (5/9))) (atom ((X 2).scale 2)),
   LE (atom ((X 2).scale 2)) (atom yz), LE (atom (K (5/96))) (atom (X 2)),
   LT (atom (X 1)) (atom (K (3/16)))]

private theorem common_exact (u : Affine 3) (t : Fin 3 → ℝ) :
    Passed t (common u) ↔ VariableEnvelope.mu < t 0 ∧ t 0 < rho ∧
      2*VariableEnvelope.v (t 0)-1 < u.eval t ∧ u.eval t < t 0 := by
  simp only [common,passed_cons,passed_nil,holds_LT,Program.eval,tent_eval,
    Affine.eval_scale,Affine.eval_add,Affine.eval_coord,Affine.eval_const,and_true]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨h1,h2,by linarith,h4⟩

private theorem three_exact (t : Fin 3 → ℝ) :
    Passed t threeTests ↔ ThirdRegion (t 0) (t 1) (t 2) := by
  simp only [threeTests,passed_append,common_exact,passed_nil,passed_cons,holds_LT,holds_LE,
    yz,Program.eval,Affine.eval_coord,Affine.eval_const,Affine.eval_add,Affine.eval_scale,and_true,ThirdRegion]
  constructor
  · rintro ⟨⟨hx,hr,hlo,hup⟩,hz,hy,h5,h1,hz5,hy3⟩
    have hpos : 0 < t 1+t 2 := by linarith
    exact ⟨hx,hr,hz,hy,hlo,hup,(le_div_iff₀ hpos).mpr h5,
      (div_le_iff₀ hpos).mpr (by linarith),hz5,hy3⟩
  · rintro ⟨hx,hr,hz,hy,hlo,hup,h5,h1,hz5,hy3⟩
    have hpos : 0 < t 1+t 2 := by linarith
    exact ⟨⟨hx,hr,hlo,hup⟩,hz,hy,(le_div_iff₀ hpos).mp h5,
      by linarith [(div_le_iff₀ hpos).mp h1],hz5,hy3⟩

def native (d : OriginalData) : Program 3 :=
  let b := meshProgram d (HistoricalThirdCoarse.cells d.e d.chi d.m).toList
  .sup b (allGates threeTests (tent yz) (allGates (common (X 1)) (tent (X 1)) b))

theorem native_exact (d : OriginalData) (N : ℝ) (hN : 1 < N) (pre : List ℕ)
    (h3 : (rosserAncestor 3 pre).length=3)
    (hp : 0 < primeHistoryTuple 3 (rosserAncestor 3 pre) 2) :
    (native d).eval (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)) = lambda3 d N pre := by
  let t := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
  have h2 (i : Fin 2) := primeHistoryLogCoordinates_ancestor N h3 (by omega : 2 ≤ 3) i
  simp only [rosserAncestor_nested 2 3 (by omega)] at h2
  have he : Passed t (common (X 1)) ↔ secondGuard N pre := by
    rw [common_exact]
    simp [secondGuard,SecondRegion,t,h2]
  have ht : Passed t threeTests ↔ thirdGuard N pre := three_exact t
  change _ = max (originalSeed d N pre) (fallbackSeed d N pre)
  simp only [native,Program.eval,mesh_exact d N hN pre h3 hp,eval_allGates,tent_eval,
    yz,Affine.eval_add,Affine.eval_coord,fallbackSeed]
  by_cases htg : thirdGuard N pre <;> by_cases hsg : secondGuard N pre <;>
    simp only [show (∀ g ∈ threeTests, g.holds t) ↔ thirdGuard N pre from ht,
      show (∀ g ∈ common (X 1), g.holds t) ↔ secondGuard N pre from he,
      htg,hsg,if_true,if_false,h2]

def complete (d : OriginalData) : Program 6 := variableCompleteProgram d (native d)

theorem data_complete_on_modulus (d : OriginalData) (N cap x : ℕ) (hN : 1 < N)
    (omega v : ℝ) (hx : x ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hr : 6 ≤ x.primeFactorsList.length) :
    (complete d).eval (coords N 6 x.primeFactorsList.reverse) =
      P4AOriginalFull87DataPolicy.currentSixthExponent d (N:ℝ) (rosserAncestor 6 x.primeFactorsList) := by
  let pre := rosserAncestor 6 x.primeFactorsList
  have h6 : pre.length=6 := by simp [pre,Nat.min_eq_left hr]
  have h3 : (rosserAncestor 3 pre).length=3 := by simp [h6]
  have hx3 : 3 ≤ x.primeFactorsList.length := by omega
  have hpre : rosserAncestor 3 pre = (List.ofFn (canonicalPrefix 3 x)).reverse := by
    rw [P4AFull87OrdinaryAdmissionDeletion.reversed_prefix x 3 hx3,pre,rosserAncestor_nested 3 6 (by omega)]
  have hp : 0 < primeHistoryTuple 3 (rosserAncestor 3 pre) 2 := by
    rw [hpre]
    simpa [primeHistoryTuple] using canonicalPrefix_pos hx hx3 (2 : Fin 3)
  rw [canonical_coords _ _ _ hr, ← P4AFull87SamePieceCapVariation.coord_ancestor hr N]
  apply P4AFull87DataSeedHistory.data_variableCompleteProgram_at_history d (N:ℝ) _ pre h6
  exact (native_exact d (N:ℝ) (by exact_mod_cast hN) pre h3 hp).symm

end
end ImbalancedChen.P4AFull87NativeThirdProgram
