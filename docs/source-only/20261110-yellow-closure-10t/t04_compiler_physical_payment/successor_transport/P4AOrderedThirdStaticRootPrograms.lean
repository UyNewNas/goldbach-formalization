import ImbalancedChen.P4AOrderedThirdRoughCutTransport
import ImbalancedChen.P4AFull87NativeThirdProgram

namespace ImbalancedChen.P4AOrderedThirdStaticRootPrograms
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (current)
open P4AOriginalOrderedThirdTable (retained capValue atPoint atPoint_on_cell rawExponent)
open P4AFull87NativeThirdProgram (tent common yz threeTests)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

def tests (m : ℕ) (j : HistoricalThirdCoarse.Cell m) : List (Gate 3) :=
  halfOpenBox (logPrimeMeshLo 0 (19/96) m j) (logPrimeMeshHi 0 (19/96) m j)

def lookup {m : ℕ} (miss : ℝ) (v : HistoricalThirdCoarse.Cell m → ℝ) :
    List (HistoricalThirdCoarse.Cell m) → Program 3
  | [] => atom (K miss)
  | j::js => allGates (tests m j) (atom (K (v j))) (lookup miss v js)

theorem eval_lookup {m : ℕ} (miss : ℝ) (v : HistoricalThirdCoarse.Cell m → ℝ)
    (s : Finset (HistoricalThirdCoarse.Cell m)) (t : Fin 3 → ℝ) (y : ℝ)
    (hit : ∀ j∈s,t∈logPrimeMeshCell 0 (19/96) m j → v j=y)
    (no : (¬∃ j∈s,t∈logPrimeMeshCell 0 (19/96) m j) → miss=y) :
    (lookup miss v s.toList).eval t=y := by
  let Q (j : HistoricalThirdCoarse.Cell m) := t∈logPrimeMeshCell 0 (19/96) m j
  have eqv j : Passed t (tests m j) ↔ Q j := by simp [tests,Q,mem_logPrimeMeshCell]
  have run (xs : List (HistoricalThirdCoarse.Cell m)) (hs : ∀ j∈xs,j∈s) :
      (lookup miss v xs).eval t=if ∃ j∈xs,Q j then y else miss := by
    induction xs with
    | nil => simp [lookup,Program.eval]
    | cons j js ih =>
      rw [lookup,eval_allGates]
      by_cases h : Q j
      · rw [if_pos ((eqv j).mpr h),if_pos (show ∃ k∈j::js,Q k from ⟨j,List.mem_cons_self,h⟩)]
        exact hit j (hs _ List.mem_cons_self) h
      · rw [if_neg (fun ht => h ((eqv j).mp ht)),ih (fun k hk => hs _ (List.mem_cons_of_mem _ hk))]
        simp [List.mem_cons,h]
  rw [run _ (fun j hj => Finset.mem_toList.mp hj)]
  split_ifs with h
  · rfl
  · exact no (by simpa only [Finset.mem_toList] using h)

def seed (d : OriginalData) : Program 3 :=
  lookup (HistoricalThirdCoarse.initial (d.e:ℝ)) (capValue (d.e:ℝ) d.m) (retained (d.e:ℝ) d.m).toList

def mode (d : OriginalData) : Program 3 :=
  allGates [LE (atom (X 0)) (atom (K VariableEnvelope.mu))]
    (lookup 0 (fun _ => 1) (retained (d.e:ℝ) d.m).toList) (atom (K 0))

theorem seed_at (d : OriginalData) (t : Fin 3 → ℝ) :
    (seed d).eval t=atPoint (d.e:ℝ) d.m t := by
  apply eval_lookup
  · intro j hj ht
    exact (atPoint_on_cell hj ht).symm
  · intro h
    simp [atPoint,h]

theorem mode_at (d : OriginalData) (t : Fin 3 → ℝ) :
    (mode d).eval t=if t 0≤VariableEnvelope.mu ∧ ∃ j∈retained (d.e:ℝ) d.m,
      t∈logPrimeMeshCell 0 (19/96) d.m j then 1 else 0 := by
  unfold mode
  rw [eval_allGates]
  simp only [passed_cons,passed_nil,holds_LE,Program.eval,Affine.eval_coord,Affine.eval_const,and_true]
  by_cases h : t 0≤VariableEnvelope.mu
  · rw [if_pos h]
    by_cases hs : ∃ j∈retained (d.e:ℝ) d.m,t∈logPrimeMeshCell 0 (19/96) d.m j
    · rw [if_pos ⟨h,hs⟩]
      exact eval_lookup _ _ _ _ 1 (by simp) (fun hn => (hn hs).elim)
    · rw [if_neg (fun H => hs H.2)]
      exact eval_lookup _ _ _ _ 0 (fun j hj ht => (hs ⟨j,hj,ht⟩).elim) (by simp)
  · rw [if_neg h,if_neg (fun H => h H.1)]

theorem tent_eval (u : Affine 3) (t : Fin 3 → ℝ) :
    (tent u).eval t = VariableEnvelope.v (u.eval t) := by
  simp [tent,Program.eval,VariableEnvelope.v_eq_min]

theorem common_exact (u : Affine 3) (t : Fin 3 → ℝ) :
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
  .sup (seed d) (allGates threeTests (tent yz) (allGates (common (X 1)) (tent (X 1)) (seed d)))

theorem static_root (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (h3 : (rosserAncestor 3 pre).length=3) (hp : 0<primeHistoryTuple 3 (rosserAncestor 3 pre) 2) :
    let t := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
    (seed d).eval t=(current d 0 N pre).scalar ∧
    ((mode d).eval t=1 ↔ (current d 0 N pre).lower) ∧
    (native d).eval t=P4AOriginalOrderedThirdFullPolicy.third (current d 0 N pre) N pre := by
  let t := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
  have ha : HistoricalThirdCoarse.active 0 N (rosserAncestor 3 pre) := ⟨h3,by
    rw [Real.rpow_zero]; exact_mod_cast (show 1≤primeHistoryTuple 3 (rosserAncestor 3 pre) 2 by omega)⟩
  have hseed : (seed d).eval t=(current d 0 N pre).scalar := by
    simp only [current,rawExponent,ha,if_true,seed_at,t]
  refine ⟨hseed,?_,?_⟩
  · rw [mode_at]
    change (if _ then (1:ℝ) else 0)=1 ↔ _ ∧ HistoricalThirdCoarse.active 0 N _ ∧ _
    simp only [ha,true_and]
    split_ifs <;> simp_all
  · have h2 (i : Fin 2) := primeHistoryLogCoordinates_ancestor N h3 (by omega : 2≤3) i
    simp only [rosserAncestor_nested 2 3 (by omega)] at h2
    have he : Passed t (common (X 1)) ↔ secondGuard N pre := by
      rw [common_exact]; simp [secondGuard,SecondRegion,t,h2]
    have ht : Passed t threeTests ↔ thirdGuard N pre := three_exact t
    change (native d).eval t=_
    simp only [native,Program.eval,eval_allGates,tent_eval,yz,Affine.eval_add,Affine.eval_coord,
      P4AOriginalOrderedThirdFullPolicy.third,hseed]
    by_cases htg : thirdGuard N pre <;> by_cases hsg : secondGuard N pre <;>
      simp only [show (∀ g∈threeTests,g.holds t) ↔ thirdGuard N pre from ht,
        show (∀ g∈common (X 1),g.holds t) ↔ secondGuard N pre from he,htg,hsg,if_true,if_false,h2,t]

end
end ImbalancedChen.P4AOrderedThirdStaticRootPrograms
