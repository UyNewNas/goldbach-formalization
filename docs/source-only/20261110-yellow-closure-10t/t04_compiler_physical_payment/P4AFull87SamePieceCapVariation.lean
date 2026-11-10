import ImbalancedChen.P4AFull87VariableSeedHistory
import ImbalancedChen.P4AFull87LicensedPhysicalSupport

namespace ImbalancedChen.P4AFull87SamePieceCapVariation
noncomputable section
open scoped Classical BigOperators
open P4AFull87VariableSeedHistory P1FiniteAffineDecisionProgram
open P4AOriginalCompleteSixthChronology (data currentSixthExponent)
open P4AFull87CompilerChangedPartition P4AUpperTaggedParityCompiler
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P5OriginalCommonRefinedConstructor (OriginalData)

abbrev prog (d : OriginalData) (c : SeedCode d) := variableCompleteProgram d (third d c)
abbrev History (d : OriginalData) := Σ c : SeedCode d, (prog d c).Signature
abbrev plane (d : OriginalData) (h : History d) := (prog d h.1).table h.2

def observation (d : OriginalData) (N : ℝ) (pre : List ℕ) : History d :=
  let c := seedCode d N pre
  ⟨c,(prog d c).signature (primeHistoryLogCoordinates N 6 pre)⟩

def variation (d : OriginalData) : ℝ :=
  1 + ∑ h : History d, ∑ i, |(plane d h).coefficient i|

def readWord {α : Type*} [Fintype α] (a : α) : List Bool :=
  List.ofFn fun i : Fin (Fintype.card α) => decide (a = (Fintype.equivFin α).symm i)

theorem word_inj {α : Type*} [Fintype α] {a b : α}
    (h : readWord a = readWord b) : a = b := by
  unfold readWord at h
  have hh := congrFun (List.ofFn_injective h)
    ((Fintype.equivFin α) a)
  have ha : decide (a=a) = decide (b=a) := by simpa only [Equiv.symm_apply_apply] using hh
  exact (of_decide_eq_true (ha.symm.trans (decide_eq_true rfl))).symm

def capWord (P : Parameters) (N x : ℕ) : List Bool :=
  readWord (observation (data P.e P.q P.om) (N : ℝ) (rosserAncestor 6 x.primeFactorsList))

/-- Keep the existing earliest-history suffix as well as the entire
finite native strict/closed affine decision signature at the own sixth. -/
def refined (P : Parameters) (N x : ℕ) : List Bool :=
  capWord P N x ++ P4AFull87HistoricalChangedSupport.suffix P N x

theorem both_reads (P : Parameters) (N : ℕ) {x y : ℕ}
    (hh : P.tags N (refined P N) x = P.tags N (refined P N) y) :
    P.tags N (P4AFull87HistoricalChangedSupport.suffix P N) x =
      P.tags N (P4AFull87HistoricalChangedSupport.suffix P N) y ∧
    observation (data P.e P.q P.om) (N : ℝ) (rosserAncestor 6 x.primeFactorsList) =
      observation (data P.e P.q P.om) (N : ℝ) (rosserAncestor 6 y.primeFactorsList) := by
  let B := Fintype.card (P4AFull87CompilerCapRead.Stage ×
    (P4AFull87CompilerCapRead.levels P.n P.e P.q : Type))
  let C := Fintype.card (History (data P.e P.q P.om))
  have lb (s : ℕ) : (P4AFull87CompilerCapRead.bits P.delta P.n P.e P.q P.om (N : ℝ) s).length = B := List.length_ofFn
  have lc (s : ℕ) : (capWord P N s).length = C := List.length_ofFn
  have hbits := congrArg (List.take B) hh
  have hs := congrArg (List.drop B) hh
  simp only [Parameters.tags,P4AFull87CompilerCapRead.tag,List.take_left' (lb x),
    List.take_left' (lb y)] at hbits
  simp only [Parameters.tags,P4AFull87CompilerCapRead.tag,List.drop_left' (lb x),
    List.drop_left' (lb y),refined] at hs
  have hbase := congrArg (List.drop C) hs
  have hnew := congrArg (List.take C) hs
  simp only [List.drop_left' (lc x),List.drop_left' (lc y)] at hbase
  simp only [List.take_left' (lc x),List.take_left' (lc y)] at hnew
  exact ⟨congrArg₂ List.append hbits hbase,word_inj hnew⟩

theorem affine_diff {k : ℕ} (a : Affine k) (x y : Fin k → ℝ)
    (t : ℝ) (h : ∀ i, |x i-y i| ≤ t) :
    |a.eval x-a.eval y| ≤ (∑ i, |a.coefficient i|)*t := by
  have he : a.eval x-a.eval y = ∑ i, a.coefficient i*(x i-y i) := by
    simp only [Affine.eval,mul_sub,Finset.sum_sub_distrib]; ring
  rw [he,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

theorem coord_ancestor {r x : ℕ} (hx : r ≤ x.primeFactorsList.length) (N : ℕ) :
    primeHistoryLogCoordinates (N : ℝ) r (rosserAncestor r x.primeFactorsList) =
      actualPrimeTupleLog N (canonicalPrefix r x) := by
  have hrev : (rosserAncestor r x.primeFactorsList).reverse = x.primeFactorsList.reverse.take r := by
    simp only [rosserAncestor,List.reverse_drop]
    congr 1
    omega
  have ha := congrArg List.reverse hrev
  simp only [List.reverse_reverse] at ha
  rw [ha]
  rfl

/-- One pre-N finite policy constant, independent of the fine width and
of the roughness used for the compiler. This holds on every rank-six
ancestor, including the corrected fallback and unsupported third. -/
theorem same_cell_current_variation (P : Parameters) (N cap : ℕ) (w z tau : ℝ)
    (ht : 0 < tau) {x y : ℕ}
    (hy : y ∈ cell (P.tags N (refined P N)) N cap w z tau x)
    (hx : 6 ≤ x.primeFactorsList.length) :
    |currentSixthExponent P.e P.q P.om (N : ℝ) (rosserAncestor 6 x.primeFactorsList) -
      currentSixthExponent P.e P.q P.om (N : ℝ) (rosserAncestor 6 y.primeFactorsList)| ≤
      variation (data P.e P.q P.om)*tau := by
  let d := data P.e P.q P.om
  let pre (s : ℕ) := rosserAncestor 6 s.primeFactorsList
  let obs (s : ℕ) := observation d (N:ℝ) (pre s)
  let t (s : ℕ) := primeHistoryLogCoordinates (N:ℝ) 6 (pre s)
  have hsame : obs y = obs x := (both_reads P N (cell_frozen_tag _ _ _ _ _ _ hy)).2
  have hyl : 6 ≤ y.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hy]; exact hx
  have hh (s : ℕ) (hl : 6 ≤ s.primeFactorsList.length) :
      (plane d (obs s)).eval (t s) =
        currentSixthExponent P.e P.q P.om (N : ℝ) (pre s) := by
    apply (Program.table_exact _ _).trans
    exact complete_at_own_six P.e P.q P.om (N : ℝ) (pre s) (by simp [pre,Nat.min_eq_left hl])
  rw [← hh x hx, ← hh y hyl,hsame]
  have hcoord (i : Fin 6) : |t x i - t y i| ≤ tau := by
    dsimp only [t,pre]
    rw [coord_ancestor hx,coord_ancestor hyl]
    exact (same_primeLabel_coordinate_distance_lt N ht
      (cell_canonicalPrefix_label_eq _ _ _ _ _ _ hy hx i)).le
  apply (affine_diff _ _ _ tau hcoord).trans
  apply mul_le_mul_of_nonneg_right _ ht.le
  have hm := Finset.single_le_sum (s := Finset.univ) (f := fun h : History d =>
    ∑ i, |(plane d h).coefficient i|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (Finset.mem_univ (obs x))
  dsimp only [variation]
  linarith

end
end ImbalancedChen.P4AFull87SamePieceCapVariation
