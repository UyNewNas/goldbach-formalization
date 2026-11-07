import ImbalancedChen.Part5OriginalH430W2ProductionReindex

/-!
SOURCE ONLY / UNCOMPILED.

The new rows enumerate the actual production singleChildren/pairChildren,
read the query of perform at the original physical node, and weight the
actual appended integer word. The two fixed occurrences and all seven
feedback occurrences retain their single /5. Equalities are finite and
pointwise, including closed query knots; no limit or count licence is data.
-/
namespace ImbalancedChen.Part5OriginalH430W2ProductionRows

noncomputable section
open Set Classical
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalHalfOpenProfileCarrier
open P2OriginalOldProfilePrimeLimits
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PrimeChildAdmission Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430W2DiscardedCarriers
open Part5OriginalH430W2ProductionGeometry Part5OriginalH430W2ProductionReindex

theorem single_query_eq {N q : ℕ} {Q chi : ℝ} {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi) (hL : residual p = physicalLevel N Q old)
    (j : Fin 36) (k : Fin 3) :
    (perform p (.w2Singleton j k) (singleCoordinates N q)).argument =
      singleRho (originalW2At j).s0
        (normalizedLog N (physicalLevel N Q old) (singleTuple q)) := by
  change singletonProfile (originalW2At j).s0 (normalized p (singleCoordinates N q) 0) = _
  rw [actual_normalized_single hw hL]
  change (originalW2At j).s0*(1-relativePrime Q old q) =
    (originalW2At j).s0*(1-normalizedLog N (physicalLevel N Q old) (singleTuple q) 0)
  rw [normalized_eq_relative hw]
  rfl

theorem pair_query_eq {N small large : ℕ} {Q chi : ℝ} {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old chi) (hL : residual p = physicalLevel N Q old)
    (j : Fin 36) (k : Fin 4) :
    (perform p (.w2Pair j k) (pairCoordinates N small large)).argument =
      pairProfile (originalW2At j) k
        (normalizedLog N (physicalLevel N Q old) (pairTuple small large)) := by
  change pairProfile (originalW2At j) k (normalized p (pairCoordinates N small large)) = _
  rw [actual_normalized_pair hw hL, normalized_pair_eq hw]

/-- This equality keeps the entire ordered old word, not only its product. -/
theorem single_word_eq {N q : ℕ} {old : List ℕ} {p : PhysicalNode}
    (hword : word p = old.map (physicalPrime N)) (j : Fin 36) (k : Fin 3) :
    word (perform p (.w2Singleton j k) (singleCoordinates N q)) =
      (singleWord old q).map (physicalPrime N) := by
  simp only [perform, word_appendOne, hword, singleCoordinates,
    Matrix.cons_val_zero, singleWord, List.map_append, List.map_cons, List.map_nil]

theorem pair_word_eq {N small large : ℕ} {old : List ℕ} {p : PhysicalNode}
    (hword : word p = old.map (physicalPrime N)) (j : Fin 36) (k : Fin 4) :
    word (perform p (.w2Pair j k) (pairCoordinates N small large)) =
      (pairWord old small large).map (physicalPrime N) := by
  simp only [perform, word_appendPair, hword, pairCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one, pairWord,
    List.map_append, List.map_cons, List.map_nil]

def productionSingleAtom (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (k : Fin 3) (a : FloorAtom) : ℝ :=
  ∑ q ∈ singleChildren (.w2 j k) N Q old p.ceiling,
    if (perform p (.w2Singleton j k) (singleCoordinates N q.val)).argument ∈
        tableAtomSet true a then thetaAtom N Q (parentProduct (singleWord old q.val)) else 0

def productionPairAtom (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (k : Fin 4) (a : FloorAtom) : ℝ :=
  ∑ q ∈ pairChildren j k N Q old p.ceiling,
    if (perform p (.w2Pair j k) (pairCoordinates N q.1.val q.2.val)).argument ∈
        tableAtomSet false a then
      thetaAtom N Q (parentProduct (pairWord old q.1.val q.2.val)) else 0

theorem productionSingleAtom_eq {N : ℕ} {Q : ℝ} {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old p.ceiling) (hL : residual p = physicalLevel N Q old)
    (j : Fin 36) (k : Fin 3)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ p.ceiling) (a : FloorAtom) :
    productionSingleAtom N Q old p j k a =
      freshSingleAtom N Q (physicalLevel N Q old) (parentProduct old) (originalW2At j) k a := by
  rw [freshSingleAtom, freshSingle_sum_eq_production hw j k hceil]
  unfold productionSingleAtom
  apply Finset.sum_congr rfl
  intro q _
  rw [single_query_eq hw hL j k]
  have hprod : parentProduct (singleWord old q.val) = parentProduct old*q.val :=
    (singleWord_history old q.val).2.2
  simp only [singleTerm, singleTuple, hprod]

theorem productionPairAtom_eq {N : ℕ} {Q : ℝ} {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old p.ceiling) (hL : residual p = physicalLevel N Q old)
    (j : Fin 36) (k : Fin 4)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ p.ceiling) (a : FloorAtom) :
    productionPairAtom N Q old p j k a =
      freshPairAtom N Q (physicalLevel N Q old) (parentProduct old) (originalW2At j) k a := by
  rw [freshPairAtom, freshPair_sum_eq_production hw j k hceil]
  unfold productionPairAtom
  apply Finset.sum_congr rfl
  intro q _
  rw [pair_query_eq hw hL j k]
  have hprod : parentProduct (pairWord old q.1.val q.2.val) =
      parentProduct old*q.1.val*q.2.val := by
    change (pairWord old q.1.val q.2.val).prod = _
    rw [(pairWord_history old q.1.val q.2.val).2.2]
    ac_rfl
  simp only [pairTerm, pairTuple, Matrix.cons_val_zero, Matrix.cons_val_one, hprod]

def productionRow (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) : RowAtom → ℝ
  | .inl a => (4*pointAtom (thetaAtom N Q (parentProduct old)) false (originalW2At j).s0 a +
      pointAtom (thetaAtom N Q (parentProduct old)) false (originalW2At j).phi1 a +
      ∑ k : Fin 4, productionPairAtom N Q old p j k a)/5
  | .inr a => (∑ k : Fin 3, productionSingleAtom N Q old p j k a)/5

/-- Exact row equality, including fixed terms. No second endpoint/repeat
payment is introduced when moving the preceding estimate to production. -/
theorem productionRow_eq_freshRow {N : ℕ} {Q : ℝ} {old : List ℕ} {p : PhysicalNode}
    (hw : parentWindow N Q old p.ceiling) (hL : residual p = physicalLevel N Q old)
    (j : Fin 36) (hceil : physicalLevel N Q old/(originalW2At j).s ≤ p.ceiling)
    (a : RowAtom) : productionRow N Q old p j a =
      freshRow N Q (physicalLevel N Q old) (parentProduct old) j a := by
  have hsingle (k : Fin 3) (a : FloorAtom) := productionSingleAtom_eq hw hL j k hceil a
  have hpair (k : Fin 4) (a : FloorAtom) := productionPairAtom_eq hw hL j k hceil a
  cases a <;> simp only [productionRow, freshRow, hsingle, hpair]

theorem originalRow_eq_production_add_removed {N : ℕ} {Q : ℝ} {old : List ℕ}
    {p : PhysicalNode} (hw : parentWindow N Q old p.ceiling)
    (hL : residual p = physicalLevel N Q old) (j : Fin 36)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ p.ceiling) (a : RowAtom) :
    arithmeticRow N Q (physicalLevel N Q old) (parentProduct old) (.inr j) a =
      productionRow N Q old p j a +
      removedRow N Q (physicalLevel N Q old) (parentProduct old) j a := by
  rw [productionRow_eq_freshRow hw hL j hceil]
  exact arithmeticRow_split _ _ _ _ _ _

/-- Raw production profile: query values come from perform, weights from
the ordered appended word, and arrays remain arbitrary old arrays. -/
def productionProfile (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (oldH oldh : Fin 200 → ℤ) : ℝ :=
  (4*thetaAtom N Q (parentProduct old)*tableFunction false oldH (originalW2At j).s0 +
    thetaAtom N Q (parentProduct old)*tableFunction false oldH (originalW2At j).phi1 +
    (∑ k : Fin 4, ∑ q ∈ pairChildren j k N Q old p.ceiling,
      thetaAtom N Q (parentProduct (pairWord old q.1.val q.2.val)) *
        tableFunction false oldH
          (perform p (.w2Pair j k) (pairCoordinates N q.1.val q.2.val)).argument) +
    (∑ k : Fin 3, ∑ q ∈ singleChildren (.w2 j k) N Q old p.ceiling,
      thetaAtom N Q (parentProduct (singleWord old q.val)) *
        tableFunction true oldh
          (perform p (.w2Singleton j k) (singleCoordinates N q.val)).argument))/5

private theorem indicator_atom_value (theta s : ℝ) (lower : Bool) (nums : Fin 200 → ℤ) :
    (∑ a : FloorAtom, (if s ∈ tableAtomSet lower a then theta else 0)*floorAtomValue nums a) =
      theta*tableFunction lower nums s := by
  calc
    _ = ∑ a : FloorAtom, pointAtom theta lower s a*floorAtomValue nums a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : s ∈ tableAtomSet lower a <;> simp [pointAtom,ha]
    _ = _ := pointAtom_value _ _ _ _

theorem productionSingleAtom_value (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (k : Fin 3) (nums : Fin 200 → ℤ) :
    (∑ a : FloorAtom, productionSingleAtom N Q old p j k a*floorAtomValue nums a) =
      ∑ q ∈ singleChildren (.w2 j k) N Q old p.ceiling,
        thetaAtom N Q (parentProduct (singleWord old q.val)) *
          tableFunction true nums (perform p (.w2Singleton j k) (singleCoordinates N q.val)).argument := by
  simp only [productionSingleAtom, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  exact indicator_atom_value _ _ _ _

theorem productionPairAtom_value (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (k : Fin 4) (nums : Fin 200 → ℤ) :
    (∑ a : FloorAtom, productionPairAtom N Q old p j k a*floorAtomValue nums a) =
      ∑ q ∈ pairChildren j k N Q old p.ceiling,
        thetaAtom N Q (parentProduct (pairWord old q.1.val q.2.val)) *
          tableFunction false nums (perform p (.w2Pair j k)
            (pairCoordinates N q.1.val q.2.val)).argument := by
  simp only [productionPairAtom, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  exact indicator_atom_value _ _ _ _

theorem productionRow_value (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (j : Fin 36) (oldH oldh : Fin 200 → ℤ) :
    (∑ a : RowAtom, productionRow N Q old p j a*oldAtomValue oldH oldh a) =
      productionProfile N Q old p j oldH oldh := by
  have hp : (∑ a : FloorAtom,
      (∑ k : Fin 4, productionPairAtom N Q old p j k a)*floorAtomValue oldH a) =
      ∑ k : Fin 4, ∑ q ∈ pairChildren j k N Q old p.ceiling,
        thetaAtom N Q (parentProduct (pairWord old q.1.val q.2.val)) *
          tableFunction false oldH
            (perform p (.w2Pair j k) (pairCoordinates N q.1.val q.2.val)).argument := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [productionPairAtom_value]
  have hs : (∑ a : FloorAtom,
      (∑ k : Fin 3, productionSingleAtom N Q old p j k a)*floorAtomValue oldh a) =
      ∑ k : Fin 3, ∑ q ∈ singleChildren (.w2 j k) N Q old p.ceiling,
        thetaAtom N Q (parentProduct (singleWord old q.val)) *
          tableFunction true oldh
            (perform p (.w2Singleton j k) (singleCoordinates N q.val)).argument := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [productionSingleAtom_value]
  simp only [Fintype.sum_sum_type, productionRow, oldAtomValue]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [pointAtom_value, pointAtom_value, hp, hs]
  unfold productionProfile
  ring

end
end ImbalancedChen.Part5OriginalH430W2ProductionRows
