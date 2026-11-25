import ImbalancedChen.Part5OriginalH430PrimeObstructionBudget
import ImbalancedChen.Part5OriginalH430ArithmeticAtomRows

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original W2 N-masked half-open tuple carriers are split into strict
fresh interiors, lower-endpoint fibres, and interior old-prefix repeats.
Endpoint/repeat intersections belong ONLY to the endpoint lane.
All seven original occurrences, both fixed terms and the single /5 survive.
These strict tuple interiors are not yet identified with production
singleChildren/pairChildren or with the original selected count history.
-/
namespace ImbalancedChen.Part5OriginalH430W2DiscardedCarriers

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalOldProfilePrimeLimits
open P2OriginalBankOldProfilePassage P2OriginalChildPhysicalNormalization
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430PrimeObstructionBudget

def box (r N : ℕ) (L : ℝ) : Finset (Fin r → ℕ) :=
  actualPrimeBoxTuples N (fun _ : Fin r => L/10) (fun _ => 3*L/5)

def faces (p : W2Parameters) : Fin 3 → ℝ := ![a0 p, a1 p, a2 p]

def Fresh {r : ℕ} (d : ℕ) (q : Fin r → ℕ) : Prop := ∀ i, ¬ q i ∣ d

def singleInterior (p : W2Parameters) (k : Fin 3) (N : ℕ) (L : ℝ)
    (q : Fin 1 → ℕ) : Prop := normalizedLog N L q 0 ∈ W2SingletonDomain p k

def pairInterior (p : W2Parameters) (k : Fin 4) (N : ℕ) (L : ℝ)
    (q : Fin 2 → ℕ) : Prop := normalizedLog N L q ∈ W2PairDomain p k

def singleCarrier (N : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 3) :=
  (box 1 N L).filter (fun q => normalizedLog N L q ∈ singleHalf (a0 p) (singletonTop p k))

def pairCarrier (N : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 4) :=
  (box 2 N L).filter (fun q => normalizedLog N L q ∈ pairHalf p k)

def freshSingle (N d : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 3) :=
  (singleCarrier N L p k).filter (fun q => singleInterior p k N L q ∧ Fresh d q)

def freshPair (N d : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 4) :=
  (pairCarrier N L p k).filter (fun q => pairInterior p k N L q ∧ Fresh d q)

def removedSingle (N d : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 3) :=
  (singleCarrier N L p k).filter (fun q => ¬ (singleInterior p k N L q ∧ Fresh d q))

def removedPair (N d : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 4) :=
  (pairCarrier N L p k).filter (fun q => ¬ (pairInterior p k N L q ∧ Fresh d q))

/-- Endpoints have priority; the repeat lane tests strict interior first. -/
theorem removed_partition {ι : Type*} (T : Finset ι) (interior fresh : ι → Prop) :
    T.filter (fun q => ¬ (interior q ∧ fresh q)) =
      T.filter (fun q => ¬ interior q) ∪ T.filter (fun q => interior q ∧ ¬ fresh q) ∧
    Disjoint (T.filter (fun q => ¬ interior q)) (T.filter (fun q => interior q ∧ ¬ fresh q)) := by
  constructor
  · ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  · apply Finset.disjoint_left.mpr
    intro q hq hr
    exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hr).2.1

/-- Every signed finite test is preserved, before any absolute estimate. -/
theorem single_sum_split (N d : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 3)
    (F : (Fin 1 → ℕ) → ℝ) :
    (∑ q ∈ singleCarrier N L p k, F q) =
      (∑ q ∈ freshSingle N d L p k, F q) + ∑ q ∈ removedSingle N d L p k, F q := by
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem pair_sum_split (N d : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 4)
    (F : (Fin 2 → ℕ) → ℝ) :
    (∑ q ∈ pairCarrier N L p k, F q) =
      (∑ q ∈ freshPair N d L p k, F q) + ∑ q ∈ removedPair N d L p k, F q := by
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem normalizedLog_coordinate {r : ℕ} (N : ℕ) (L : ℝ) (q : Fin r → ℕ) (i : Fin r) :
    normalizedLog N L q i = logCoordinate N L (q i) := by
  change L⁻¹ * (Real.log (q i : ℝ) / Real.log (N : ℝ)) =
    (Real.log (q i : ℝ) / Real.log (N : ℝ)) / L
  ring

/-- The original box already deletes divisors of N; Fresh adds exactly
old-prefix coprimality, not a changed prime window or a selected mask. -/
theorem fresh_iff_coprime {r N d : ℕ} {L : ℝ} {q : Fin r → ℕ}
    (hq : q ∈ box r N L) : Fresh d q ↔ ∀ i, (q i).Coprime (N*d) := by
  constructor
  · intro hf i
    have hp := mem_actualPrimeBoxTuples_iff.mp hq i
    exact Nat.coprime_mul_iff_right.mpr
      ⟨hp.1.coprime_iff_not_dvd.mpr hp.2.1, hp.1.coprime_iff_not_dvd.mpr (hf i)⟩
  · intro hf i
    have hp := mem_actualPrimeBoxTuples_iff.mp hq i
    exact hp.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp (hf i)).2

theorem singleton_domain (p : W2Parameters) (k : Fin 3) :
    W2SingletonDomain p k = Ioo (a0 p) (singletonTop p k) := by
  fin_cases k <;> rfl

theorem removedSingle_obstructed {N d : ℕ} {L : ℝ} {p : W2Parameters} {k : Fin 3}
    {q : Fin 1 → ℕ} (hq : q ∈ removedSingle N d L p k) :
    obstructed N d L (faces p) (q 0) := by
  obtain ⟨hq, hnot⟩ := Finset.mem_filter.mp hq
  have hx := (Finset.mem_filter.mp hq).2
  by_cases hpd : q 0 ∣ d
  · exact Or.inl hpd
  · by_cases he : normalizedLog N L q 0 = a0 p
    · exact Or.inr (Or.inl (by simpa [faces, normalizedLog_coordinate] using he))
    · exfalso
      apply hnot
      constructor
      · rw [singleInterior, singleton_domain]
        exact ⟨lt_of_le_of_ne hx.1 (Ne.symm he),hx.2⟩
      · intro i
        fin_cases i
        exact hpd

theorem removedPair_obstructed {N d : ℕ} {L : ℝ} {p : W2Parameters} {k : Fin 4}
    {q : Fin 2 → ℕ} (hq : q ∈ removedPair N d L p k) :
    obstructed N d L (faces p) (q 0) ∨ obstructed N d L (faces p) (q 1) := by
  obtain ⟨hq, hnot⟩ := Finset.mem_filter.mp hq
  have hx := (Finset.mem_filter.mp hq).2
  by_cases h0 : q 0 ∣ d
  · exact Or.inl (Or.inl h0)
  · by_cases h1 : q 1 ∣ d
    · exact Or.inr (Or.inl h1)
    · have hf : Fresh d q := by intro i; fin_cases i <;> assumption
      have hout : normalizedLog N L q ∉ W2PairDomain p k := fun h => hnot ⟨h,hf⟩
      have hw := ((pairHalf_partition p k _).mp hx).resolve_left hout
      have hwall := hw.2
      fin_cases k
      · exact Or.inl (Or.inr (Or.inl (by simpa [faces, pairLowerWall, normalizedLog_coordinate] using hwall)))
      · rcases hwall with he | he
        · exact Or.inl (Or.inr (Or.inl (by simpa [faces, normalizedLog_coordinate] using he)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa [faces, normalizedLog_coordinate] using he))))
      · exact Or.inl (Or.inr (Or.inl (by simpa [faces, pairLowerWall, normalizedLog_coordinate] using hwall)))
      · rcases hwall with he | he
        · exact Or.inl (Or.inr (Or.inl (by simpa [faces, normalizedLog_coordinate] using he)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [faces, normalizedLog_coordinate] using he))))

/-- The enclosing box supplies both the true prime floor and q<=N.
No assumption about the number of its prime tuples is used. -/
theorem box_in_primePool {r N : ℕ} {L A : ℝ} (hN : 1 < N)
    (hL : L ≤ 1) (hA : A ≤ (N : ℝ)^(L/10))
    {q : Fin r → ℕ} (hq : q ∈ box r N L) (i : Fin r) : q i ∈ primePool N A := by
  have hp := mem_actualPrimeBoxTuples_iff.mp hq i
  have hexp : 3*L/5 ≤ 1 := by linarith
  have hcap : (N : ℝ)^(3*L/5) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN.le) hexp
  exact mem_primePool.mpr ⟨hp.1.pos, by exact_mod_cast hp.2.2.2.le.trans hcap,
    hp.1, hA.trans hp.2.2.1⟩

def singleTerm (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters) (b : FloorAtom)
    (q : Fin 1 → ℕ) : ℝ :=
  if singleRho p.s0 (normalizedLog N L q) ∈ tableAtomSet true b then
    thetaAtom N Q (d*q 0) else 0

def pairTerm (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters) (k : Fin 4)
    (b : FloorAtom) (q : Fin 2 → ℕ) : ℝ :=
  if pairProfile p k (normalizedLog N L q) ∈ tableAtomSet false b then
    thetaAtom N Q (d*q 0*q 1) else 0

def freshSingleAtom (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters) (k : Fin 3)
    (b : FloorAtom) : ℝ := ∑ q ∈ freshSingle N d L p k, singleTerm N Q L d p b q

def freshPairAtom (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters) (k : Fin 4)
    (b : FloorAtom) : ℝ := ∑ q ∈ freshPair N d L p k, pairTerm N Q L d p k b q

def removedSingleAtom (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters) (k : Fin 3)
    (b : FloorAtom) : ℝ := ∑ q ∈ removedSingle N d L p k, singleTerm N Q L d p b q

def removedPairAtom (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters) (k : Fin 4)
    (b : FloorAtom) : ℝ := ∑ q ∈ removedPair N d L p k, pairTerm N Q L d p k b q

theorem singleChildAtom_split (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters)
    (k : Fin 3) (b : FloorAtom) :
    singleChildAtom N Q L d (a0 p) (singletonTop p k) p.s0 b =
      freshSingleAtom N Q L d p k b + removedSingleAtom N Q L d p k b := by
  rw [← single_sum_split N d L p k (singleTerm N Q L d p b)]
  simp only [singleChildAtom, profileAtomSum, singleCarrier, Finset.sum_filter, box]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hx : normalizedLog N L q ∈ singleHalf (a0 p) (singletonTop p k)
  · by_cases hb : singleRho p.s0 (normalizedLog N L q) ∈ tableAtomSet true b
    all_goals simp [singleTerm, tablePullback, hx, hb]
  · simp [hx, tablePullback]

theorem pairChildAtom_split (N : ℕ) (Q L : ℝ) (d : ℕ) (p : W2Parameters)
    (k : Fin 4) (b : FloorAtom) :
    pairChildAtom N Q L d p k b = freshPairAtom N Q L d p k b + removedPairAtom N Q L d p k b := by
  rw [← pair_sum_split N d L p k (pairTerm N Q L d p k b)]
  simp only [pairChildAtom, profileAtomSum, pairCarrier, Finset.sum_filter, box]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hx : normalizedLog N L q ∈ pairHalf p k
  · by_cases hb : pairProfile p k (normalizedLog N L q) ∈ tableAtomSet false b
    all_goals simp [pairTerm, tablePullback, hx, hb]
  · simp [hx, tablePullback]

def freshRow (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) : RowAtom → ℝ
  | .inl b => (4*pointAtom (thetaAtom N Q d) false (originalW2At j).s0 b +
      pointAtom (thetaAtom N Q d) false (originalW2At j).phi1 b +
      ∑ k : Fin 4, freshPairAtom N Q L d (originalW2At j) k b)/5
  | .inr b => (∑ k : Fin 3, freshSingleAtom N Q L d (originalW2At j) k b)/5

def removedRow (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) : RowAtom → ℝ
  | .inl b => (∑ k : Fin 4, removedPairAtom N Q L d (originalW2At j) k b)/5
  | .inr b => (∑ k : Fin 3, removedSingleAtom N Q L d (originalW2At j) k b)/5

/-- Fixed 4/5 and 1/5 terms are unchanged; the seven feedback occurrences
are kept in their original order, each with its original single /5. -/
theorem arithmeticRow_split (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (b : RowAtom) :
    arithmeticRow N Q L d (.inr j) b = freshRow N Q L d j b + removedRow N Q L d j b := by
  cases b with
  | inl b =>
      simp only [arithmeticRow, freshRow, removedRow, pairChildAtom_split, Finset.sum_add_distrib]
      ring
  | inr b =>
      simp only [arithmeticRow, freshRow, removedRow, singleChildAtom_split, Finset.sum_add_distrib]
      ring

end
end ImbalancedChen.Part5OriginalH430W2DiscardedCarriers
