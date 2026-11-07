import ImbalancedChen.P4AOriginalSaving19BankExhaustion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact prime/log dictionary for G's selected list. The selected
frontier is not replaced by a set: all incoming signs, masses, remaining
carriers and repeated occurrences remain available to an arbitrary
signed state test. No prime mean or prior numerical gain is inferred.
-/

namespace ImbalancedChen.P4AOriginalSaving19BankFrontier

noncomputable section
open scoped Classical BigOperators
open P4AOriginalLive171819Atlas P4AOriginalLive171819CommonParent
open P4AOriginalLive171819PrimeBank P4AOriginalCell0HalfOpenPrimeCarrier
open P4AOriginalSaving19BankExhaustion P4AOriginalSaving19CommonHistory
open P5OriginalCommonRefinedConstructor P2OriginalSaving19HistoricalMinorant
open P2OriginalThirdMinorantLogDictionarySourceOnly

/-- Real frontier membership supplies primality and target exclusion;
the existing power-box dictionary supplies both endpoint directions. -/
theorem frontier_primeBox_iff (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8 parent (fun p => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap w z)) (m : ℕ) (j : BoxIndex m) :
    primeHistoryTuple 8 s.selectedPrefix ∈ primeBox m N j ↔
      point8 (N : ℝ) s.selectedPrefix ∈ logPrimeMeshCell 0 (19 / 96) m j := by
  have hp (k : Fin 8) := primeHistoryTuple_frontier_mem 8 parent
    (fun p => 1 / ((p : ℝ) - 1)) N cap w z s hs k
  change primeHistoryTuple 8 s.selectedPrefix ∈ actualPrimeBoxTuples N _ _ ↔ _
  rw [mem_actualPrimeBoxTuples_log_iff hN]
  constructor
  · exact fun h => h.2
  · intro ht
    exact ⟨fun k => ⟨mem_roughPrimeUniverse_prime (hp k),
      mem_roughPrimeUniverse_not_dvd (hp k)⟩, ht⟩

/-- Exact membership in G's existing list, with a genuine original
frontier on the right. This does not manufacture frontier admission. -/
theorem selected_iff_frontier_bankRegion (i : Fin 13) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) (s : FirstExitDepthState ℕ) :
    s ∈ selected (.ascending19 i) e chi m omega N cap w z parent ↔
      s ∈ firstExitDepthFrontier 8 parent (fun p => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap w z) ∧
        point8 (N : ℝ) s.selectedPrefix ∈ bankRegion i e chi m omega := by
  simp only [selected, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, j, hj, hp⟩
    exact ⟨hs, j, hj, (frontier_primeBox_iff N cap hN w z parent s hs m j).mp hp⟩
  · rintro ⟨hs, j, hj, ht⟩
    exact ⟨hs, j, hj, (frontier_primeBox_iff N cap hN w z parent s hs m j).mpr ht⟩

private theorem sum_filter_decide {α : Type*} (L : List α) (P : α → Prop)
    (f : α → ℝ) :
    ((L.filter (fun a => decide (P a))).map f).sum =
      (L.map (fun a => if P a then f a else 0)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      by_cases h : P a <;> simp [h, ih]

private theorem sum_indicator_congr {α : Type*} (L : List α) (P Q : α → Prop)
    (f : α → ℝ) (h : ∀ a ∈ L, P a ↔ Q a) :
    (L.map (fun a => if P a then f a else 0)).sum =
      (L.map (fun a => if Q a then f a else 0)).sum := by
  revert h
  induction L with
  | nil => intro h; simp
  | cons a L ih =>
      intro h
      have ha := h a (by simp)
      have hL : ∀ b ∈ L, P b ↔ Q b := fun b hb => h b (by simp [hb])
      simp only [List.map_cons, List.sum_cons]
      rw [ih hL, ha]

/-- Exact signed sum dictionary with original LIST multiplicity. The
test may read sign, mass, prefix, or remaining primes of the same state.
No positivity or coefficientwise monotonicity assumption is imposed. -/
theorem selected_signed_sum (i : Fin 13) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (N cap : ℕ) (hN : 1 < N) (w z : ℝ)
    (parent : Bool → List ℕ → Bool) (f : FirstExitDepthState ℕ → ℝ) :
    ((selected (.ascending19 i) e chi m omega N cap w z parent).map f).sum =
      ((firstExitDepthFrontier 8 parent (fun p => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap w z)).map
        (fun s => if point8 (N : ℝ) s.selectedPrefix ∈ bankRegion i e chi m omega
          then f s else 0)).sum := by
  unfold selected
  rw [sum_filter_decide]
  apply sum_indicator_congr
  intro s hs
  constructor
  · rintro ⟨j, hj, hp⟩
    exact ⟨j, hj, (frontier_primeBox_iff N cap hN w z parent s hs m j).mp hp⟩
  · rintro ⟨j, hj, ht⟩
    exact ⟨j, hj, (frontier_primeBox_iff N cap hN w z parent s hs m j).mpr ht⟩

/-- The original arithmetic dictionary can now be entered from the
geometric footprint on the same actual common-policy frontier. The
actual current sixth parent is retained, not equated to comparison R. -/
theorem bankRegion_actual_parent_dictionary
    (i : Fin 13) (d : OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8 (policy8 d (N : ℝ))
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z))
    (ht : point8 (N : ℝ) s.selectedPrefix ∈ bankRegion i d.e d.chi d.m d.omega)
    {δ : ℝ} (hδ : 0 < δ) (hm : δ ≤ historyMargin (point8 (N : ℝ) s.selectedPrefix))
    (heδ : (d.e : ℝ) ≤ δ / 16) (hegate : (d.e : ℝ) ≤ 3 / 256) (hchi : d.chi ≤ δ / 16) :
    history7 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
      lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ≤
        lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∧
      lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ≤
        comparisonCap (point8 (N : ℝ) s.selectedPrefix) ∧
      conservativeDensity (point8 (N : ℝ) s.selectedPrefix) ≤
        parentDensity (lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))
          (point8 (N : ℝ) s.selectedPrefix) := by
  have hsel := (selected_iff_frontier_bankRegion i d.e d.chi d.m d.omega N cap hN w z
    (policy8 d (N : ℝ)) s).mpr ⟨hs, ht⟩
  exact selected_saving19_actual_parent_dictionary i d he N cap hN w z s hsel
    hδ hm heδ hegate hchi

end
end ImbalancedChen.P4AOriginalSaving19BankFrontier
