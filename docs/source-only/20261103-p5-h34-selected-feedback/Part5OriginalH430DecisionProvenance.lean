import ImbalancedChen.P2Selected430CausalOccurrenceExporter

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Full provenance of the EXISTING seed-only interpreter. All three choice
constructors are covered, with strict-update tie handling unchanged.
This is a theorem about the literal scalar producer, not a count licence.
-/
namespace ImbalancedChen.Part5OriginalH430DecisionProvenance

noncomputable section
open scoped Classical BigOperators
open P2Selected430LiteralActionData (Row rows q)
open P2Selected430CausalOccurrenceExporter

def buchstabValue (old : Table) (up : Bool) (i : Fin 200) : ℤ :=
  if up then suffix old false (max 50 (i.val-49))
  else suffix old true (i.val-49)

def choiceValue (old : Table) (up : Bool) (i : Fin 200) : Choice → ℤ
  | .retained => old up i
  | .buchstab => buchstabValue old up i
  | .bank k => candidate old (rows k)

def choiceAllowed (up : Bool) (i : Fin 200) : Choice → Prop
  | .retained => True
  | .buchstab => 50 ≤ i.val
  | .bank k => up = true ∧ i.val ∈ (rows k).targets

def provenance (old : Table) (up : Bool) (i : Fin 200) (d : Decision) : Prop :=
  choiceAllowed up i d.choice ∧ d.numerator = choiceValue old up i d.choice

/-- Equal offers preserve the earlier owner, not just its value. -/
theorem offer_tie (d : Decision) (c : Choice) : offer d d.numerator c = d := by
  simp [offer]

theorem ordinary_provenance (old : Table) (up : Bool) (i : Fin 200) :
    provenance old up i (ordinaryDecision old up i) := by
  by_cases hi : 50 ≤ i.val
  · simp only [ordinaryDecision, if_pos hi]
    change provenance old up i
      (offer ⟨old up i, .retained⟩ (buchstabValue old up i) .buchstab)
    by_cases hv : old up i < buchstabValue old up i
    · simp only [offer, if_pos hv]
      exact ⟨hi, rfl⟩
    · simp only [offer, if_neg hv]
      exact ⟨trivial, rfl⟩
  · simp only [ordinaryDecision, if_neg hi]
    exact ⟨trivial, rfl⟩

private theorem offerRow_provenance (old : Table) (i : Fin 200)
    (d : Decision) (k : Fin 106) (hd : provenance old true i d) :
    provenance old true i (offerRow old i d k) := by
  by_cases ht : i.val ∈ (rows k).targets
  · by_cases hv : d.numerator < candidate old (rows k)
    · simp only [offerRow, if_pos ht, offer, if_pos hv]
      exact ⟨⟨rfl, ht⟩, rfl⟩
    · simpa only [offerRow, if_pos ht, offer, if_neg hv] using hd
  · simpa only [offerRow, if_neg ht] using hd

private theorem scan_provenance (old : Table) (i : Fin 200)
    (ks : List (Fin 106)) (d : Decision) (hd : provenance old true i d) :
    provenance old true i (scan old i ks d) := by
  induction ks generalizing d with
  | nil => exact hd
  | cons k ks ih => exact ih _ (offerRow_provenance old i d k hd)

/-- One statement for retained, both Buchstab directions and every bank
row. Every candidate reads the SAME old array. -/
theorem roundDecision_provenance (old : Table) (up : Bool) (i : Fin 200) :
    provenance old up i (roundDecision old up i) := by
  cases up with
  | false => exact ordinary_provenance old false i
  | true => exact scan_provenance old i _ _ (ordinary_provenance old true i)

theorem roundDecision_allowed (old : Table) (up : Bool) (i : Fin 200) :
    choiceAllowed up i (roundDecision old up i).choice :=
  (roundDecision_provenance old up i).1

theorem roundDecision_value (old : Table) (up : Bool) (i : Fin 200) :
    (roundDecision old up i).numerator =
      choiceValue old up i (roundDecision old up i).choice :=
  (roundDecision_provenance old up i).2

private theorem le_offerRow (old : Table) (i : Fin 200) (d : Decision) (k : Fin 106) :
    d.numerator ≤ (offerRow old i d k).numerator := by
  by_cases ht : i.val ∈ (rows k).targets
  · simp only [offerRow, if_pos ht, offer_numerator]
    exact le_max_left _ _
  · simp only [offerRow, if_neg ht, le_refl]

private theorem le_scan (old : Table) (i : Fin 200) (ks : List (Fin 106))
    (d : Decision) : d.numerator ≤ (scan old i ks d).numerator := by
  induction ks generalizing d with
  | nil => exact le_rfl
  | cons k ks ih => exact (le_offerRow old i d k).trans (ih _)

private theorem candidate_le_scan (old : Table) (i : Fin 200)
    (ks : List (Fin 106)) (d : Decision) {k : Fin 106}
    (hk : k ∈ ks) (ht : i.val ∈ (rows k).targets) :
    candidate old (rows k) ≤ (scan old i ks d).numerator := by
  induction ks generalizing d with
  | nil => simp at hk
  | cons j js ih =>
      rcases List.mem_cons.mp hk with rfl | hk
      · have hfirst : candidate old (rows j) ≤ (offerRow old i d j).numerator := by
          simp only [offerRow, if_pos ht, offer_numerator]
          exact le_max_right _ _
        exact hfirst.trans (le_scan old i js _)
      · exact ih _ hk

private theorem old_le_ordinary (old : Table) (up : Bool) (i : Fin 200) :
    old up i ≤ (ordinaryDecision old up i).numerator := by
  rw [ordinaryDecision_numerator]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem old_le_roundDecision (old : Table) (up : Bool) (i : Fin 200) :
    old up i ≤ (roundDecision old up i).numerator := by
  cases up with
  | false => exact old_le_ordinary old false i
  | true => exact (old_le_ordinary old true i).trans (le_scan old i _ _)

theorem buchstab_le_roundDecision (old : Table) (up : Bool) (i : Fin 200)
    (hi : 50 ≤ i.val) : buchstabValue old up i ≤ (roundDecision old up i).numerator := by
  have ho : buchstabValue old up i ≤ (ordinaryDecision old up i).numerator := by
    rw [ordinaryDecision_numerator, if_pos hi]
    exact le_max_right _ _
  cases up with
  | false => exact ho
  | true => exact ho.trans (le_scan old i _ _)

theorem bank_le_roundDecision (old : Table) (i : Fin 200) (k : Fin 106)
    (ht : i.val ∈ (rows k).targets) :
    candidate old (rows k) ≤ (roundDecision old true i).numerator := by
  exact candidate_le_scan old i (List.finRange 106) _ (by simp) ht

/-- Every offered alternative is dominated, but alternatives are NOT
summed. This is the literal maximum, including disabled branches. -/
theorem allowed_value_le_roundDecision (old : Table) (up : Bool) (i : Fin 200)
    (c : Choice) (hc : choiceAllowed up i c) :
    choiceValue old up i c ≤ (roundDecision old up i).numerator := by
  cases c with
  | retained => exact old_le_roundDecision old up i
  | buchstab => exact buchstab_le_roundDecision old up i hc
  | bank k =>
      rcases hc with ⟨rfl, ht⟩
      exact bank_le_roundDecision old i k ht

/-- A bound on all enabled alternatives bounds the actual selected
value. No new numerical or analytic bound is asserted here. -/
theorem roundDecision_le_of_bounds (old : Table) (up : Bool) (i : Fin 200) (B : ℤ)
    (hB : ∀ c, choiceAllowed up i c → choiceValue old up i c ≤ B) :
    (roundDecision old up i).numerator ≤ B := by
  rw [roundDecision_value]
  exact hB _ (roundDecision_allowed old up i)

theorem iterate_le_succ (g : ℕ) (up : Bool) (i : Fin 200) :
    iterate g up i ≤ iterate (g+1) up i :=
  old_le_roundDecision (iterate g) up i

/-- Positivity is derived from the literal seed and retention. It is
not a claim that every offered base or every offered candidate is positive. -/
theorem iterate_nonneg (g : ℕ) (up : Bool) (i : Fin 200) : 0 ≤ iterate g up i := by
  induction g with
  | zero =>
      change 0 ≤ seed up i
      unfold seed q
      split_ifs <;> positivity
  | succ g ih => exact ih.trans (iterate_le_succ g up i)

theorem selected_buchstab_source {g : ℕ} {up : Bool} {i : Fin 200}
    (hc : (roundDecision (iterate g) up i).choice = .buchstab) :
    50 ≤ i.val ∧ iterate (g+1) up i = buchstabValue (iterate g) up i := by
  have ha := roundDecision_allowed (iterate g) up i
  have hv := roundDecision_value (iterate g) up i
  rw [hc] at ha hv
  exact ⟨ha, hv⟩

end
end ImbalancedChen.Part5OriginalH430DecisionProvenance
