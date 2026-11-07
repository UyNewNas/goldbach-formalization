import ImbalancedChen.P5U7ActualMovingComponentMargins

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Exact ORIGINAL branch-collar truncation dictionary. The additive-complement
prime gate and any physical product mask commute with the literal marked
interior/collar split. Progression and large-original-prime endpoint masks
are covered without altering a strict or inclusive endpoint. The original
unit branch is retained explicitly. No distribution estimate is asserted.
-/
namespace ImbalancedChen
noncomputable section
open scoped BigOperators
open Classical

def p5U7OriginalPrimeInterior (N : ℕ) (eta : ℝ) : Finset P5U7ThreeLabel :=
  (currentChenUpsilon7PrimeTriples N).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta)

def p5U7OriginalSemiprimeInterior (N : ℕ) (eta : ℝ) : Finset P5U7FourLabel :=
  (currentChenUpsilon7SemiprimeQuadruples N).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta)

def p5U7OriginalPrimeCollar (N : ℕ) (eta : ℝ) : Finset P5U7ThreeLabel :=
  (currentChenUpsilon7PrimeTriples N).filter (fun x => x.1 ∉ p5U7InteriorSelector N eta)

def p5U7OriginalSemiprimeCollar (N : ℕ) (eta : ℝ) : Finset P5U7FourLabel :=
  (currentChenUpsilon7SemiprimeQuadruples N).filter (fun x => x.1 ∉ p5U7InteriorSelector N eta)

/-- The truncated ORIGINAL prime branch uses the same marked actual
arithmetic interior and its genuine additive-complement prime test. -/
theorem p5U7OriginalPrimeInterior_eq_gated_arithmetic (N : ℕ) (eta : ℝ) :
    p5U7OriginalPrimeInterior N eta = (p5U7ActualInteriorThree N eta).filter
      (fun x => Nat.Prime (N-p5U7ThreeProduct x)) := by
  rw [p5U7OriginalPrimeInterior,p5U7_originalPrimeTriples_eq_gated_arithmetic,
    p5U7ActualInteriorThree_eq_original_filter]
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx,hp⟩,hi⟩
    exact ⟨⟨hx,hi⟩,hp⟩
  · rintro ⟨⟨hx,hi⟩,hp⟩
    exact ⟨⟨hx,hp⟩,hi⟩

theorem p5U7OriginalSemiprimeInterior_eq_gated_arithmetic (N : ℕ) (eta : ℝ) :
    p5U7OriginalSemiprimeInterior N eta = (p5U7ActualInteriorFour N eta).filter
      (fun x => Nat.Prime (N-p5U7FourProduct x)) := by
  rw [p5U7OriginalSemiprimeInterior,p5U7_originalSemiprimeQuadruples_eq_gated_arithmetic,
    p5U7ActualInteriorFour_eq_original_filter]
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx,hp⟩,hi⟩
    exact ⟨⟨hx,hi⟩,hp⟩
  · rintro ⟨⟨hx,hi⟩,hp⟩
    exact ⟨⟨hx,hp⟩,hi⟩

private theorem p5U7Component_indicator_count {α : Type*} [DecidableEq α]
    (S : Finset α) (P : α → Prop) :
    (∑ x ∈ S,if P x then (1 : ℝ) else 0) = ((S.filter P).card : ℝ) := by
  rw [← Finset.sum_filter]
  simp

/-- Exact physical weight dictionary for the original truncated prime
branch, including every further mask on its physical product. -/
theorem p5U7OriginalPrimeInterior_masked_weight (N : ℕ) (eta : ℝ) (G : ℕ → Prop) :
    (∑ m ∈ Finset.range N,if Nat.Prime (N-m) ∧ G m then
      p5U7ActualInteriorPrimeProductWeight N eta m else 0) =
      (((p5U7OriginalPrimeInterior N eta).filter (fun x => G (p5U7ThreeProduct x))).card : ℝ) := by
  have h := p5U7ActualInteriorPrimeProductWeight_Fubini N eta
    (fun m => if Nat.Prime (N-m) ∧ G m then (1 : ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at h
  rw [h,p5U7Component_indicator_count,p5U7OriginalPrimeInterior_eq_gated_arithmetic,
    Finset.filter_filter]

theorem p5U7OriginalSemiprimeInterior_masked_weight (N : ℕ) (eta : ℝ) (G : ℕ → Prop) :
    (∑ m ∈ Finset.range N,if Nat.Prime (N-m) ∧ G m then
      p5U7ActualInteriorSemiprimeProductWeight N eta m else 0) =
      (((p5U7OriginalSemiprimeInterior N eta).filter (fun x => G (p5U7FourProduct x))).card : ℝ) := by
  have h := p5U7ActualInteriorSemiprimeProductWeight_Fubini N eta
    (fun m => if Nat.Prime (N-m) ∧ G m then (1 : ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero] at h
  rw [h,p5U7Component_indicator_count,p5U7OriginalSemiprimeInterior_eq_gated_arithmetic,
    Finset.filter_filter]

/-- The exact masked original branch is interior PLUS its original
gated collar. No arithmetic boundary label has been discarded. -/
theorem p5U7OriginalPrime_masked_split (N : ℕ) (eta : ℝ) (G : ℕ → Prop) :
    (((currentChenUpsilon7PrimeTriples N).filter (fun x => G (p5U7ThreeProduct x))).card : ℝ) =
      (((p5U7OriginalPrimeInterior N eta).filter (fun x => G (p5U7ThreeProduct x))).card : ℝ) +
      (((p5U7OriginalPrimeCollar N eta).filter (fun x => G (p5U7ThreeProduct x))).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (currentChenUpsilon7PrimeTriples N).filter (fun x => G (p5U7ThreeProduct x)))
    (p := fun x => x.1 ∈ p5U7InteriorSelector N eta)
  have hl : (((currentChenUpsilon7PrimeTriples N).filter (fun x => G (p5U7ThreeProduct x))).filter
      (fun x => x.1 ∈ p5U7InteriorSelector N eta)) =
      (p5U7OriginalPrimeInterior N eta).filter (fun x => G (p5U7ThreeProduct x)) := by
    ext x
    simp only [p5U7OriginalPrimeInterior,Finset.mem_filter]
    simp only [and_assoc,and_left_comm,and_comm]
  have hr : (((currentChenUpsilon7PrimeTriples N).filter (fun x => G (p5U7ThreeProduct x))).filter
      (fun x => x.1 ∉ p5U7InteriorSelector N eta)) =
      (p5U7OriginalPrimeCollar N eta).filter (fun x => G (p5U7ThreeProduct x)) := by
    ext x
    simp only [p5U7OriginalPrimeCollar,Finset.mem_filter]
    simp only [and_assoc,and_left_comm,and_comm]
  rw [hl,hr] at h
  exact_mod_cast h.symm

theorem p5U7OriginalSemiprime_masked_split (N : ℕ) (eta : ℝ) (G : ℕ → Prop) :
    (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x => G (p5U7FourProduct x))).card : ℝ) =
      (((p5U7OriginalSemiprimeInterior N eta).filter (fun x => G (p5U7FourProduct x))).card : ℝ) +
      (((p5U7OriginalSemiprimeCollar N eta).filter (fun x => G (p5U7FourProduct x))).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (currentChenUpsilon7SemiprimeQuadruples N).filter (fun x => G (p5U7FourProduct x)))
    (p := fun x => x.1 ∈ p5U7InteriorSelector N eta)
  have hl : (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x => G (p5U7FourProduct x))).filter
      (fun x => x.1 ∈ p5U7InteriorSelector N eta)) =
      (p5U7OriginalSemiprimeInterior N eta).filter (fun x => G (p5U7FourProduct x)) := by
    ext x
    simp only [p5U7OriginalSemiprimeInterior,Finset.mem_filter]
    simp only [and_assoc,and_left_comm,and_comm]
  have hr : (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x => G (p5U7FourProduct x))).filter
      (fun x => x.1 ∉ p5U7InteriorSelector N eta)) =
      (p5U7OriginalSemiprimeCollar N eta).filter (fun x => G (p5U7FourProduct x)) := by
    ext x
    simp only [p5U7OriginalSemiprimeCollar,Finset.mem_filter]
    simp only [and_assoc,and_left_comm,and_comm]
  rw [hl,hr] at h
  exact_mod_cast h.symm

/-- Every gated original prime collar is a literal subfamily of the
paid arithmetic prime collar. The mask may include a progression. -/
theorem p5U7OriginalPrimeCollar_masked_le (N : ℕ) (eta : ℝ) (G : ℕ → Prop) :
    (((p5U7OriginalPrimeCollar N eta).filter (fun x => G (p5U7ThreeProduct x))).card : ℝ) ≤
      ((p5U7ActualPrimeCollar N eta).card : ℝ) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx,_⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hx
  rw [p5U7_originalPrimeTriples_eq_gated_arithmetic] at hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hn⟩

theorem p5U7OriginalSemiprimeCollar_masked_le (N : ℕ) (eta : ℝ) (G : ℕ → Prop) :
    (((p5U7OriginalSemiprimeCollar N eta).filter (fun x => G (p5U7FourProduct x))).card : ℝ) ≤
      ((p5U7ActualSemiprimeCollar N eta).card : ℝ) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx,_⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hx
  rw [p5U7_originalSemiprimeQuadruples_eq_gated_arithmetic] at hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hn⟩

/-- Exact original U7 retains BOTH gated component collars AND its unit
branch. Only these actual finite objects enter subsequent estimates. -/
theorem p5U7Original_eq_interior_add_collars_add_unit (N : ℕ) (eta : ℝ) :
    currentChenUpsilon7 N =
      ((p5U7OriginalPrimeInterior N eta).card : ℝ) +
      ((p5U7OriginalSemiprimeInterior N eta).card : ℝ) +
      ((p5U7OriginalPrimeCollar N eta).card : ℝ) +
      ((p5U7OriginalSemiprimeCollar N eta).card : ℝ) +
      ((currentChenUpsilon7UnitFibres N).card : ℝ) := by
  have hp := p5U7OriginalPrime_masked_split N eta (fun _ => True)
  have hs := p5U7OriginalSemiprime_masked_split N eta (fun _ => True)
  simp only [Finset.filter_true] at hp hs
  rw [currentChenUpsilon7_eq_primeTriples_add_semiprimeQuadruples_add_unitFibres]
  linarith only [hp,hs]

end
end ImbalancedChen
