import ImbalancedChen.P5OriginalOrdinaryConditionalPrefix

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact LOWER native e*d state, complementing the existing upper dictionary.
The old actual upper dictionary and its separated rough/small prefix
identities are reused unchanged. Lower even-prefix tests leave LOWER small
parity when the rough cardinality is even and flip to UPPER small parity
when it is odd. The small level is the ACTUAL L/d.

The last theorem is an identity for the literal original arithmetic
coefficient, including the strict complete-product level test, actual
rough product/cardinality, every small prefix, and the original sign.
It does not replace this coefficient by an independent beta(e)*lambda(d),
change the physical sigma, or assert a density/AP/enhanced-count licence.
-/

namespace ImbalancedChen.P2EnhancedNativeLowerConditionalPrefix

noncomputable section

open scoped BigOperators Classical
open P5Z.OriginalOrdinaryBetaRegroup
open P5Z.OriginalOrdinaryConditionalPrefix
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- Exact lower set-prefix state before any independence or averaging claim. -/
theorem lowerAdmissible_union_iff {A B : Finset ℕ} {w L : ℝ}
    (hA : ∀ q ∈ A, w ≤ (q : ℝ)) (hB : ∀ q ∈ B, (q : ℝ) < w) :
    LowerAdmissibleSet L (A ∪ B) ↔
      LowerAdmissibleSet L A ∧
      ∀ p ∈ B, Even (A.card + (B.filter (fun q => p ≤ q)).card) →
        ((A.prod id : ℕ) : ℝ) * (((B.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) *
          (p : ℝ) ^ 2 < L := by
  have hdis := separated_disjoint hA hB
  have hdisP (p : ℕ) : Disjoint A (B.filter (fun q => p ≤ q)) :=
    hdis.mono_right (Finset.filter_subset _ _)
  constructor
  · intro h
    constructor
    · intro p hp heven
      have hh := h p (Finset.mem_union_left _ hp)
      rw [rough_prefix_filter hA hB hp] at hh
      exact hh heven
    · intro p hp heven
      have hh := h p (Finset.mem_union_right _ hp)
      rw [small_prefix_filter hA hB hp, Finset.card_union_of_disjoint (hdisP p),
        Finset.prod_union (hdisP p), Nat.cast_mul] at hh
      exact hh heven
  · rintro ⟨hrough, hsmall⟩ p hp heven
    rcases Finset.mem_union.mp hp with hp | hp
    · rw [rough_prefix_filter hA hB hp] at heven ⊢
      exact hrough p hp heven
    · rw [small_prefix_filter hA hB hp, Finset.card_union_of_disjoint (hdisP p)] at heven
      rw [small_prefix_filter hA hB hp, Finset.prod_union (hdisP p), Nat.cast_mul]
      exact hsmall p hp heven

theorem lower_even_state_small_gates {A B : Finset ℕ} {L : ℝ}
    (hprod : 0 < ((A.prod id : ℕ) : ℝ)) (hEven : Even A.card) :
    (∀ p ∈ B, Even (A.card + (B.filter (fun q => p ≤ q)).card) →
      ((A.prod id : ℕ) : ℝ) * (((B.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) *
        (p : ℝ) ^ 2 < L) ↔ LowerAdmissibleSet (L / ((A.prod id : ℕ) : ℝ)) B := by
  have hpar (k : ℕ) : Even (A.card + k) ↔ Even k := by
    simp only [Nat.even_iff] at hEven ⊢
    omega
  unfold LowerAdmissibleSet
  constructor
  · intro h p hp heven
    have hh := h p hp ((hpar _).mpr heven)
    apply (lt_div_iff₀ hprod).mpr
    nlinarith only [hh]
  · intro h p hp heven
    have hh := (lt_div_iff₀ hprod).mp (h p hp ((hpar _).mp heven))
    nlinarith only [hh]

theorem lower_odd_state_small_gates {A B : Finset ℕ} {L : ℝ}
    (hprod : 0 < ((A.prod id : ℕ) : ℝ)) (hOdd : ¬ Even A.card) :
    (∀ p ∈ B, Even (A.card + (B.filter (fun q => p ≤ q)).card) →
      ((A.prod id : ℕ) : ℝ) * (((B.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) *
        (p : ℝ) ^ 2 < L) ↔ UpperAdmissibleSet (L / ((A.prod id : ℕ) : ℝ)) B := by
  have hpar (k : ℕ) : Even (A.card + k) ↔ ¬ Even k := by
    simp only [Nat.even_iff] at hOdd ⊢
    omega
  unfold UpperAdmissibleSet
  constructor
  · intro h p hp hodd
    have hh := h p hp ((hpar _).mpr hodd)
    apply (lt_div_iff₀ hprod).mpr
    nlinarith only [hh]
  · intro h p hp heven
    have hh := (lt_div_iff₀ hprod).mp (h p hp ((hpar _).mp heven))
    nlinarith only [hh]

/-- The actual natural rough product d remains the small-prefix state. -/
theorem actual_lower_gates {N cap e d : ℕ} {w Z L : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hd : d ∈ roughSupport N cap w Z) :
    LowerAdmissibleSet L (e * d).primeFactors ↔
      LowerAdmissibleSet L d.primeFactors ∧
      ∀ p ∈ e.primeFactors,
        Even (d.primeFactors.card + (e.primeFactors.filter (fun q => p ≤ q)).card) →
        (d : ℝ) * (((e.primeFactors.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) *
          (p : ℝ) ^ 2 < L := by
  have heS := actualSmallRosserSupport_smallPrimeSupportedAt N cap w he
  have hdR := roughSupport_rough hd
  have hdSF := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (roughProduct_squarefree N cap w Z)
  rw [Nat.primeFactors_mul heS.1 hdR.1, Finset.union_comm]
  have hh := lowerAdmissible_union_iff hdR.2 heS.2 (L := L)
  rwa [Nat.prod_primeFactors_of_squarefree hdSF] at hh

theorem actual_lower_gates_even {N cap e d : ℕ} {w Z L : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hd : d ∈ roughSupport N cap w Z)
    (hEven : Even d.primeFactors.card) :
    LowerAdmissibleSet L (e * d).primeFactors ↔
      LowerAdmissibleSet L d.primeFactors ∧ LowerAdmissibleSet (L / (d : ℝ)) e.primeFactors := by
  have hdSF := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (roughProduct_squarefree N cap w Z)
  have hpos : 0 < ((d.primeFactors.prod id : ℕ) : ℝ) := by
    rw [Nat.prod_primeFactors_of_squarefree hdSF]
    exact_mod_cast Nat.pos_of_ne_zero hdSF.ne_zero
  have hc := lower_even_state_small_gates (B := e.primeFactors) (L := L) hpos hEven
  rw [Nat.prod_primeFactors_of_squarefree hdSF] at hc
  rw [actual_lower_gates he hd, hc]

theorem actual_lower_gates_odd {N cap e d : ℕ} {w Z L : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hd : d ∈ roughSupport N cap w Z)
    (hOdd : ¬ Even d.primeFactors.card) :
    LowerAdmissibleSet L (e * d).primeFactors ↔
      LowerAdmissibleSet L d.primeFactors ∧ UpperAdmissibleSet (L / (d : ℝ)) e.primeFactors := by
  have hdSF := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (roughProduct_squarefree N cap w Z)
  have hpos : 0 < ((d.primeFactors.prod id : ℕ) : ℝ) := by
    rw [Nat.prod_primeFactors_of_squarefree hdSF]
    exact_mod_cast Nat.pos_of_ne_zero hdSF.ne_zero
  have hc := lower_odd_state_small_gates (B := e.primeFactors) (L := L) hpos hOdd
  rw [Nat.prod_primeFactors_of_squarefree hdSF] at hc
  rw [actual_lower_gates he hd, hc]

/-- Literal actual lower coefficient, with its complete strict level test,
rough parity, residual L/d state, and all small e-prefix tests retained. -/
theorem actual_native_lower_conditional_value {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w ≤ Z) (he : e ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ roughSupport N cap w Z) :
    actualSmallRosserMinus N cap Z L (e * d) =
      if ((e * d : ℕ) : ℝ) < L ∧ LowerAdmissibleSet L d.primeFactors ∧
        (∀ p ∈ e.primeFactors,
          Even (d.primeFactors.card + (e.primeFactors.filter (fun q => p ≤ q)).card) →
          (d : ℝ) * (((e.primeFactors.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) *
            (p : ℝ) ^ 2 < L)
      then (-1 : ℝ) ^ (d.primeFactors.card + e.primeFactors.card) else 0 := by
  have heS := actualSmallRosserSupport_smallPrimeSupportedAt N cap w he
  have hdR := roughSupport_rough hd
  have hdis : Disjoint d.primeFactors e.primeFactors := separated_disjoint hdR.2 heS.2
  have hcard : (e * d).primeFactors.card = d.primeFactors.card + e.primeFactors.card := by
    rw [Nat.primeFactors_mul heS.1 hdR.1, Finset.card_union_of_disjoint hdis.symm]
    omega
  have hmem : e * d ∈ actualSmallRosserSupport N cap Z := by
    rw [nativeSupport_eq_products N cap hwZ]
    exact Finset.mem_image.mpr ⟨(e, d), Finset.mem_product.mpr ⟨he, hd⟩, rfl⟩
  have hmem' : e * d ∈ (actualSmallPrimeProduct N cap Z).divisors := hmem
  change lowerWeight (actualSmallPrimeProduct N cap Z) L (e * d) = _
  rw [lowerWeight_apply]
  simp only [hmem', true_and, actual_lower_gates he hd, hcard, and_assoc]

end
end ImbalancedChen.P2EnhancedNativeLowerConditionalPrefix
