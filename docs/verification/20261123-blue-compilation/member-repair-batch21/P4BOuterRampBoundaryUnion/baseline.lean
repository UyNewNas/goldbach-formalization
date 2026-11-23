import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.P4BLogGateOuterRamp

/-!
# P4B finite arithmetic boundary union bound for outer ramps

SOURCE-ONLY / YELLOW / UNCOMPILED, 2026-10-24.

This file is independent of a particular scalar ramp construction. Finite
ramps in [0,1], equal to one at positive gates and zero at gates at most
-width, majorize the strict intersection. Their surplus is paid by the
sum of the literal arithmetic strip counts -width < G_i <= 0. Empty gate
families and zero gate values are included. No continuity, volume, null
wall, asymptotic boundary estimate or analytic supplier is asserted.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped Classical BigOperators
open Filter Topology

/-- Elementary bounds for a finite product of scalar ramps. -/
theorem finite_gate_ramp_product_bounds {ι : Type*}
    (I : Finset ι) (ramp : ι → ℝ)
    (hbound : ∀ i ∈ I, 0 ≤ ramp i ∧ ramp i ≤ 1) :
    0 ≤ (∏ i ∈ I, ramp i) ∧ (∏ i ∈ I, ramp i) ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i hi => (hbound i hi).1),
    Finset.prod_le_one (fun i hi => (hbound i hi).1)
      (fun i hi => (hbound i hi).2)⟩

/-- On the strict gate intersection every ramp is exactly one. -/
theorem finite_gate_ramp_product_eq_one {ι : Type*}
    (I : Finset ι) (G ramp : ι → ℝ)
    (hone : ∀ i ∈ I, 0 < G i → ramp i = 1)
    (hstrict : ∀ i ∈ I, 0 < G i) :
    (∏ i ∈ I, ramp i) = 1 := by
  exact Finset.prod_eq_one (fun i hi => hone i hi (hstrict i hi))

/-- A positive product outside the strict intersection has an actual
bad gate in the one-sided boundary strip, including the wall G_i = 0. -/
theorem exists_gate_strip_of_product_pos {ι : Type*}
    (I : Finset ι) (G ramp : ι → ℝ) (width : ℝ)
    (hzero : ∀ i ∈ I, G i ≤ -width → ramp i = 0)
    (hnot : ¬ ∀ i ∈ I, 0 < G i)
    (hprod : 0 < ∏ i ∈ I, ramp i) :
    ∃ i ∈ I, -width < G i ∧ G i ≤ 0 := by
  classical
  obtain ⟨i, hi, hbad⟩ : ∃ i ∈ I, G i ≤ 0 := by
    simpa only [not_forall, not_imp, not_lt] using hnot
  refine ⟨i, hi, ?_, hbad⟩
  apply lt_of_not_ge
  intro hfar
  have hprodZero : (∏ j ∈ I, ramp j) = 0 :=
    Finset.prod_eq_zero hi (hzero i hi hfar)
  rw [hprodZero] at hprod
  exact (lt_irrefl 0) hprod

/-- The product majorizes the strict-intersection indicator, with no
positivity assumption on width beyond the stated scalar ramp laws. -/
theorem strict_gate_indicator_le_ramp_product {ι : Type*}
    (I : Finset ι) (G ramp : ι → ℝ)
    (hbound : ∀ i ∈ I, 0 ≤ ramp i ∧ ramp i ≤ 1)
    (hone : ∀ i ∈ I, 0 < G i → ramp i = 1) :
    (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0) ≤ ∏ i ∈ I, ramp i := by
  classical
  by_cases hstrict : ∀ i ∈ I, 0 < G i
  · simpa only [if_pos hstrict,
      finite_gate_ramp_product_eq_one I G ramp hone hstrict] using (le_refl (1 : ℝ))
  · rw [if_neg hstrict]
    exact (finite_gate_ramp_product_bounds I ramp hbound).1

/-- Exact finite union payment: the outer product's excess over the
strict indicator costs at most the sum of the arithmetic strip indicators.
The lower strip endpoint is strict; the wall endpoint is included. -/
theorem ramp_product_sub_strict_indicator_le_strip_union {ι : Type*}
    (I : Finset ι) (G ramp : ι → ℝ) (width : ℝ)
    (hbound : ∀ i ∈ I, 0 ≤ ramp i ∧ ramp i ≤ 1)
    (hone : ∀ i ∈ I, 0 < G i → ramp i = 1)
    (hzero : ∀ i ∈ I, G i ≤ -width → ramp i = 0) :
    (∏ i ∈ I, ramp i) - (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0) ≤
      ∑ i ∈ I, if -width < G i ∧ G i ≤ 0 then (1 : ℝ) else 0 := by
  classical
  have hsumNonneg : 0 ≤
      ∑ i ∈ I, if -width < G i ∧ G i ≤ 0 then (1 : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro i _hi
    split_ifs <;> norm_num
  by_cases hstrict : ∀ i ∈ I, 0 < G i
  · rw [if_pos hstrict, finite_gate_ramp_product_eq_one I G ramp hone hstrict,
      sub_self]
    exact hsumNonneg
  · rw [if_neg hstrict, sub_zero]
    by_cases hprod : 0 < ∏ i ∈ I, ramp i
    · obtain ⟨i, hi, hstrip⟩ :=
        exists_gate_strip_of_product_pos I G ramp width hzero hstrict hprod
      calc
        (∏ j ∈ I, ramp j) ≤ 1 :=
          (finite_gate_ramp_product_bounds I ramp hbound).2
        _ = (if -width < G i ∧ G i ≤ 0 then (1 : ℝ) else 0) :=
          (if_pos hstrip).symm
        _ ≤ _ := Finset.single_le_sum
          (fun j _hj => by split_ifs <;> norm_num) hi
    · exact (le_of_not_gt hprod).trans hsumNonneg

/-- Summation over a literal natural-number carrier. Each strip price is
an actual finite cardinal, so arithmetic boundary atoms are retained. -/
theorem finiteSourceMass_ramp_product_le_strict_card_add_strip_cards {ι : Type*}
    (I : Finset ι) (S : Finset ℕ) (G ramp : ι → ℕ → ℝ) (width : ℝ)
    (hbound : ∀ m ∈ S, ∀ i ∈ I, 0 ≤ ramp i m ∧ ramp i m ≤ 1)
    (hone : ∀ m ∈ S, ∀ i ∈ I, 0 < G i m → ramp i m = 1)
    (hzero : ∀ m ∈ S, ∀ i ∈ I, G i m ≤ -width → ramp i m = 0) :
    finiteSourceMass S (fun m => ∏ i ∈ I, ramp i m) ≤
      (((S.filter (fun m => ∀ i ∈ I, 0 < G i m)).card : ℕ) : ℝ) +
        ∑ i ∈ I, (((S.filter
          (fun m => -width < G i m ∧ G i m ≤ 0)).card : ℕ) : ℝ) := by
  classical
  have hstrictMass :
      (∑ m ∈ S, if ∀ i ∈ I, 0 < G i m then (1 : ℝ) else 0) =
        (((S.filter (fun m => ∀ i ∈ I, 0 < G i m)).card : ℕ) : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  have hstripMass :
      (∑ m ∈ S, ∑ i ∈ I,
        if -width < G i m ∧ G i m ≤ 0 then (1 : ℝ) else 0) =
      ∑ i ∈ I, (((S.filter
        (fun m => -width < G i m ∧ G i m ≤ 0)).card : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_filter]
    simp
  calc
    finiteSourceMass S (fun m => ∏ i ∈ I, ramp i m) =
        ∑ m ∈ S, ((if ∀ i ∈ I, 0 < G i m then (1 : ℝ) else 0) +
          ((∏ i ∈ I, ramp i m) -
            (if ∀ i ∈ I, 0 < G i m then (1 : ℝ) else 0))) := by
      unfold finiteSourceMass
      apply Finset.sum_congr rfl
      intro m _hm
      ring
    _ ≤ ∑ m ∈ S, ((if ∀ i ∈ I, 0 < G i m then (1 : ℝ) else 0) +
        ∑ i ∈ I, if -width < G i m ∧ G i m ≤ 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro m hm
      exact add_le_add_left
        (ramp_product_sub_strict_indicator_le_strip_union I
          (fun i => G i m) (fun i => ramp i m) width
          (hbound m hm) (hone m hm) (hzero m hm)) _
    _ = _ := by rw [Finset.sum_add_distrib, hstrictMass, hstripMass]

/-- Once the strict gate filter is identified with the actual source,
its complete ramp surplus is paid by the actual arithmetic strip budget. -/
theorem finiteSourceMass_ramp_product_surplus_paid {ι : Type*}
    (I : Finset ι) (S A : Finset ℕ) (G ramp : ι → ℕ → ℝ) (width E : ℝ)
    (hbound : ∀ m ∈ S, ∀ i ∈ I, 0 ≤ ramp i m ∧ ramp i m ≤ 1)
    (hone : ∀ m ∈ S, ∀ i ∈ I, 0 < G i m → ramp i m = 1)
    (hzero : ∀ m ∈ S, ∀ i ∈ I, G i m ≤ -width → ramp i m = 0)
    (hsource : S.filter (fun m => ∀ i ∈ I, 0 < G i m) = A)
    (hpaid : (∑ i ∈ I, (((S.filter
      (fun m => -width < G i m ∧ G i m ≤ 0)).card : ℕ) : ℝ)) ≤ E) :
    finiteSourceMass S (fun m => ∏ i ∈ I, ramp i m) ≤ (A.card : ℝ) + E := by
  have h := finiteSourceMass_ramp_product_le_strict_card_add_strip_cards
    I S G ramp width hbound hone hzero
  rw [hsource] at h
  exact h.trans (add_le_add_left hpaid (A.card : ℝ))

/-- Direct adapter to the original hsurplus interface. The width and
finite gates can depend on delta and N. Their arithmetic strip-cardinality
payment is an explicit external estimate, never a null-volume argument. -/
theorem eventually_realSource_ramp_surplus_paid {ι : Type*}
    (b kappa : ℝ) (I : ℝ → ℕ → Finset ι) (S : ℝ → ℕ → Finset ℕ)
    (G ramp : ℝ → ℕ → ι → ℕ → ℝ) (width : ℝ → ℕ → ℝ)
    (hramp : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ S delta N, ∀ i ∈ I delta N,
        (0 ≤ ramp delta N i m ∧ ramp delta N i m ≤ 1) ∧
        (0 < G delta N i m → ramp delta N i m = 1) ∧
        (G delta N i m ≤ -width delta N → ramp delta N i m = 0))
    (hsource : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (S delta N).filter (fun m => ∀ i ∈ I delta N, 0 < G delta N i m) =
        realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
    (hpaid : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (∑ i ∈ I delta N, ((((S delta N).filter
        (fun m => -width delta N < G delta N i m ∧ G delta N i m ≤ 0)).card : ℕ) : ℝ)) ≤
        delta * ((N : ℝ) / Real.log (N : ℝ))) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      finiteSourceMass (S delta N)
        (fun m => ∏ i ∈ I delta N, ramp delta N i m) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)) := by
  intro delta hdelta
  filter_upwards [hramp delta hdelta, hsource delta hdelta, hpaid delta hdelta]
    with N hrampN hsourceN hpaidN
  intro hEven
  exact finiteSourceMass_ramp_product_surplus_paid (I delta N) (S delta N)
    (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
    (G delta N) (ramp delta N) (width delta N)
    (delta * ((N : ℝ) / Real.log (N : ℝ)))
    (fun m hm i hi => (hrampN hEven m hm i hi).1)
    (fun m hm i hi => (hrampN hEven m hm i hi).2.1)
    (fun m hm i hi => (hrampN hEven m hm i hi).2.2)
    (hsourceN hEven) (hpaidN hEven)

/-- Adapter to the public scalar ramp: its proved scalar bounds and
endpoint laws discharge every pointwise premise of the union bound. -/
theorem logGateOuterRamp_product_surplus_le_strip_union {ι : Type*}
    (I : Finset ι) (G : ι → ℝ) {width : ℝ} (hwidth : 0 < width) :
    (∏ i ∈ I, logGateOuterRamp width (G i)) -
      (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0) ≤
        ∑ i ∈ I, if -width < G i ∧ G i ≤ 0 then (1 : ℝ) else 0 := by
  exact ramp_product_sub_strict_indicator_le_strip_union I G
    (fun i => logGateOuterRamp width (G i)) width
    (fun i _hi => logGateOuterRamp_bounds width (G i))
    (fun i _hi hpos => logGateOuterRamp_eq_one hwidth hpos.le)
    (fun i _hi hfar => logGateOuterRamp_eq_zero hwidth hfar)

/-- For the actual public ramp the only remaining surplus payment is a
bound for the literal arithmetic boundary-strip cardinalities. -/
theorem finiteSourceMass_logGateOuterRamp_surplus_paid {ι : Type*}
    (I : Finset ι) (S A : Finset ℕ) (G : ι → ℕ → ℝ)
    {width : ℝ} (hwidth : 0 < width) (E : ℝ)
    (hsource : S.filter (fun m => ∀ i ∈ I, 0 < G i m) = A)
    (hpaid : (∑ i ∈ I, (((S.filter
      (fun m => -width < G i m ∧ G i m ≤ 0)).card : ℕ) : ℝ)) ≤ E) :
    finiteSourceMass S (fun m => ∏ i ∈ I, logGateOuterRamp width (G i m)) ≤
      (A.card : ℝ) + E := by
  exact finiteSourceMass_ramp_product_surplus_paid I S A G
    (fun i m => logGateOuterRamp width (G i m)) width E
    (fun m _hm i _hi => logGateOuterRamp_bounds width (G i m))
    (fun m _hm i _hi hpos => logGateOuterRamp_eq_one hwidth hpos.le)
    (fun m _hm i _hi hfar => logGateOuterRamp_eq_zero hwidth hfar)
    hsource hpaid

end

end ImbalancedChen.P4B
