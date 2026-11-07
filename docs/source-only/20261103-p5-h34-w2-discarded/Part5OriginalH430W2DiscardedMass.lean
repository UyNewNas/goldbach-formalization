import ImbalancedChen.Part5OriginalH430W2DiscardedCarriers
import ImbalancedChen.Part5OriginalH430BuchstabCeilingPayment
import ImbalancedChen.Part5OriginalH430ImmutableBankProfiles

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Elementary same-Q payment for all W2 endpoint/repeated-prefix deletions.
The exact singular factors are retained. Both coordinates have the original
prime-box floor. A bad pair is bounded by two coordinate fibres; the
remaining reciprocal sum is at most 1+log N. No PNT/BV/PP proof is added.
-/
namespace ImbalancedChen.Part5OriginalH430W2DiscardedMass

noncomputable section
open Set Filter
open scoped Classical BigOperators Topology
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalOldProfilePrimeLimits P2OriginalBankOldProfilePassage
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430PrimeObstructionBudget Part5OriginalH430W2DiscardedCarriers
open Part5OriginalH430BuchstabCeilingPayment (localPrimeFactor_le_two_div)

/-- Fresh and repeated singular multipliers are both bounded, not replaced. -/
theorem single_theta_bounds {N d : ℕ} {Q L : ℝ} {p : W2Parameters} {k : Fin 3}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (hp : W2Geometry p)
    {q : Fin 1 → ℕ} (hq : q ∈ singleCarrier N L p k) :
    0 ≤ thetaAtom N Q (d*q 0) ∧
      thetaAtom N Q (d*q 0) ≤ 4*thetaAtom N Q d / (q 0:ℝ) := by
  obtain ⟨hbox,hx⟩ := Finset.mem_filter.mp hq
  have hq0 := mem_actualPrimeBoxTuples_iff.mp hbox 0
  have hq4 : (4:ℝ) ≤ q 0 := hA.trans hq0.2.2.1
  have hq2 : 2 < q 0 := by exact_mod_cast (show (2:ℝ) < q 0 by linarith)
  have hu : normalizedLog N L q 0 ≤ 1/2 := hx.2.le.trans (W2_singleton_top hp k)
  have hR := sameQ_residual_gt_one (by omega) hd hL hQ
  have ht := thetaAtom_nonneg hN hd hR
  have he : Real.log (q 0:ℝ)/Real.log (Q/d) = normalizedLog N L q 0 := by
    rw [hQ]
    exact physical_log_ratio (by omega) hd hL q 0
  refine ⟨single_arithmetic_child_nonneg hN hd hL hA hQ hbox hu, ?_⟩
  rw [thetaAtom_single (by omega) hd hq0.1 hq2
    (hq0.1.coprime_iff_not_dvd.mpr hq0.2.1) hR, he]
  have hden : 0 < 1-normalizedLog N L q 0 := by linarith
  have hrat : localPrimeFactor d (q 0)/(1-normalizedLog N L q 0) ≤ 4/(q 0:ℝ) := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ 2/(q 0:ℝ) := localPrimeFactor_le_two_div hq4
      _ = (4/(q 0:ℝ))*(1/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hrat ht

theorem pair_theta_bounds {N d : ℕ} {Q L : ℝ} {p : W2Parameters} {k : Fin 4}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (hp : W2Geometry p)
    {q : Fin 2 → ℕ} (hq : q ∈ pairCarrier N L p k) :
    0 ≤ thetaAtom N Q (d*q 0*q 1) ∧
      thetaAtom N Q (d*q 0*q 1) ≤ 20*thetaAtom N Q d *
        ((1/(q 0:ℝ))*(1/(q 1:ℝ))) := by
  obtain ⟨hbox,hx⟩ := Finset.mem_filter.mp hq
  have hqi (i : Fin 2) := mem_actualPrimeBoxTuples_iff.mp hbox i
  have hq4 (i : Fin 2) : (4:ℝ) ≤ q i := hA.trans (hqi i).2.2.1
  have hq2 (i : Fin 2) : 2 < q i := by exact_mod_cast (show (2:ℝ) < q i by linarith [hq4 i])
  have hR := sameQ_residual_gt_one (by omega) hd hL hQ
  have ht := thetaAtom_nonneg hN hd hR
  have he (i : Fin 2) : Real.log (q i:ℝ)/Real.log (Q/d) = normalizedLog N L q i := by
    rw [hQ]
    exact physical_log_ratio (by omega) hd hL q i
  have hr := (pairHalf_geometry hp k hx).2.1
  have hden : 0 < 1-normalizedLog N L q 0-normalizedLog N L q 1 := by linarith
  refine ⟨pair_arithmetic_child_nonneg hN hd hL hA hQ hp k hbox hx, ?_⟩
  rw [thetaAtom_pair (by omega) hd (hqi 0).1 (hqi 1).1 (hq2 0) (hq2 1)
    ((hqi 0).1.coprime_iff_not_dvd.mpr (hqi 0).2.1)
    ((hqi 1).1.coprime_iff_not_dvd.mpr (hqi 1).2.1) hR, he 0, he 1]
  have hfac : localPrimeFactor d (q 0)*localPrimeFactor (d*q 0) (q 1) ≤
      (2/(q 0:ℝ))*(2/(q 1:ℝ)) :=
    mul_le_mul (localPrimeFactor_le_two_div (d := d) (hq4 0))
      (localPrimeFactor_le_two_div (d := d*q 0) (hq4 1))
      (localPrimeFactor_pos (by exact_mod_cast hq2 1)).le (by positivity)
  have hrat : localPrimeFactor d (q 0)*localPrimeFactor (d*q 0) (q 1)/
      (1-normalizedLog N L q 0-normalizedLog N L q 1) ≤
        20*((1/(q 0:ℝ))*(1/(q 1:ℝ))) := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ (2/(q 0:ℝ))*(2/(q 1:ℝ)) := hfac
      _ = (20*((1/(q 0:ℝ))*(1/(q 1:ℝ))))*(1/5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left hrat ht

theorem singleTerm_bounds {N d : ℕ} {Q L : ℝ} {p : W2Parameters} {k : Fin 3}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (hp : W2Geometry p)
    {q : Fin 1 → ℕ} (hq : q ∈ singleCarrier N L p k) (b : FloorAtom) :
    0 ≤ singleTerm N Q L d p b q ∧
      singleTerm N Q L d p b q ≤ 4*thetaAtom N Q d/(q 0:ℝ) := by
  have hh := single_theta_bounds hN hd hL hA hQ hp hq
  unfold singleTerm
  split_ifs
  · exact hh
  · exact ⟨le_rfl, hh.1.trans hh.2⟩

theorem pairTerm_bounds {N d : ℕ} {Q L : ℝ} {p : W2Parameters} {k : Fin 4}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (hp : W2Geometry p)
    {q : Fin 2 → ℕ} (hq : q ∈ pairCarrier N L p k) (b : FloorAtom) :
    0 ≤ pairTerm N Q L d p k b q ∧
      pairTerm N Q L d p k b q ≤ 20*thetaAtom N Q d*((1/(q 0:ℝ))*(1/(q 1:ℝ))) := by
  have hh := pair_theta_bounds hN hd hL hA hQ hp hq
  unfold pairTerm
  split_ifs
  · exact hh
  · exact ⟨le_rfl, hh.1.trans hh.2⟩

/-- Quantitative finite payment before any limit or family normalization. -/
theorem removedSingleAtom_bound {N d : ℕ} {Q L A : ℝ} {p : W2Parameters}
    (hN : 4 ≤ N) (hd : 0 < d) (hdN : d ≤ N) (hL : 0 < L) (hL1 : L ≤ 1)
    (hA : 4 ≤ A) (hfloor : A ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (hp : W2Geometry p) (k : Fin 3) (b : FloorAtom) :
    0 ≤ removedSingleAtom N Q L d p k b ∧
      removedSingleAtom N Q L d p k b ≤
        4*thetaAtom N Q d*(obstructionCount N/A) := by
  let T := removedSingle N d L p k
  let B := badPool N d A L (faces p)
  have hN1 : 1 < N := by omega
  have hA0 : 0 < A := by linarith
  have hB (q : Fin 1 → ℕ) (hq : q ∈ T) : q 0 ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨box_in_primePool hN1 hL1 hfloor
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1 0, removedSingle_obstructed hq⟩
  have hsum : (∑ q ∈ T, 1/(q 0:ℝ)) ≤ obstructionCount N/A := by
    have hsub : T.image (fun q => q 0) ⊆ B := by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      exact hB q hq
    have he : (∑ q ∈ T, 1/(q 0:ℝ)) = ∑ a ∈ T.image (fun q => q 0), 1/(a:ℝ) := by
      rw [Finset.sum_image]
      intro q _ r _ h
      funext i
      fin_cases i
      exact h
    rw [he]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
      (badPool_reciprocal_le hN1 hL hd hdN hA0 (faces p))
  have ht := thetaAtom_nonneg hN hd (sameQ_residual_gt_one hN1 hd hL hQ)
  have hb (q) (hq : q ∈ T) := singleTerm_bounds hN hd hL (hA.trans hfloor) hQ hp
    (Finset.mem_filter.mp hq).1 b
  refine ⟨Finset.sum_nonneg (fun q hq => (hb q hq).1), ?_⟩
  calc
    _ ≤ ∑ q ∈ T, 4*thetaAtom N Q d/(q 0:ℝ) := Finset.sum_le_sum (fun q hq => (hb q hq).2)
    _ = (4*thetaAtom N Q d)*(∑ q ∈ T, 1/(q 0:ℝ)) := by rw [Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

theorem removedPairAtom_bound {N d : ℕ} {Q L A : ℝ} {p : W2Parameters}
    (hN : 4 ≤ N) (hd : 0 < d) (hdN : d ≤ N) (hL : 0 < L) (hL1 : L ≤ 1)
    (hA : 4 ≤ A) (hfloor : A ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (hp : W2Geometry p) (k : Fin 4) (b : FloorAtom) :
    0 ≤ removedPairAtom N Q L d p k b ∧
      removedPairAtom N Q L d p k b ≤
        40*thetaAtom N Q d*(obstructionCount N/A)*harmonicBudget N := by
  let T := removedPair N d L p k
  let P := primePool N A
  let B := badPool N d A L (faces p)
  have hN1 : 1 < N := by omega
  have hA0 : 0 < A := by linarith
  have hP (q : Fin 2 → ℕ) (hq : q ∈ T) (i : Fin 2) : q i ∈ P :=
    box_in_primePool hN1 hL1 hfloor (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1 i
  have hB (q : Fin 2 → ℕ) (hq : q ∈ T) : q 0 ∈ B ∨ q 1 ∈ B := by
    rcases removedPair_obstructed hq with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hP q hq 0,h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hP q hq 1,h⟩)
  have hs := pair_bad_reciprocal_le P B (Finset.filter_subset _ _) T
    (fun q hq => ⟨hP q hq 0,hP q hq 1⟩) hB
  have hbn : 0 ≤ ∑ q ∈ B, 1/(q:ℝ) := Finset.sum_nonneg (by intros; positivity)
  have hpn : 0 ≤ ∑ q ∈ P, 1/(q:ℝ) := Finset.sum_nonneg (by intros; positivity)
  have hb := badPool_reciprocal_le (A := A) hN1 hL hd hdN hA0 (faces p)
  have hp' := primePool_reciprocal_le N A
  have hs' : (∑ q ∈ T, (1/(q 0:ℝ))*(1/(q 1:ℝ))) ≤
      2*(obstructionCount N/A)*harmonicBudget N :=
    hs.trans (mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num)) hp' hpn
      (mul_nonneg (by norm_num) (hbn.trans hb)))
  have ht := thetaAtom_nonneg hN hd (sameQ_residual_gt_one hN1 hd hL hQ)
  have hb' (q) (hq : q ∈ T) := pairTerm_bounds hN hd hL (hA.trans hfloor) hQ hp
    (Finset.mem_filter.mp hq).1 b
  refine ⟨Finset.sum_nonneg (fun q hq => (hb' q hq).1), ?_⟩
  calc
    _ ≤ ∑ q ∈ T, 20*thetaAtom N Q d*((1/(q 0:ℝ))*(1/(q 1:ℝ))) :=
      Finset.sum_le_sum (fun q hq => (hb' q hq).2)
    _ = (20*thetaAtom N Q d)*(∑ q ∈ T, (1/(q 0:ℝ))*(1/(q 1:ℝ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ (20*thetaAtom N Q d)*(2*(obstructionCount N/A)*harmonicBudget N) :=
      mul_le_mul_of_nonneg_left hs' (by positivity)
    _ = _ := by ring

/-- The original fixed rows have no deletion. Every strict coefficient is
positive, and deletions can only decrease the unnormalised original row. -/
theorem freshRow_bounds {N d : ℕ} {Q L : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hL : 0 < L) (hA : 4 ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (j : Fin 36) (b : RowAtom) :
    0 ≤ freshRow N Q L d j b ∧ 0 ≤ removedRow N Q L d j b ∧
      freshRow N Q L d j b ≤ arithmeticRow N Q L d (.inr j) b := by
  have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hs (k : Fin 3) (b : FloorAtom) (T : Finset (Fin 1 → ℕ))
      (hT : T ⊆ singleCarrier N L (originalW2At j) k) :
      0 ≤ ∑ q ∈ T, singleTerm N Q L d (originalW2At j) b q :=
    Finset.sum_nonneg (fun q hq => (singleTerm_bounds hN hd hL hA hQ hp (hT hq) b).1)
  have hpair (k : Fin 4) (b : FloorAtom) (T : Finset (Fin 2 → ℕ))
      (hT : T ⊆ pairCarrier N L (originalW2At j) k) :
      0 ≤ ∑ q ∈ T, pairTerm N Q L d (originalW2At j) k b q :=
    Finset.sum_nonneg (fun q hq => (pairTerm_bounds hN hd hL hA hQ hp (hT hq) b).1)
  have ht := thetaAtom_nonneg hN hd (sameQ_residual_gt_one (by omega) hd hL hQ)
  have hf : 0 ≤ freshRow N Q L d j b := by
    cases b with
    | inl b =>
        exact div_nonneg (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) (pointAtom_nonneg ht _ _ _)) (pointAtom_nonneg ht _ _ _))
          (Finset.sum_nonneg (fun k _ => hpair k b _ (Finset.filter_subset _ _)))) (by norm_num)
    | inr b => exact div_nonneg
        (Finset.sum_nonneg (fun k _ => hs k b _ (Finset.filter_subset _ _))) (by norm_num)
  have hr : 0 ≤ removedRow N Q L d j b := by
    cases b with
    | inl b => exact div_nonneg
        (Finset.sum_nonneg (fun k _ => hpair k b _ (Finset.filter_subset _ _))) (by norm_num)
    | inr b => exact div_nonneg
        (Finset.sum_nonneg (fun k _ => hs k b _ (Finset.filter_subset _ _))) (by norm_num)
  refine ⟨hf, hr, ?_⟩
  rw [arithmeticRow_split]
  exact le_add_of_nonneg_right hr

theorem removedRow_bound {N d : ℕ} {Q L A : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hdN : d ≤ N) (hL : 0 < L) (hL1 : L ≤ 1)
    (hA : 4 ≤ A) (hfloor : A ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (j : Fin 36) (b : RowAtom) :
    removedRow N Q L d j b ≤
      40*(obstructionCount N*harmonicBudget N/A)*thetaAtom N Q d := by
  have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have ht := thetaAtom_nonneg hN hd (sameQ_residual_gt_one (by omega) hd hL hQ)
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hK : 0 ≤ obstructionCount N := by unfold obstructionCount; positivity
  have hH : 1 ≤ harmonicBudget N := by unfold harmonicBudget; linarith
  have hA0 : 0 < A := by linarith
  cases b with
  | inl b =>
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
        (fun k _ => (removedPairAtom_bound hN hd hdN hL hL1 hA hfloor hQ hp k b).2)
      norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      change (∑ k : Fin 4, removedPairAtom N Q L d (originalW2At j) k b)/5 ≤ _
      have hh : 0 ≤ thetaAtom N Q d*(obstructionCount N/A)*harmonicBudget N := by positivity
      nlinarith [hs]
  | inr b =>
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (fun k _ => (removedSingleAtom_bound hN hd hdN hL hL1 hA hfloor hQ hp k b).2)
      norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      have hm := mul_le_mul_of_nonneg_left hH
        (mul_nonneg ht (div_nonneg hK hA0.le))
      change (∑ k : Fin 3, removedSingleAtom N Q L d (originalW2At j) k b)/5 ≤ _
      nlinarith [hs]

def rowGap (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (g : Fin 430) : ℝ :=
  ∑ b : RowAtom, |arithmeticRow N Q L d (.inr j) b - freshRow N Q L d j b| *
    |oldAtomValue (precedingH g) (precedingh g) b|

def rowMagnitude (g : Fin 430) : ℝ :=
  ∑ b : RowAtom, |oldAtomValue (precedingH g) (precedingh g) b|

def magnitudeEnvelope : ℝ := ∑ g : Fin 430, rowMagnitude g

theorem magnitude_le_envelope (g : Fin 430) : rowMagnitude g ≤ magnitudeEnvelope :=
  Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ g)

theorem rowGap_bound {N d : ℕ} {Q L A : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hdN : d ≤ N) (hL : 0 < L) (hL1 : L ≤ 1)
    (hA : 4 ≤ A) (hfloor : A ≤ (N:ℝ)^(L/10))
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (j : Fin 36) (g : Fin 430) :
    rowGap N Q L d j g ≤
      (40*magnitudeEnvelope)*(obstructionCount N*harmonicBudget N/A)*thetaAtom N Q d := by
  have ht := thetaAtom_nonneg hN hd (sameQ_residual_gt_one (by omega) hd hL hQ)
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hA0 : 0 < A := by linarith
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hcoef : 0 ≤ 40*(obstructionCount N*harmonicBudget N/A)*thetaAtom N Q d := by
    unfold obstructionCount harmonicBudget
    positivity
  calc
    _ ≤ ∑ b : RowAtom, (40*(obstructionCount N*harmonicBudget N/A)*thetaAtom N Q d)*
        |oldAtomValue (precedingH g) (precedingh g) b| := by
      apply Finset.sum_le_sum
      intro b _
      have hb := freshRow_bounds hN hd hL (hA.trans hfloor) hQ j b
      have he : arithmeticRow N Q L d (.inr j) b - freshRow N Q L d j b =
          removedRow N Q L d j b := by rw [arithmeticRow_split]; ring
      rw [he, abs_of_nonneg hb.2.1]
      exact mul_le_mul_of_nonneg_right
        (removedRow_bound hN hd hdN hL hL1 hA hfloor hQ j b) (abs_nonneg _)
    _ = (40*(obstructionCount N*harmonicBudget N/A)*thetaAtom N Q d)*rowMagnitude g :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (40*(obstructionCount N*harmonicBudget N/A)*thetaAtom N Q d)*magnitudeEnvelope :=
      mul_le_mul_of_nonneg_left (magnitude_le_envelope g) hcoef
    _ = _ := by ring

/-- One threshold precedes Q,d,L,the seven domains and all430 old arrays.
The finite depth and the original selected root construction supply Lmin
at the consumer; this theorem does not invent a count-history licence. -/
theorem uniform_W2_rowGap {Lmin epsilon : ℝ} (hmin : 0 < Lmin) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q L : ℝ, ∀ d : ℕ,
      Lmin ≤ L → L ≤ 1 → 0 < d → d ≤ N → Q = (d:ℝ)*(N:ℝ)^L →
      ∀ j : Fin 36, ∀ g : Fin 430,
        rowGap N Q L d j g ≤ epsilon*thetaAtom N Q d ∧
        ∀ b : RowAtom, 0 ≤ freshRow N Q L d j b ∧
          freshRow N Q L d j b ≤ arithmeticRow N Q L d (.inr j) b := by
  let a := Lmin/10
  have ha : 0 < a := by dsimp [a]; positivity
  have hlim := (removalRate_tendsto ha).const_mul (40*magnitudeEnvelope)
  simp only [mul_zero] at hlim
  obtain ⟨Te,hTe⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds he))
  obtain ⟨Ta,hTa⟩ := exists_nat_ge ((4:ℝ)^(1/a))
  refine ⟨max 4 (max Ta Te), le_max_left _ _, ?_⟩
  intro N hN Q L d hLmin hL1 hd hdN hQ j g
  have hN4 : 4 ≤ N := by omega
  have hL : 0 < L := hmin.trans_le hLmin
  have hbase : (4:ℝ)^(1/a) ≤ (N:ℝ) := hTa.trans (by exact_mod_cast (show Ta ≤ N by omega))
  have hA : (4:ℝ) ≤ (N:ℝ)^a := by
    have hc : ((4:ℝ)^(1/a))^a = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)]
      have heq : (1/a)*a = (1:ℝ) := by field_simp [ha.ne']
      rw [heq, Real.rpow_one]
    rw [← hc]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hbase ha.le
  have hfloor : (N:ℝ)^a ≤ (N:ℝ)^(L/10) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (div_le_div_of_nonneg_right hLmin (by norm_num))
  have ht := thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one (by omega) hd hL hQ)
  have herr := rowGap_bound hN4 hd hdN hL hL1 hA hfloor hQ j g
  have hsmall := (hTe N (by omega)).le
  refine ⟨herr.trans (mul_le_mul_of_nonneg_right hsmall ht), ?_⟩
  intro b
  have hb := freshRow_bounds hN4 hd hL (hA.trans hfloor) hQ j b
  exact ⟨hb.1,hb.2.2⟩

end
end ImbalancedChen.Part5OriginalH430W2DiscardedMass
