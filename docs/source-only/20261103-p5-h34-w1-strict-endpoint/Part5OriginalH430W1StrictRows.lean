import ImbalancedChen.Part5OriginalH430W1WindowDictionary
import ImbalancedChen.Part5OriginalH430ArithmeticAtomRows
import ImbalancedChen.Part5OriginalH430ImmutableBankProfiles

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact W1 coefficient split, finite endpoint payment, and one threshold for
all430 OLD arrays. Only the lower-endpoint prime is removed from W1's
already d*N-masked row. The original one-half coefficient is used once.
This does not license the scalar bank candidate, its base or original counts.
-/
namespace ImbalancedChen.Part5OriginalH430W1StrictRows

noncomputable section
open Set Classical
open scoped BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalHalfOpenProfileCarrier P2OriginalOldProfilePrimeLimits
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430W1WindowDictionary
open Part5OriginalH430BuchstabCeilingDictionary (primeFloor)

/-- A natural-prime atom with the same original inherited query. -/
def atomTerm (N : ℕ) (Q : ℝ) (old : List ℕ) (j : Fin 10) (b : FloorAtom) (q : ℕ) : ℝ :=
  if childQuery Q old j q ∈ tableAtomSet true b then thetaAtom N Q (parentProduct old*q) else 0

def strictChildAtom (N : ℕ) (Q chi : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (b : FloorAtom) : ℝ :=
  ∑ q ∈ singleChildren (.w1 i j) N Q old chi, atomTerm N Q old j b q.val

def endpointAtom (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (b : FloorAtom) : ℝ :=
  ∑ q ∈ endpointWindow N Q old i j, atomTerm N Q old j b q

def endpointMass (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ q ∈ endpointWindow N Q old i j, thetaAtom N Q (parentProduct old*q)

def strictRow (N : ℕ) (Q chi : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) : RowAtom → ℝ
  | .inl b => pointAtom (thetaAtom N Q (parentProduct old)) false (W1Anchor j) b
  | .inr b => strictChildAtom N Q chi old i j b/2

def endpointRow (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) : RowAtom → ℝ
  | .inl _ => 0
  | .inr b => endpointAtom N Q old i j b/2

theorem original_child_atom_sum (N : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (b : FloorAtom) :
    W1ChildAtom N Q (parentProduct old) i j b =
      ∑ q ∈ halfWindow N Q old i j, atomTerm N Q old j b q := by
  unfold W1ChildAtom profileAtomSum
  apply Finset.sum_congr rfl
  intro q _
  change (Set.univ ∩ tablePullback true (childQuery Q old j) b).indicator
    (fun _ => thetaAtom N Q (parentProduct old*q)) q = atomTerm N Q old j b q
  by_cases hb : childQuery Q old j q ∈ tableAtomSet true b <;>
    simp [atomTerm,tablePullback,hb]

theorem original_child_split {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10)
    (hceil : physicalLevel N Q old/W1Target i ≤ chi) (b : FloorAtom) :
    W1ChildAtom N Q (parentProduct old) i j b =
      strictChildAtom N Q chi old i j b + endpointAtom N Q old i j b := by
  rw [original_child_atom_sum]
  exact window_sum_split hw i j hceil (atomTerm N Q old j b)

/-- Every upper point is unchanged. No second factor 1/2 is introduced. -/
theorem arithmeticRow_split {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (L : ℝ) (i : Fin 7) (j : Fin 10)
    (hceil : physicalLevel N Q old/W1Target i ≤ chi) (b : RowAtom) :
    arithmeticRow N Q L (parentProduct old) (.inl (i,j)) b =
      strictRow N Q chi old i j b + endpointRow N Q old i j b := by
  cases b with
  | inl b => simp only [arithmeticRow,strictRow,endpointRow,add_zero]
  | inr b =>
      change W1ChildAtom N Q (parentProduct old) i j b/2 =
        strictChildAtom N Q chi old i j b/2 + endpointAtom N Q old i j b/2
      rw [original_child_split hw i j hceil]
      ring

/-- True child Theta is nonnegative by its actual product support. -/
theorem window_theta_nonneg {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hq : q ∈ halfWindow N Q old i j) : 0 ≤ thetaAtom N Q (parentProduct old*q) := by
  have hp := ((mem_halfWindow hw i j).mp hq).1
  have hd := Nat.mul_pos hw.2.1 hp.pos
  apply thetaAtom_nonneg hN hd
  apply (lt_div_iff₀ (Nat.cast_pos.mpr hd)).mpr
  simpa only [one_mul] using window_product_lt hw hq

/-- Reuse the exact singular multiplier; never replace it by 1/(q-1). -/
theorem window_theta_le {N q : ℕ} {Q chi A : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hq : q ∈ halfWindow N Q old i j) (hA : 4 ≤ A) (hAq : A ≤ (q:ℝ)) :
    thetaAtom N Q (parentProduct old*q) ≤ (4/A)*thetaAtom N Q (parentProduct old) := by
  have h := (mem_halfWindow hw i j).mp hq
  have hq4 : (4:ℝ) ≤ q := hA.trans hAq
  have hq0 : (0:ℝ) < q := by linarith
  have hA0 : 0 < A := by linarith
  have hq2 : 2 < q := by exact_mod_cast (show (2:ℝ) < q by linarith)
  have hpN := (Nat.coprime_mul_iff_right.mp h.2.1).1
  have hR := (parentWindow_logs hw).2.1
  have ht := thetaAtom_nonneg hN hw.2.1 hR
  have hu : relativePrime Q old q ≤ 1/2 := h.2.2.2.le.trans (target_recip_le_half i)
  have hden : 0 < 1-relativePrime Q old q := by linarith
  have hratio : localPrimeFactor (parentProduct old) q/(1-relativePrime Q old q) ≤ 4/(q:ℝ) := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ 2/(q:ℝ) := Part5OriginalH430BuchstabCeilingPayment.localPrimeFactor_le_two_div hq4
      _ = (4/(q:ℝ))*(1/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hdiv : 4/(q:ℝ) ≤ 4/A := div_le_div_of_nonneg_left (by norm_num) hA0 hAq
  rw [thetaAtom_single (by omega) hw.2.1 h.1 hq2 hpN hR]
  change thetaAtom N Q (parentProduct old)*
    (localPrimeFactor (parentProduct old) q/(1-relativePrime Q old q)) ≤ _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hratio.trans hdiv) ht

theorem atomTerm_bounds {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hq : q ∈ halfWindow N Q old i j) (b : FloorAtom) :
    0 ≤ atomTerm N Q old j b q ∧ atomTerm N Q old j b q ≤ thetaAtom N Q (parentProduct old*q) := by
  have ht := window_theta_nonneg hN hw hq
  unfold atomTerm
  split_ifs
  · exact ⟨ht,le_rfl⟩
  · exact ⟨le_rfl,ht⟩

theorem endpointAtom_bounds {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10) (b : FloorAtom) :
    0 ≤ endpointAtom N Q old i j b ∧
      endpointAtom N Q old i j b ≤ endpointMass N Q old i j := by
  constructor
  · exact Finset.sum_nonneg (fun q hq =>
      (atomTerm_bounds hN hw (Finset.mem_filter.mp hq).1 b).1)
  · exact Finset.sum_le_sum (fun q hq =>
      (atomTerm_bounds hN hw (Finset.mem_filter.mp hq).1 b).2)

theorem endpointMass_bounds {N : ℕ} {Q chi A : ℝ} {old : List ℕ}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10)
    (hA : 4 ≤ A) (hfloor : A ≤ primeFloor N Q old) :
    0 ≤ endpointMass N Q old i j ∧
      endpointMass N Q old i j ≤ (4/A)*thetaAtom N Q (parentProduct old) := by
  have ht := thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hc : (0:ℝ) ≤ (4/A)*thetaAtom N Q (parentProduct old) := mul_nonneg (by positivity) ht
  refine ⟨Finset.sum_nonneg (fun q hq => window_theta_nonneg hN hw (Finset.mem_filter.mp hq).1),?_⟩
  calc
    _ ≤ ∑ _q ∈ endpointWindow N Q old i j, (4/A)*thetaAtom N Q (parentProduct old) := by
      apply Finset.sum_le_sum
      intro q hq
      have hh := (Finset.mem_filter.mp hq).1
      exact window_theta_le hN hw hh hA (hfloor.trans (window_primeFloor_le hw hh))
    _ = ((endpointWindow N Q old i j).card:ℝ)*((4/A)*thetaAtom N Q (parentProduct old)) := by simp
    _ ≤ 1*((4/A)*thetaAtom N Q (parentProduct old)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast endpoint_card_le_one hw i j) hc
    _ = _ := one_mul _

theorem strictRow_bounds {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi) (L : ℝ) (i : Fin 7) (j : Fin 10)
    (hceil : physicalLevel N Q old/W1Target i ≤ chi) (b : RowAtom) :
    0 ≤ strictRow N Q chi old i j b ∧
      strictRow N Q chi old i j b ≤ arithmeticRow N Q L (parentProduct old) (.inl (i,j)) b := by
  have he := arithmeticRow_split hw L i j hceil b
  cases b with
  | inl b =>
      exact ⟨pointAtom_nonneg (thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1) _ _ _,le_rfl⟩
  | inr b =>
      have hs : 0 ≤ strictChildAtom N Q chi old i j b := by
        apply Finset.sum_nonneg
        intro q hq
        have hh := (Finset.mem_filter.mp ((mem_strictWindow_iff_child hw i j hceil q).mpr hq)).1
        exact (atomTerm_bounds hN hw hh b).1
      refine ⟨div_nonneg hs (by norm_num),?_⟩
      have hb := (endpointAtom_bounds hN hw i j b).1
      change strictChildAtom N Q chi old i j b/2 ≤ _
      change arithmeticRow N Q L (parentProduct old) (.inl (i,j)) (.inr b) =
        strictChildAtom N Q chi old i j b/2 + endpointAtom N Q old i j b/2 at he
      linarith

def rowGap (N : ℕ) (Q chi : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom,
    |arithmeticRow N Q (physicalLevel N Q old) (parentProduct old) (.inl (i,j)) b -
      strictRow N Q chi old i j b|*|oldAtomValue oldH oldh b|

theorem rowGap_le {N : ℕ} {Q chi A : ℝ} {old : List ℕ}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10)
    (hceil : physicalLevel N Q old/W1Target i ≤ chi) (hA : 4 ≤ A)
    (hfloor : A ≤ primeFloor N Q old) (oldH oldh : Fin 200 → ℤ) :
    rowGap N Q chi old i j oldH oldh ≤
      atomMagnitude oldh*(2/A)*thetaAtom N Q (parentProduct old) := by
  have he : rowGap N Q chi old i j oldH oldh =
      ∑ b : FloorAtom, (endpointAtom N Q old i j b/2)*|floorAtomValue oldh b| := by
    unfold rowGap
    simp_rw [arithmeticRow_split hw (physicalLevel N Q old) i j hceil]
    simp only [add_sub_cancel_left,Fintype.sum_sum_type,endpointRow,oldAtomValue,
      abs_zero,zero_mul,Finset.sum_const_zero,zero_add]
    apply Finset.sum_congr rfl
    intro b _
    rw [abs_of_nonneg (div_nonneg (endpointAtom_bounds hN hw i j b).1 (by norm_num))]
  rw [he]
  calc
    _ ≤ ∑ b : FloorAtom, (endpointMass N Q old i j/2)*|floorAtomValue oldh b| :=
      Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (endpointAtom_bounds hN hw i j b).2 (by norm_num)) (abs_nonneg _))
    _ = (endpointMass N Q old i j/2)*atomMagnitude oldh := by rw [atomMagnitude,Finset.mul_sum]
    _ ≤ (((4/A)*thetaAtom N Q (parentProduct old))/2)*atomMagnitude oldh :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (endpointMass_bounds hN hw i j hA hfloor).2 (by norm_num))
        (atomMagnitude_nonneg oldh)
    _ = _ := by ring

/-- Exact applied row on the PRODUCTION strict child carrier. Every
closed-knot value is retained; the half coefficient appears exactly once. -/
theorem strictRow_value (N : ℕ) (Q chi : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (oldH oldh : Fin 200 → ℤ) :
    (∑ b : RowAtom, strictRow N Q chi old i j b*oldAtomValue oldH oldh b) =
      thetaAtom N Q (parentProduct old)*tableFunction false oldH (W1Anchor j) +
      (∑ q ∈ singleChildren (.w1 i j) N Q old chi,
        thetaAtom N Q (parentProduct old*q.val)*tableFunction true oldh (childQuery Q old j q.val))/2 := by
  have hinner (q : ℕ) :
      (∑ b : FloorAtom, atomTerm N Q old j b q*floorAtomValue oldh b) =
        thetaAtom N Q (parentProduct old*q)*tableFunction true oldh (childQuery Q old j q) := by
    rw [tableFunction,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : childQuery Q old j q ∈ tableAtomSet true b <;> simp [atomTerm,hb]
  simp only [Fintype.sum_sum_type,strictRow,oldAtomValue]
  rw [pointAtom_value]
  apply congrArg (fun z : ℝ => thetaAtom N Q (parentProduct old)*
    tableFunction false oldH (W1Anchor j) + z)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ => z/2)
  simp only [strictChildAtom,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun q _ => hinner q.val)

/-- A symbolic finite envelope, not evaluation of the 430-round producer. -/
def lowerMagnitudeEnvelope : ℝ := 1 + ∑ g : Fin 430, atomMagnitude (precedingh g)

theorem lowerMagnitudeEnvelope_pos : 0 < lowerMagnitudeEnvelope := by
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun g _ => atomMagnitude_nonneg (precedingh g))
  unfold lowerMagnitudeEnvelope
  linarith

theorem lowerMagnitude_le (g : Fin 430) : atomMagnitude (precedingh g) ≤ lowerMagnitudeEnvelope := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (fun g _ => atomMagnitude_nonneg (precedingh g)) (Finset.mem_univ g)
  unfold lowerMagnitudeEnvelope
  linarith

/-- The threshold precedes both action parameters, all histories and g.
The positive residual floor is still a geometric input to this local API. -/
theorem uniform_rowGap {Lmin epsilon : ℝ} (hmin : 0 < Lmin) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → 4 ≤ N ∧
      ∀ Q chi : ℝ, ∀ old : List ℕ, ∀ i : Fin 7, ∀ j : Fin 10,
      parentWindow N Q old chi → Lmin ≤ physicalLevel N Q old →
      physicalLevel N Q old/W1Target i ≤ chi → ∀ g : Fin 430,
      rowGap N Q chi old i j (precedingH g) (precedingh g) ≤
        epsilon*thetaAtom N Q (parentProduct old) := by
  let A := max (4:ℝ) (2*lowerMagnitudeEnvelope/epsilon)
  have hA : 4 ≤ A := le_max_left _ _
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hsmall : lowerMagnitudeEnvelope*(2/A) ≤ epsilon := by
    have h := (div_le_iff₀ he).mp (le_max_right (4:ℝ) (2*lowerMagnitudeEnvelope/epsilon))
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hA0).mpr
    change 2*lowerMagnitudeEnvelope ≤ A*epsilon at h
    nlinarith only [h]
  obtain ⟨T,hT⟩ := Part5OriginalH430BuchstabCeilingPayment.exists_uniform_primeFloor hmin hA
  refine ⟨T,?_⟩
  intro N hN
  obtain ⟨hN4,hfloor⟩ := hT N hN
  refine ⟨hN4,?_⟩
  intro Q chi old i j hw hL hceil g
  have ht := thetaAtom_nonneg hN4 hw.2.1 (parentWindow_logs hw).2.1
  calc
    _ ≤ atomMagnitude (precedingh g)*(2/A)*thetaAtom N Q (parentProduct old) :=
      rowGap_le hN4 hw i j hceil hA (hfloor Q old hL) _ _
    _ ≤ lowerMagnitudeEnvelope*(2/A)*thetaAtom N Q (parentProduct old) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (lowerMagnitude_le g) (by positivity)) ht
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall ht

end
end ImbalancedChen.Part5OriginalH430W1StrictRows
