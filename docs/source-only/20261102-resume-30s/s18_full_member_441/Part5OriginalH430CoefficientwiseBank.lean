import ImbalancedChen.Part5OriginalH430TrueAtomLimits
import ImbalancedChen.Part5OriginalH430ImmutableBankProfiles

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual coefficientwise absolute bank payment. The new ideal row is the
literal atom integral in the existing normalized Pi-coordinate carrier;
its full old-table value is proved to be the original action integral.
Both point masses are retained exactly. Every finite arithmetic knot
coefficient is retained. The absolute value is taken coefficient by
coefficient, before the old-array sum and before the parent-family sum.

The original switched/ordinary base discrepancy remains unspent. This
does not declare a full-Member source identity or common441 realization.
-/

namespace ImbalancedChen.Part5OriginalH430CoefficientwiseBank

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalOldProfilePrimeLimits
open P2OriginalPhysicalOldProfileMass P2OriginalBankOldProfilePassage
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalLiteralW1OldProfile P5OriginalActionMassBound
open P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430TrueAtomLimits Part5OriginalH430ImmutableBankProfiles

def trueRow (N : ℕ) (L : ℝ) (d : ℕ) : Original106Action → RowAtom → ℝ
  | .inl (i,j), .inl b => pointAtom 1 false (W1Anchor j) b
  | .inl (i,j), .inr b =>
      maskedSingleAtom N L d (1/W1Anchor j) (1/W1Target i) (W1Anchor j) b/2
  | .inr j, .inl b =>
      (4*pointAtom 1 false (originalW2At j).s0 b +
        pointAtom 1 false (originalW2At j).phi1 b +
        ∑ k : Fin 4, truePairAtom N L d (originalW2At j) k b)/5
  | .inr j, .inr b =>
      (∑ k : Fin 3, trueSingleAtom N L d (a0 (originalW2At j))
        (singletonTop (originalW2At j) k) (originalW2At j).s0 b)/5

def integralRow : Original106Action → RowAtom → ℝ
  | .inl (i,j), .inl b => pointAtom 1 false (W1Anchor j) b
  | .inl (i,j), .inr b =>
      singleAtomIntegral (1/W1Anchor j) (1/W1Target i) (W1Anchor j) b/2
  | .inr j, .inl b =>
      (4*pointAtom 1 false (originalW2At j).s0 b +
        pointAtom 1 false (originalW2At j).phi1 b +
        ∑ k : Fin 4, pairAtomIntegral (originalW2At j) k b)/5
  | .inr j, .inr b =>
      (∑ k : Fin 3, singleAtomIntegral (a0 (originalW2At j))
        (singletonTop (originalW2At j) k) (originalW2At j).s0 b)/5

theorem singleAtomIntegral_value {lo hi : ℝ} (hlo : (1/5:ℝ) ≤ lo)
    (hhi : hi ≤ 1/2) (s0 : ℝ) (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, singleAtomIntegral lo hi s0 b*floorAtomValue nums b) =
      singleOldIntegral lo hi s0 nums := by
  calc
    _ = oldProfileIntegral (singleHalf lo hi) residualSingle (singleRho s0) true nums := by
      unfold oldProfileIntegral singleAtomIntegral singleAtomDomain
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := single_profile_original_integral hlo hhi s0 true nums

theorem pairAtomIntegral_value {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) (nums : Fin 200 → ℤ) :
    (∑ b : FloorAtom, pairAtomIntegral p k b*floorAtomValue nums b) =
      pairOldIntegral p k nums := by
  calc
    _ = oldProfileIntegral (pairHalf p k) residualPair (pairProfile p k) false nums := by
      unfold oldProfileIntegral pairAtomIntegral pairAtomDomain
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := pair_profile_original_integral hp k nums

/-- This is the manuscript action itself, including its closed minima.
The Pi-coordinate row is not defined by the claimed value or its error. -/
theorem integralRow_value (oldH oldh : Fin 200 → ℤ) (a : Original106Action) :
    (∑ b : RowAtom, integralRow a b*oldAtomValue oldH oldh b) =
      idealProfile oldH oldh a := by
  rcases a with ⟨i,j⟩ | j
  · simp only [Fintype.sum_sum_type,integralRow,oldAtomValue,idealProfile]
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div,pointAtom_value,
      singleAtomIntegral_value (W1_endpoints i j).1 (W1_endpoints i j).2.1]
    simp only [one_mul,W1OldIntegral]
  · have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
    have hp : (∑ b : FloorAtom,
        (∑ k : Fin 4, pairAtomIntegral (originalW2At j) k b)*floorAtomValue oldH b) =
        ∑ k : Fin 4, pairOldIntegral (originalW2At j) k oldH := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [pairAtomIntegral_value hg]
    have hs : (∑ b : FloorAtom,
        (∑ k : Fin 3, singleAtomIntegral (a0 (originalW2At j))
          (singletonTop (originalW2At j) k) (originalW2At j).s0 b)*floorAtomValue oldh b) =
        ∑ k : Fin 3, singleOldIntegral (a0 (originalW2At j))
          (singletonTop (originalW2At j) k) (originalW2At j).s0 oldh := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact singleAtomIntegral_value hg.1 (W2_singleton_top hg k) _ oldh
    simp only [Fintype.sum_sum_type,integralRow,oldAtomValue,idealProfile]
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div,Finset.sum_div]
    simp only [add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
    rw [pointAtom_value,pointAtom_value,hp,hs]
    unfold W2OldIntegral
    ring

theorem arithmeticRow_eq_theta_trueRow {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hA : 4 ≤ (N:ℝ)^(L/10)) (hQ : Q = (d:ℝ)*(N:ℝ)^L)
    (a : Original106Action) (b : RowAtom) :
    arithmeticRow N Q L d a b = thetaAtom N Q d*trueRow N L d a b := by
  have hpoint (s : ℝ) (b : FloorAtom) :
      pointAtom (thetaAtom N Q d) false s b = thetaAtom N Q d*pointAtom 1 false s b := by
    simp only [pointAtom,one_mul]
  rcases a with ⟨i,j⟩ | j
  · cases b with
    | inl b => exact hpoint _ b
    | inr b =>
        change W1ChildAtom N Q d i j b/2 = _
        rw [W1ChildAtom_eq hN hd hL hA hQ]
        change (thetaAtom N Q d * maskedSingleAtom N L d _ _ _ b)/2 =
          thetaAtom N Q d * (maskedSingleAtom N L d _ _ _ b/2)
        ring
  · have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
    cases b with
    | inl b =>
        simp only [arithmeticRow,trueRow,hpoint,pairChildAtom_eq hN hd hL hA hQ hg,
          ← Finset.mul_sum]
        ring
    | inr b =>
        simp only [arithmeticRow,trueRow,
          singleChildAtom_eq hN hd hL (W2_singleton_top hg _) hA hQ,← Finset.mul_sum]
        ring

/-- One finite common threshold for all 106 actions and all 802 polar
atoms. Neither a signed-profile estimate nor an old array is a premise. -/
theorem all106_true_row_atom_error {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      ∀ d : ℕ, 0 < d → d ≤ N → ∀ a : Original106Action, ∀ b : RowAtom,
      |trueRow N L d a b-integralRow a b| < epsilon := by
  have h1 (q : (Fin 7 × Fin 10) × FloorAtom) : ∀ᶠ N : ℕ in atTop,
      ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ, 0 < d → d ≤ N →
      |maskedSingleAtom N L d (1/W1Anchor q.1.2) (1/W1Target q.1.1)
        (W1Anchor q.1.2) q.2 -
        singleAtomIntegral (1/W1Anchor q.1.2) (1/W1Target q.1.1) (W1Anchor q.1.2) q.2| < epsilon := by
    obtain ⟨hlo,hhi,hs⟩ := W1_endpoints q.1.1 q.1.2
    obtain ⟨T,hT⟩ := compact_uniform_masked_single_atom hmin hmax he hlo hhi hs q.2
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  have h2 (q : (Fin 36 × Fin 3) × FloorAtom) : ∀ᶠ N : ℕ in atTop,
      ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |trueSingleAtom N L d (a0 (originalW2At q.1.1))
        (singletonTop (originalW2At q.1.1) q.1.2) (originalW2At q.1.1).s0 q.2-
        singleAtomIntegral (a0 (originalW2At q.1.1))
          (singletonTop (originalW2At q.1.1) q.1.2) (originalW2At q.1.1).s0 q.2| < epsilon := by
    have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem q.1.1)
    obtain ⟨T,hT⟩ := compact_uniform_single_atom hmin hmax he hp.1
      (W2_singleton_top hp q.1.2) (W2_anchor_positive hp) q.2
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  have h3 (q : (Fin 36 × Fin 4) × FloorAtom) : ∀ᶠ N : ℕ in atTop,
      ∀ L ∈ Icc Lmin Lmax, ∀ d : ℕ,
      |truePairAtom N L d (originalW2At q.1.1) q.1.2 q.2-
        pairAtomIntegral (originalW2At q.1.1) q.1.2 q.2| < epsilon := by
    have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem q.1.1)
    obtain ⟨T,hT⟩ := compact_uniform_pair_atom hmin hmax he hp q.1.2 q.2
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((eventually_all.mpr h1).and ((eventually_all.mpr h2).and (eventually_all.mpr h3)))
  refine ⟨T, ?_⟩
  intro N hN L hL d hd hdN a b
  rcases hT N hN with ⟨hW1,hSingle,hPair⟩
  rcases a with ⟨i,j⟩ | j
  · cases b with
    | inl b => simpa only [trueRow,integralRow,sub_self,abs_zero] using he
    | inr b =>
        change |maskedSingleAtom N L d _ _ _ b/2-singleAtomIntegral _ _ _ b/2| < epsilon
        rw [← sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
        apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
        linarith [hW1 ((i,j),b) L hL d hd hdN]
  · cases b with
    | inl b =>
        have heq : trueRow N L d (.inr j) (.inl b)-integralRow (.inr j) (.inl b) =
            (∑ k : Fin 4, (truePairAtom N L d (originalW2At j) k b-
              pairAtomIntegral (originalW2At j) k b))/5 := by
          unfold trueRow integralRow
          rw [Finset.sum_sub_distrib]
          ring
        rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 5)]
        have hs : |∑ k : Fin 4, (truePairAtom N L d (originalW2At j) k b-
              pairAtomIntegral (originalW2At j) k b)| ≤ 4*epsilon := by
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          exact (Finset.sum_le_sum (fun k _ => (hPair ((j,k),b) L hL d).le)).trans_eq (by simp)
        apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 5)).mpr
        linarith
    | inr b =>
        have heq : trueRow N L d (.inr j) (.inr b)-integralRow (.inr j) (.inr b) =
            (∑ k : Fin 3, (trueSingleAtom N L d (a0 (originalW2At j))
              (singletonTop (originalW2At j) k) (originalW2At j).s0 b-
                singleAtomIntegral (a0 (originalW2At j))
                  (singletonTop (originalW2At j) k) (originalW2At j).s0 b))/5 := by
          unfold trueRow integralRow
          rw [Finset.sum_sub_distrib]
          ring
        rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 5)]
        have hs : |∑ k : Fin 3, (trueSingleAtom N L d (a0 (originalW2At j))
              (singletonTop (originalW2At j) k) (originalW2At j).s0 b-
                singleAtomIntegral (a0 (originalW2At j))
                  (singletonTop (originalW2At j) k) (originalW2At j).s0 b)| ≤ 3*epsilon := by
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          exact (Finset.sum_le_sum (fun k _ => (hSingle ((j,k),b) L hL d).le)).trans_eq (by simp)
        apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 5)).mpr
        linarith

theorem all106_arithmetic_row_atom_error {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q L : ℝ, ∀ d : ℕ,
      L ∈ Icc Lmin Lmax → 0 < d → Q = (d:ℝ)*(N:ℝ)^L →
      2 ≤ alpha (Real.log (d:ℝ)/Real.log (N:ℝ)) L →
      ∀ a : Original106Action, ∀ b : RowAtom,
        |arithmeticRow N Q L d a b-thetaAtom N Q d*integralRow a b| ≤
          epsilon*thetaAtom N Q d := by
  obtain ⟨Tp,hTp⟩ := all106_true_row_atom_error hmin hmax he
  obtain ⟨Te,hTe⟩ := P2OriginalCompactThetaMass.compact_multiplier_error (k := 1)
    hmin hmax (by norm_num : (0:ℝ) ≤ 0) he
  refine ⟨max 4 (max Tp Te), ?_⟩
  intro N hN Q L d hL hd hQ halpha a b
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hL0 := hmin.trans_le hL.1
  have ht := thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one hN1 hd hL0 hQ)
  have hp := (hTp N (by omega) L hL d hd
    (prefix_le_target_of_true_alpha hN1 hd hL0 halpha) a b).le
  rw [arithmeticRow_eq_theta_trueRow hN1 hd hL0 (hTe N (by omega) L hL).1 hQ,
    ← mul_sub,abs_mul,abs_of_nonneg ht]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp ht

def absoluteBankError {ι : Type*} (N : ℕ) (Q : ℝ) (S : Finset ι)
    (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ)
    (oldH oldh : Fin 200 → ℤ) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom,
    |parentRow N Q S L d sigma (fun _ => a) b-parentTheta N Q S d sigma*integralRow a b| *
      |oldAtomValue oldH oldh b|

def oldAtomMagnitude (oldH oldh : Fin 200 → ℤ) : ℝ :=
  ∑ b : RowAtom, |oldAtomValue oldH oldh b|

theorem oldAtomMagnitude_nonneg (oldH oldh : Fin 200 → ℤ) :
    0 ≤ oldAtomMagnitude oldH oldh := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Absolute coefficient errors are paid for the complete labelled
same-Q positive family. No cancellation of coefficient signs is used. -/
theorem all106_absolute_bank_errors {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon)
    (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ),
      (∀ i ∈ S, L i ∈ Icc Lmin Lmax) → (∀ i ∈ S, 0 < d i) →
      (∀ i ∈ S, Q = (d i:ℝ)*(N:ℝ)^(L i)) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, 2 ≤ alpha (Real.log (d i:ℝ)/Real.log (N:ℝ)) (L i)) →
      ∀ a : Original106Action,
        absoluteBankError N Q S L d sigma oldH oldh a ≤
          epsilon*parentTheta N Q S d sigma := by
  let eta := epsilon/(1+oldAtomMagnitude oldH oldh)
  have hmag := oldAtomMagnitude_nonneg oldH oldh
  have heta : 0 < eta := div_pos he (by linarith)
  obtain ⟨T,hT⟩ := all106_arithmetic_row_atom_error hmin hmax heta
  refine ⟨max 4 T, ?_⟩
  intro N hN Q ι S L d sigma hL hd hQ hsigma halpha a
  have htheta : 0 ≤ parentTheta N Q S d sigma := by
    apply parentTheta_nonneg (by omega) Q S d sigma hd hsigma
    intro i hi
    exact sameQ_residual_gt_one (by omega) (hd i hi) (hmin.trans_le (hL i hi).1) (hQ i hi)
  have hatom (b : RowAtom) :
      |parentRow N Q S L d sigma (fun _ => a) b-parentTheta N Q S d sigma*integralRow a b| ≤
        eta*parentTheta N Q S d sigma := by
    unfold parentRow parentTheta
    rw [Finset.sum_mul,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    have heq : sigma i*arithmeticRow N Q (L i) (d i) a b-
        (sigma i*thetaAtom N Q (d i))*integralRow a b =
        sigma i*(arithmeticRow N Q (L i) (d i) a b-thetaAtom N Q (d i)*integralRow a b) := by ring
    rw [heq,abs_mul,abs_of_nonneg (hsigma i hi)]
    have hh := mul_le_mul_of_nonneg_left
      (hT N (by omega) Q (L i) (d i) (hL i hi) (hd i hi) (hQ i hi) (halpha i hi) a b)
      (hsigma i hi)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have hp : eta*oldAtomMagnitude oldH oldh ≤ epsilon := by
    have heq : eta*(1+oldAtomMagnitude oldH oldh) = epsilon :=
      div_mul_cancel₀ _ (by linarith)
    nlinarith
  calc
    absoluteBankError N Q S L d sigma oldH oldh a ≤
        ∑ b : RowAtom, (eta*parentTheta N Q S d sigma)*|oldAtomValue oldH oldh b| := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_right (hatom b) (abs_nonneg _)
    _ = (eta*oldAtomMagnitude oldH oldh)*parentTheta N Q S d sigma := by
      rw [oldAtomMagnitude,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ epsilon*parentTheta N Q S d sigma := mul_le_mul_of_nonneg_right hp htheta

/-- Actual seed-only predecessor arrays, with one threshold for all430.
The bound is coefficientwise absolute, rather than an absolute signed profile. -/
theorem immutable430_absolute_bank_errors {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ g : Fin 430, ∀ Q : ℝ,
      ∀ {ι : Type*} (S : Finset ι) (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ),
      (∀ i ∈ S, L i ∈ Icc Lmin Lmax) → (∀ i ∈ S, 0 < d i) →
      (∀ i ∈ S, Q = (d i:ℝ)*(N:ℝ)^(L i)) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, 2 ≤ alpha (Real.log (d i:ℝ)/Real.log (N:ℝ)) (L i)) →
      ∀ a : Original106Action,
        absoluteBankError N Q S L d sigma (precedingH g) (precedingh g) a ≤
          epsilon*parentTheta N Q S d sigma := by
  have hg (g : Fin 430) : ∀ᶠ N : ℕ in atTop, ∀ Q : ℝ,
      ∀ {ι : Type*} (S : Finset ι) (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ),
      (∀ i ∈ S, L i ∈ Icc Lmin Lmax) → (∀ i ∈ S, 0 < d i) →
      (∀ i ∈ S, Q = (d i:ℝ)*(N:ℝ)^(L i)) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, 2 ≤ alpha (Real.log (d i:ℝ)/Real.log (N:ℝ)) (L i)) →
      ∀ a : Original106Action,
        absoluteBankError N Q S L d sigma (precedingH g) (precedingh g) a ≤
          epsilon*parentTheta N Q S d sigma := by
    obtain ⟨T,hT⟩ := all106_absolute_bank_errors hmin hmax he (precedingH g) (precedingh g)
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  exact eventually_atTop.mp (eventually_all.mpr hg)

end
end ImbalancedChen.Part5OriginalH430CoefficientwiseBank
