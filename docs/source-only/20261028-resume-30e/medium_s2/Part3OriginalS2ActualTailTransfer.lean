import ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
import ImbalancedChen.Part3OriginalS2NativeKeyTailPayment
import Mathlib.Tactic

/-!
Exact carrier binding and payment for the independently defined actual
preliminary S2. All key windows and primitive q labels stay literal.
The two explicitly named gate corrections are retained in the conclusion.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2ActualTailTransfer

open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2LambdaDivisorPacket
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2NativeKeyTail
open ImbalancedChen.Part3OriginalS2NativeKeyTailPayment
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open Classical Finset
open scoped BigOperators

noncomputable section

def rawKeyFamily (d : MediumAtom) (k : Key) : Finset CoefficientIndex :=
  (nativeQCarrier d ×ˢ dyadicWindow k.d).sigma
    (fun _ => dyadicWindow k.w ×ˢ dyadicWindow k.w)

theorem primitiveSmoothOuter_eq_native_product (d : MediumAtom) (k : Key) :
    primitiveSmoothOuter d k =
      nativeQCarrier d ×ˢ (dyadicWindow k.d ×ˢ paperPsiNaturalCarrier d.V) := by
  ext t
  simp only [primitiveSmoothOuter, smoothOuterCarrier, nativeQCarrier,
    Finset.mem_filter, Finset.mem_product, and_assoc, and_left_comm, and_comm]

/-- Reindex the independently supplied paired carrier, not a carrier
defined by pulling back the packet to be proved. -/
theorem actual_pair_sum_reindex (d : MediumAtom) (k : Key) (f : S2Index → ℂ) :
    (∑ t ∈ pairedCarrier d k, f (canonicalIndex t)) =
      ∑ c ∈ rawKeyFamily d k, ∑ n₁ ∈ d.alphaCarrier, ∑ n₂ ∈ d.alphaCarrier,
        ∑ m ∈ paperPsiNaturalCarrier d.V, f ⟨c.1, (c.2, ((n₁, n₂), m))⟩ := by
  unfold pairedCarrier
  rw [primitiveSmoothOuter_eq_native_product]
  simp only [innerCarrier, rawKeyFamily, Finset.sum_product, Finset.sum_sigma,
    canonicalIndex]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro small hsmall
  rw [Finset.sum_comm (s := paperPsiNaturalCarrier d.V) (t := dyadicWindow k.w)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm (s := paperPsiNaturalCarrier d.V) (t := d.alphaCarrier)]
  calc
    _ = ∑ n₁ ∈ d.alphaCarrier, ∑ s ∈ dyadicWindow k.w,
        ∑ n₂ ∈ d.alphaCarrier, ∑ m ∈ paperPsiNaturalCarrier d.V,
          f ⟨(q, small), ((r, s), ((n₁, n₂), m))⟩ := by
      apply Finset.sum_congr rfl
      intro n₁ hn₁
      rw [Finset.sum_comm (s := paperPsiNaturalCarrier d.V) (t := dyadicWindow k.w)]
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem paperPsiM_sum_eq_common
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (c : CoefficientIndex)
    (left right : ℕ → ℕ → ℂ) (n₁ n₂ : ℕ) :
    (∑ m ∈ paperPsiNaturalCarrier d.V,
      samePsiTerm d left right ⟨c.1, (c.2, ((n₁, n₂), m))⟩) =
      ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        samePsiTerm d left right ⟨c.1, (c.2, ((n₁, n₂), m))⟩ := by
  have hV : 0 < d.V := by linarith [hd.2.1]
  have hsub : paperPsiNaturalCarrier d.V ⊆ d.transposedAtom.commonSmoothCarrier := by
    intro m hm
    have hhi : (m : ℝ) ≤ 5 * d.V / 2 :=
      (show (m : ℝ) ≤ (Nat.floor (5 * d.V / 2) : ℝ) by
        exact_mod_cast (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))
    change m ∈ Finset.Icc 0 (Nat.ceil (3 * d.V))
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by
      exact_mod_cast (hhi.trans (by linarith)).trans (Nat.le_ceil (3 * d.V))⟩
  symm
  apply Finset.sum_subset hsub
  intro m hm hn
  have hweight : actualPsiMWeight d m = 0 := by
    by_contra hne
    obtain ⟨hlo, hhi, _⟩ := actualPsiMWeight_support hd m hne
    exact hn (Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩)
  simp [samePsiTerm, s2TermWithM, hweight]

theorem actual_pair_samePsi_eq_raw_inner
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : Key)
    (left right : ℕ → ℕ → ℂ) :
    (∑ t ∈ pairedCarrier d k, samePsiTerm d left right (canonicalIndex t)) =
      ∑ c ∈ rawKeyFamily d k, psiCoefficientInner d c left right := by
  rw [actual_pair_sum_reindex]
  apply Finset.sum_congr rfl
  intro c hc
  unfold psiCoefficientInner
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  apply Finset.sum_congr rfl
  intro n₂ hn₂
  exact paperPsiM_sum_eq_common hd c left right n₁ n₂

theorem nonzero_labelSubset_support (d : MediumAtom) (z : ℝ)
    (small rough : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P]
    (hne : (∑ v ∈ labelSubset d z small rough P, d.gamma2 v.1 * d.gamma3 v.2) ≠ 0) :
    small ∈ dCarrier d z ∧ rough ∈ roughFiber d z small := by
  have hw : ∃ v ∈ labelSubset d z small rough P, d.gamma2 v.1 * d.gamma3 v.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finset.sum_eq_zero (fun v hv => h v hv))
  obtain ⟨v, hv, _⟩ := hw
  have hp := (Finset.mem_filter.mp hv).1
  have hl := (Finset.mem_filter.mp hv).2.1
  have hdw : (small, rough) ∈ dwCarrier d z :=
    Finset.mem_image.mpr ⟨v, hp, hl⟩
  exact ⟨Finset.mem_image.mpr ⟨(small, rough), hdw, rfl⟩,
    Finset.mem_image.mpr ⟨(small, rough), Finset.mem_filter.mpr ⟨hdw, rfl⟩, rfl⟩⟩

theorem keyCoefficients_zero_outside (d : MediumAtom) (x z : ℝ) (k : Key)
    (small rough : ℕ) (h : ¬(small ∈ dCarrier d z ∧ rough ∈ roughFiber d z small)) :
    keyFull d z k small rough = 0 ∧ keyKept d x z k small rough = 0 ∧
      keyTail d x z k small rough = 0 := by
  constructor
  · by_contra hne
    exact h (nonzero_labelSubset_support d z small rough (keyPredicate z k) hne)
  constructor
  · by_contra hne
    exact h (nonzero_labelSubset_support d z small rough
      (fun v => keyPredicate z k v ∧ individualSmoothWithinY x z v) hne)
  · by_contra hne
    exact h (nonzero_labelSubset_support d z small rough
      (fun v => keyPredicate z k v ∧ ¬individualSmoothWithinY x z v) hne)

theorem nativeKeyFamily_subset_raw (d : MediumAtom) (z : ℝ) (k : Key) :
    nativeKeyFamily d z k ⊆ rawKeyFamily d k := by
  intro c hc
  obtain ⟨hc, hd, hr, hs⟩ := Finset.mem_filter.mp hc
  have hq := (Finset.mem_product.mp (Finset.mem_sigma.mp hc).1).1
  exact Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr ⟨hq, hd⟩,
    Finset.mem_product.mpr ⟨hr, hs⟩⟩

theorem keyThreeTailInner_zero_raw_complement (d : MediumAtom) (z : ℝ) (k : Key)
    (c : CoefficientIndex) (hc : c ∈ rawKeyFamily d k)
    (hn : c ∉ nativeKeyFamily d z k) : keyThreeTailInner d d.scale z k c = 0 := by
  have hq := (Finset.mem_product.mp (Finset.mem_sigma.mp hc).1).1
  have hdw := (Finset.mem_product.mp (Finset.mem_sigma.mp hc).1).2
  have hrw := (Finset.mem_product.mp (Finset.mem_sigma.mp hc).2).1
  have hsw := (Finset.mem_product.mp (Finset.mem_sigma.mp hc).2).2
  by_cases hd : c.1.2 ∈ dCarrier d z
  · by_cases hr : c.2.1 ∈ roughFiber d z c.1.2
    · by_cases hs : c.2.2 ∈ roughFiber d z c.1.2
      · exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
          ⟨Finset.mem_product.mpr ⟨hq, hd⟩, Finset.mem_product.mpr ⟨hr, hs⟩⟩,
          hdw, hrw, hsw⟩)).elim
      · obtain ⟨_, hK, hT⟩ := keyCoefficients_zero_outside d d.scale z k c.1.2 c.2.2
          (by simp [hs])
        simp [keyThreeTailInner, psiCoefficientInner, samePsiTerm, s2TermWithM, hK, hT]
    · obtain ⟨_, hK, hT⟩ := keyCoefficients_zero_outside d d.scale z k c.1.2 c.2.1
        (by simp [hr])
      simp [keyThreeTailInner, psiCoefficientInner, samePsiTerm, s2TermWithM, hK, hT]
  · obtain ⟨_, hK, hT⟩ := keyCoefficients_zero_outside d d.scale z k c.1.2 c.2.1
      (by simp [hd])
    simp [keyThreeTailInner, psiCoefficientInner, samePsiTerm, s2TermWithM, hK, hT]

/-- The analytic packet is now identified with the actual source tail,
including its complete q support, m support and individual common-key windows. -/
theorem actual_keyMixedTail_eq_native
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key) :
    keyMixedTailSum d d.scale z k = nativeKeyTail d z k := by
  unfold keyMixedTailSum
  simp only [Finset.sum_add_distrib]
  rw [actual_pair_samePsi_eq_raw_inner hd, actual_pair_samePsi_eq_raw_inner hd,
    actual_pair_samePsi_eq_raw_inner hd]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  change (∑ c ∈ rawKeyFamily d k, keyThreeTailInner d d.scale z k c) = nativeKeyTail d z k
  symm
  exact Finset.sum_subset (nativeKeyFamily_subset_raw d z k)
    (fun c hc hn => keyThreeTailInner_zero_raw_complement d z k c hc hn)

theorem exists_actual_keyMixedTail_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → X ≤ d.scale →
        nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)) →
        ‖keyMixedTailSum d d.scale (roughZ d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C, X, hC, hX, hbound⟩ := exists_nativeKeyTail_arbitrary_log hShiu A hA
  refine ⟨C, X, hC, hX, ?_⟩
  intro B sigma kappa c0 d k hd hx hphysical
  rw [actual_keyMixedTail_eq_native hd]
  exact hbound B sigma kappa c0 d k hd hx hphysical

/-- Original preliminary S2 with BOTH named corrections retained. This
is a bound on its actual receiver full/kept difference, not on a surrogate.
No bound on the two separate gate corrections is assumed or asserted. -/
theorem exists_actual_preliminary_S2_smooth_deletion_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → X ≤ d.scale →
        nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)) →
        |(keyFullRestoredSum d d.scale (roughZ d.scale) k).re -
          (primitiveS2 d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k +
            (otherRoughCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re +
            (singleZeroCorrection d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re)| ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C, X, hC, hX, hbound⟩ := exists_actual_keyMixedTail_arbitrary_log hShiu A hA
  refine ⟨C, X, hC, hX, ?_⟩
  intro B sigma kappa c0 d k hd hx hphysical
  have hz : 0 ≤ roughZ d.scale := Real.rpow_nonneg (by
    dsimp [MediumAtom.scale]
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hV : 0 ≤ d.V := by linarith [hd.2.1]
    positivity) _
  rw [actual_preliminary_S2_receiver_full_identity hd d.scale (roughZ d.scale) hz k,
    add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans (hbound B sigma kappa c0 d k hd hx hphysical)

end
end ImbalancedChen.Part3OriginalS2ActualTailTransfer
