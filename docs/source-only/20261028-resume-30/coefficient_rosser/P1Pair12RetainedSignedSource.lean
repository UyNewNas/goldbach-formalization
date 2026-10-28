import ImbalancedChen.P1Pair12RetainedActualFifthPolicyBound
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
import ImbalancedChen.ChenInitialPrimeSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Nonmultiplicative arithmetic tests of the actual retained tree. The existing
polynomial splice identity only treats products of local prime weights. AP
counts and exact coprime means are not such products. This file proves the
stopped identity again for a terminal test, identifies its unit-weight source
with the literal physical small/rough coefficient, and applies it to policy5.
The parent admits rank six before a replacement acts. No support licence,
Sixth cap, PP estimate, density estimate or numerical gain is postulated.
-/

namespace ImbalancedChen.P1Pair12RetainedSignedSource

noncomputable section
open Classical
open scoped BigOperators

/-- A terminal test may depend on the complete selected word and its sign. -/
def signedTest {α : Type*} (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre : List α) (positive : Bool)
    (mass : ℝ) : List α → ℝ
  | [] => signedTreeCoefficient positive mass * T positive pre
  | p :: ps =>
      signedTest R h T pre positive mass ps +
        if R (!positive) (p :: pre) = true then
          signedTest R h T (p :: pre) (!positive) (mass * h p) ps
        else 0

theorem signedTest_eq_leaves {α : Type*} (R : Bool → List α → Bool)
    (h : α → ℝ) (T : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    signedTest R h T pre positive mass remaining =
      ((firstExitRetainedLeaves R h pre positive mass remaining).map
        (fun leaf => leaf.value * T leaf.positive leaf.selected)).sum := by
  induction remaining generalizing pre positive mass with
  | nil => simp [signedTest, firstExitRetainedLeaves, FirstExitLeaf.value]
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [signedTest, firstExitRetainedLeaves, if_pos hr,
          List.map_append, List.sum_append]
        rw [ih, ih]
      · simp only [signedTest, firstExitRetainedLeaves, if_neg hr,
          List.append_nil, add_zero]
        exact ih pre positive mass

/-- Subtraction changes only the terminal test, never the retained policy,
leaf multiplicities, signs or small-prime choice. -/
theorem signedTest_sub {α : Type*} (R : Bool → List α → Bool)
    (h : α → ℝ) (C M : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    signedTest R h (fun s p => C s p - M s p) pre positive mass remaining =
      signedTest R h C pre positive mass remaining -
        signedTest R h M pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp only [signedTest]; ring
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [signedTest, if_pos hr]
        rw [ih, ih]
        ring
      · simp only [signedTest, if_neg hr, add_zero]
        exact ih pre positive mass

/-- Unit local weights reindex an arbitrary arithmetic test to the same
fixed Mobius lookup. This is not restricted to multiplicative tests. -/
theorem signedTest_eq_fixed_moduli_test
    (R : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (F : Bool → ℕ → ℝ) :
    signedTest R (fun _ => 1) (fun s pre => F s pre.prod) [] true 1 carrier =
      ∑ d ∈ firstExitRetainedModuli R carrier,
        (firstExitRetainedCoefficient R carrier d : ℝ) *
          F (decide (0 ≤ (firstExitRetainedCoefficient R carrier d : ℝ))) d := by
  rw [signedTest_eq_leaves]
  let leaves := firstExitRootLeaves R (fun _ => 1) carrier
  let weight : ℕ → ℝ := fun d =>
    (firstExitRetainedCoefficient R carrier d : ℝ) *
      F (decide (0 ≤ (firstExitRetainedCoefficient R carrier d : ℝ))) d
  have hvalues :
      leaves.map (fun leaf => leaf.value * F leaf.positive leaf.selected.prod) =
        (leaves.map (fun leaf => leaf.selected.prod)).map weight := by
    rw [List.map_map]
    apply List.map_congr_left
    intro leaf hleaf
    have hm : leaf.mass = 1 := by
      have hm := mem_firstExitRootLeaves_mass_eq_selected_prod
        R (fun _ => 1) carrier leaf hleaf
      simpa using hm
    have hd : leaf.selected.prod ∈ firstExitRetainedModuli R carrier :=
      (mem_firstExitRetainedModuli R carrier _).mpr ⟨leaf, hleaf, rfl⟩
    have hc : (firstExitRetainedCoefficient R carrier leaf.selected.prod : ℝ) =
        leaf.value := by
      rw [firstExitRetainedCoefficient, if_pos hd]
      have hv := mem_firstExitRootLeaves_value_eq_moebius_mul_selected_prod
        R (fun _ => 1) carrier hnodup hprime leaf hleaf
      simpa using hv.symm
    have hsign :
        decide (0 ≤ (firstExitRetainedCoefficient R carrier leaf.selected.prod : ℝ)) =
          leaf.positive := by
      rw [hc]
      cases hp : leaf.positive <;>
        simp [FirstExitLeaf.value, signedTreeCoefficient, hp, hm]
    change leaf.value * F leaf.positive leaf.selected.prod =
      (firstExitRetainedCoefficient R carrier leaf.selected.prod : ℝ) *
        F (decide (0 ≤ (firstExitRetainedCoefficient R carrier leaf.selected.prod : ℝ)))
          leaf.selected.prod
    rw [hsign, hc]
  change (leaves.map (fun leaf => leaf.value * F leaf.positive leaf.selected.prod)).sum = _
  rw [hvalues]
  exact (List.sum_toFinset weight
    (firstExitRootLeaves_selectedProd_map_nodup R (fun _ => 1)
      carrier hnodup hprime)).symm

/-- The sign-sensitive actual small factor on the full physical modulus. -/
def attachedLeafTest (N cap mark : ℕ) (w L : ℝ) (G : ℕ → ℝ)
    (positive : Bool) (pre : List ℕ) : ℝ :=
  ∑ a ∈ actualSmallRosserSupport N cap w,
    (if positive then actualSmallRosserPlus N cap w L a
     else actualSmallRosserMinus N cap w L a) * G (mark * (a * pre.prod))

/-- Exact physical-rho identification for any even-retaining policy. The
same result applies to a later sixth splice provided its replacement retains
even nodes. No prime distribution assumption occurs in this identity. -/
theorem physical_test_eq_signedTest
    (R : Bool → List ℕ → Bool) (heven : ∀ pre, R true pre = true)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ actualSmallRoughModuli (R false) N cap w z,
      actualSmallRoughRho (R false) N cap w z L q * G (mark * q)) =
      signedTest R (fun _ => 1) (attachedLeafTest N cap mark w L G)
        [] true 1 (roughPrimeUniverse N cap w z) := by
  let S := firstExitRetainedModuli R (roughPrimeUniverse N cap w z)
  let c : ℕ → ℝ := fun d =>
    (firstExitRetainedCoefficient R (roughPrimeUniverse N cap w z) d : ℝ)
  have hs : fixedRoughSupport (R false) N cap w z = S :=
    UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
      R heven N cap w z
  have hr : ∀ d ∈ S, RoughPrimeSupportedAt w d := by
    intro d hd
    rw [← hs] at hd
    exact fixedRoughSupport_roughPrimeSupportedAt (R false) N cap w z hd
  rw [UpperPolicyFiniteBridge.actualSmallRoughRho_eq_firstExitAttachment R heven]
  change (∑ q ∈ smallRoughModuli (actualSmallRosserSupport N cap w)
      (fixedRoughSupport (R false) N cap w z),
      smallRoughRho (actualSmallRosserSupport N cap w) S c
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) q *
          G (mark * q)) = _
  rw [hs, sum_smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd) hr]
  unfold smallRoughPairs
  rw [Finset.sum_product, Finset.sum_comm]
  rw [show attachedLeafTest N cap mark w L G =
    (fun s pre =>
      (fun b d => ∑ a ∈ actualSmallRosserSupport N cap w,
        (if b then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) * G (mark * (a * d))) s pre.prod)
      from rfl]
  rw [signedTest_eq_fixed_moduli_test R _ (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [smallRoughPairCoefficient, signAttachedCoefficient, decide_eq_true_eq]
  by_cases hc : 0 ≤ c d <;> simp [hc, c] <;> ring

/-- Stopped arithmetic source: exhausted branches below rank k are common
to the old and new policies and will cancel, even for an AP count test. -/
def stoppedTest {α : Type*} (k : ℕ) (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre : List α) (positive : Bool)
    (mass : ℝ) : List α → ℝ
  | [] => if k ≤ pre.length then 0 else signedTreeCoefficient positive mass * T positive pre
  | p :: ps => if k ≤ pre.length then 0 else
      stoppedTest k R h T pre positive mass ps +
        if R (!positive) (p :: pre) = true then
          stoppedTest k R h T (p :: pre) (!positive) (mass * h p) ps
        else 0

theorem signedTest_splice_after_rank {α : Type*} (k : ℕ)
    (parent fresh : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α) (positive : Bool)
    (mass : ℝ) (hk : k ≤ pre.length) :
    signedTest (firstExitDepthSplicePolicy k parent fresh) h T pre positive mass remaining =
      signedTest fresh h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hnext : k < (p :: pre).length := by
        simpa only [List.length_cons] using Nat.lt_succ_of_le hk
      simp only [signedTest, firstExitDepthSplicePolicy,
        if_neg (Nat.not_le_of_gt hnext)]
      rw [ih pre positive mass hk,
        ih (p :: pre) (!positive) (mass * h p) hnext.le]

theorem signedTest_splice_eq_stopped_add_frontier {α : Type*} (k : ℕ)
    (parent fresh : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    signedTest (firstExitDepthSplicePolicy k parent fresh) h T pre positive mass remaining =
      stoppedTest k parent h T pre positive mass remaining +
        ((firstExitDepthFrontier k parent h pre positive mass remaining).map
          (fun s => signedTest fresh h T s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length <;>
        simp [signedTest, stoppedTest, firstExitDepthFrontier, hk]
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · rw [signedTest_splice_after_rank k parent fresh h T pre (p :: ps) positive mass hk]
        simp only [stoppedTest, firstExitDepthFrontier, if_pos hk,
          List.map_singleton, List.sum_singleton, zero_add]
      · have hnext : (p :: pre).length ≤ k := by
          simpa only [List.length_cons] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hk)
        have htest : firstExitDepthSplicePolicy k parent fresh (!positive) (p :: pre) =
            parent (!positive) (p :: pre) := by
          simp only [firstExitDepthSplicePolicy, if_pos hnext]
        simp only [signedTest, htest, stoppedTest, firstExitDepthFrontier, if_neg hk]
        by_cases hr : parent (!positive) (p :: pre) = true
        · rw [if_pos hr, if_pos hr, if_pos hr, List.map_append, List.sum_append,
            ih pre positive mass, ih (p :: pre) (!positive) (mass * h p)]
          ring
        · simp only [if_neg hr, add_zero, List.append_nil]
          exact ih pre positive mass

theorem signedTest_splice_sub_eq_frontier {α : Type*} (k : ℕ)
    (parent fresh : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    signedTest (firstExitDepthSplicePolicy k parent fresh) h T pre positive mass remaining -
        signedTest parent h T pre positive mass remaining =
      ((firstExitDepthFrontier k parent h pre positive mass remaining).map
        (fun s => signedTest fresh h T s.selectedPrefix s.positive s.mass s.remaining -
          signedTest parent h T s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  have hparent := signedTest_splice_eq_stopped_add_frontier k parent parent h T
    pre remaining positive mass
  rw [firstExitDepthSplicePolicy_self] at hparent
  rw [signedTest_splice_eq_stopped_add_frontier, hparent, add_sub_add_left_eq_sub]
  generalize firstExitDepthFrontier k parent h pre positive mass remaining = states
  induction states with
  | nil => simp
  | cons s states ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

/-- Literal full-modulus exact coprime mean, with the original prime prefix. -/
def exactCoprimeMean (N q : ℕ) : ℝ :=
  (((chenPrimePrefix N).filter (fun P => P.Coprime q)).card : ℝ) / (Nat.totient q : ℝ)

section ActualFifth
open P1OriginalVariableFifthContinuation P2OriginalFourthCapProducerInterface
open Certificates.P2OriginalSixthElevenLogSemantics
open P5Z.Pair12RetainedActualFifthPolicyBound

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- The actual fifth physical coefficient has a same-signed leaf source
for both the original AP count and its full-modulus exact coprime mean. -/
theorem actual_fifth_same_rho_PP_source (N cap mark : ℕ) (w z L : ℝ) :
    let R := policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5
    (∑ q ∈ actualSmallRoughModuli (R false) N cap w z,
      actualSmallRoughRho (R false) N cap w z L q *
        (chenPrimeAPCount N N (mark * q) - exactCoprimeMean N (mark * q))) =
      signedTest R (fun _ => 1)
        (fun s pre =>
          attachedLeafTest N cap mark w L (chenPrimeAPCount N N) s pre -
          attachedLeafTest N cap mark w L (exactCoprimeMean N) s pre)
        [] true 1 (roughPrimeUniverse N cap w z) := by
  dsimp only
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [physical_test_eq_signedTest _
      (P4AOriginalVariableFifthPhysicalLedger.fifth_even e chi m omega rows4 licensed4 J5 rows5 (N : ℝ)),
    physical_test_eq_signedTest _
      (P4AOriginalVariableFifthPhysicalLedger.fifth_even e chi m omega rows4 licensed4 J5 rows5 (N : ℝ))]
  exact (signedTest_sub _ _ _ _ [] _ true 1).symm

/-- Exact change of the physical same-rho source below the actual retained
sixth frontier. This identity preserves the parent's rank-six admission test
and all branches exhausted before it. It applies without alteration to AP
counts, exact coprime means, or their signed difference by choosing G. -/
theorem actual_fifth_retained_six_physical_change
    (fresh : Bool → List ℕ → Bool) (hfresh : ∀ pre, fresh true pre = true)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    let R := policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5
    let Rnew := firstExitDepthSplicePolicy 6 R fresh
    (∑ q ∈ actualSmallRoughModuli (Rnew false) N cap w z,
      actualSmallRoughRho (Rnew false) N cap w z L q * G (mark * q)) -
      (∑ q ∈ actualSmallRoughModuli (R false) N cap w z,
        actualSmallRoughRho (R false) N cap w z L q * G (mark * q)) =
      ((firstExitDepthFrontier 6 R (fun _ : ℕ => 1) [] true 1
          (roughPrimeUniverse N cap w z)).map
        (fun state =>
          signedTest fresh (fun _ => 1) (attachedLeafTest N cap mark w L G)
              state.selectedPrefix state.positive state.mass state.remaining -
            signedTest R (fun _ => 1) (attachedLeafTest N cap mark w L G)
              state.selectedPrefix state.positive state.mass state.remaining)).sum := by
  dsimp only
  have heven := P4AOriginalVariableFifthPhysicalLedger.fifth_even
    e chi m omega rows4 licensed4 J5 rows5 (N : ℝ)
  have hnew := UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained
    6 (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) fresh heven hfresh
  rw [physical_test_eq_signedTest _ hnew,
    physical_test_eq_signedTest _ heven]
  exact signedTest_splice_sub_eq_frontier 6
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) fresh
    (fun _ => 1) (attachedLeafTest N cap mark w L G)
    [] (roughPrimeUniverse N cap w z) true 1

/-- Every arithmetic-source rank-six state uses the very fifth parent
bounded in PhaseD. Its frontier uses unit weights; the cap proof needs only
the actual selected length, so no artificial reciprocal-density premise is
added to the AP-count source. -/
theorem actual_fifth_arithmetic_frontier_parent_bound
    (N cap : ℕ) (w z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 6
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
      (fun _ : ℕ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (he : 0 ≤ e)
    (hc : PhysicalCell .pair12_fixed (pair12Physical (N : ℝ) state.selectedPrefix))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega (N : ℝ)
      (rosserAncestor 3 state.selectedPrefix))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (hmask : ∀ r ∈ rows4, licensed4 r →
      (∑ i ∈ r.selected, (pair12Physical (N : ℝ) state.selectedPrefix)
        (i.castLE (by omega : 4 ≤ 6))) =
          subsetSum r.mask (pair12Physical (N : ℝ) state.selectedPrefix)) :
    pair12ActualFifthExponent e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5 state.selectedPrefix ≤
      oldCap .pair12_fixed (pair12Physical (N : ℝ) state.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 6
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    (fun _ : ℕ => 1) [] (roughPrimeUniverse N cap w z) true 1
    (by simp) state hstate
  exact pair12_actual_fifth_le_oldCap e chi m omega (N : ℝ)
    rows4 licensed4 J5 rows5 state.selectedPrefix hlen he hc hs hgeometry hmask

end ActualFifth
end
end ImbalancedChen.P1Pair12RetainedSignedSource
