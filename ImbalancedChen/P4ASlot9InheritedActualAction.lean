import ImbalancedChen.P2OriginalAscending34CapDictionary
import ImbalancedChen.P4ASameRhoSignedMassLedger
import ImbalancedChen.CurrentUpperEighteenBudget

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Original all22 saving 9 is the ascending mask34 sixth-node increment,
M=(1+t2+t6)/2-10^-6, compared conservatively with R=max(R0,D33).
The frozen source only gives current >= lambda5, not current >= R0.
Here the required lower residual bound is derived from the *actual*
retained fifth history H5<current. This permits buffered current<R0.

The local action preserves the actual current cap off its strict licensed
rows and freezes at rank six. The exact physical charge below uses an
arbitrary fixed presieve w, including w>0, and keeps the same signed and
absolute rough masses. No unpresieved residual formula is applied at w>0.

This is a local original-formula construction. Identification with the
two original pattern1371 cells, the implemented prior sixth policy, its
complete common ancestor refinement and the 621-simplex rational lower
enclosure remain OPEN. The all22 physical density/currentK claim remains
OPEN. The exponent inflation lemma is not a global support theorem.
-/

namespace ImbalancedChen.P4ASlot9InheritedActualActionSourceOnly

noncomputable section
open scoped Classical BigOperators
open P2OriginalAscending34CapDictionary

theorem slot9_literal_endpoint :
    currentUpperEighteenGains 8 = (306737545112876482463163 / 2^96 : ℝ) := rfl

def fifthHistory (t : Fin 6 → ℝ) : ℝ :=
  t 0 + t 1 + t 2 + t 3 + 3 * t 4

theorem fifthHistory_residual (t : Fin 6 → ℝ) :
    fifthHistory t - S t = 2 * t 4 - t 5 := by
  simp [fifthHistory, S, Fin.sum_univ_succ]
  <;> ring

/-- These are local, primitive history/cap guards; no gain is a field. -/
def actionRows (t : Fin 6 → ℝ) (current : ℝ) : Prop :=
  SourceGuard t ∧ fifthHistory t < current ∧ current ≤ comparisonR t

/-- H5<current supplies the lower bound even when current<R0. -/
theorem inherited_residual_range {t : Fin 6 → ℝ} {current : ℝ}
    (h : actionRows t current) :
    0 < t 5 ∧ t 5 < current - S t ∧ current - S t ≤ 3 * t 5 ∧
      t 5 < M t - S t ∧ M t - S t ≤ 3 * t 5 := by
  have horder : StrictAnti t := h.1.2.1.1
  have h54 : t 5 < t 4 := horder (by decide : (4 : Fin 6) < 5)
  have hhist := fifthHistory_residual t
  have hr := h.1.1
  refine ⟨hr.1, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [h54, hhist, h.2.1, h.2.2, hr.2.2.1, hr.2.2.2]

/-- Conservative same-node comparison, requiring no current>=R0 premise. -/
theorem comparison_gain_le_inherited {t : Fin 6 → ℝ} {current : ℝ}
    (h : actionRows t current) :
    sourceGain (comparisonR t) (M t) t ≤ sourceGain current (M t) t := by
  have hp := inherited_residual_range h
  have hc : 0 < current - S t := hp.1.trans hp.2.1
  have hR : 0 < comparisonR t - S t :=
    hc.trans_le (sub_le_sub_right h.2.2 _)
  have hM : 0 < M t - S t := hp.1.trans hp.2.2.2.1
  have hi := one_div_le_one_div_of_le hc (sub_le_sub_right h.2.2 (S t))
  have hfour : 4 / (comparisonR t - S t) ≤ 4 / (current - S t) := by
    convert mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  rw [sourceGain_eq_difference _ _ t hR hM,
    sourceGain_eq_difference _ _ t hc hM]
  exact sub_le_sub_right hfour _

/-- The literal actual quotient residual, with one threshold before N.
No inherited buffered cap is replaced by R0 in this theorem. -/
theorem exists_actual_inherited_increment_threshold
    {t : Fin 6 → ℝ} {current : ℝ} (h : actionRows t current)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y : ℝ, 0 < P → 0 < y →
        Real.log P / Real.log (N : ℝ) = S t →
        Real.log y / Real.log (N : ℝ) = t 5 →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          sourceGain (comparisonR t) (M t) t - epsilon <
            (actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ current / P) -
              actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ M t / P)) *
                Real.log (N : ℝ) / singularSeries N := by
  let T : Set (ℝ × ℝ) := {(current - S t, t 5)} ∪ {(M t - S t, t 5)}
  have hT : IsCompact T := isCompact_singleton.union isCompact_singleton
  have hp := inherited_residual_range h
  have hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2 := by
    intro p hpT
    rcases hpT with hpT | hpT
    · have heq := Set.mem_singleton_iff.mp hpT
      subst p
      exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    · have heq := Set.mem_singleton_iff.mp hpT
      subst p
      exact ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold
      T hT hparam epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y hP hy hlogP hlogy cap hcap
  have hOld : actualRosserQuotientParameters (N : ℝ) P y current ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inl (Set.mem_singleton _)
  have hNew : actualRosserQuotientParameters (N : ℝ) P y (M t) ∈ T := by
    simp only [actualRosserQuotientParameters, hlogP, hlogy]
    exact Or.inr (Set.mem_singleton _)
  have hb := abs_lt.mp (hbound N hN hEven P y current (M t) hP hy hOld hNew cap hcap)
  rw [hlogP] at hb
  have hcomp := comparison_gain_le_inherited h
  unfold sourceGain at hcomp ⊢
  linarith only [hb.1, hcomp]

/-- The actual existing sixth exponent is frozen at its sixth ancestor. -/
def inheritedExponent (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  lambda6 (rosserAncestor 6 history)

def nextExponent (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 6 history
  if actionRows t (inheritedExponent lambda6 history) then M t
  else inheritedExponent lambda6 history

def oldLevel (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  N ^ inheritedExponent lambda6 history

def nextLevel (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  N ^ nextExponent N lambda6 history

theorem nextExponent_outside (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ)
    (h : ¬ actionRows (primeHistoryLogCoordinates N 6 history)
      (inheritedExponent lambda6 history)) :
    nextExponent N lambda6 history = inheritedExponent lambda6 history := by
  simp only [nextExponent, if_neg h]

theorem inheritedExponent_le_next (N : ℝ) (lambda6 : List ℕ → ℝ)
    (history : List ℕ) :
    inheritedExponent lambda6 history ≤ nextExponent N lambda6 history := by
  unfold nextExponent
  dsimp only
  split_ifs with h
  · exact h.2.2.trans h.1.1.2.2.1.le
  · exact le_rfl

theorem oldLevel_le_nextLevel (N : ℝ) (hN : 1 ≤ N)
    (lambda6 : List ℕ → ℝ) (history : List ℕ) :
    oldLevel N lambda6 history ≤ nextLevel N lambda6 history := by
  exact Real.rpow_le_rpow_of_exponent_le hN
    (inheritedExponent_le_next N lambda6 history)

theorem nextLevel_on_rows (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ)
    (h : actionRows (primeHistoryLogCoordinates N 6 history)
      (inheritedExponent lambda6 history)) :
    nextLevel N lambda6 history = sourceLevel N history := by
  simp only [nextLevel, nextExponent, if_pos h, sourceLevel]

/-- The proposed action satisfies both literal natural-history square
families on its active source rows, rather than only a cap inequality. -/
theorem nextLevel_actual_square_gates (N : ℝ) (hN : 1 < N)
    (lambda6 : List ℕ → ℝ) (history : List ℕ) (hlen : history.length = 6)
    (hpos : ∀ p ∈ history, 0 < p)
    (h : actionRows (primeHistoryLogCoordinates N 6 history)
      (inheritedExponent lambda6 history)) :
    (∀ i, ((∏ k ∈ Finset.univ.filter (fun k => k < i),
        primeHistoryTuple 6 history k : ℕ) : ℝ) *
      (primeHistoryTuple 6 history i : ℝ) ^ 2 < nextLevel N lambda6 history) ∧
    (∀ i ∉ mask34, ((∏ k ∈ mask34, primeHistoryTuple 6 history k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k => k < i ∧ k ∉ mask34),
        primeHistoryTuple 6 history k : ℕ) : ℝ) *
      (primeHistoryTuple 6 history i : ℝ) ^ 2 < nextLevel N lambda6 history) := by
  rw [nextLevel_on_rows N lambda6 history h]
  exact sourceLevel_actual_square_gates N hN history hlen hpos h.1

/-- The new cap has the literal mask34 license, hence is below 153/256. -/
theorem active_cap_lt_original_root {t : Fin 6 → ℝ} {current : ℝ}
    (h : actionRows t current) : M t < (299 / 500 : ℝ) := by
  have hl := (sourceGuard_support_license t h.1).2.2.2
  have hb := VariableEnvelope.v_le_cap (∑ i ∈ mask34, t i)
  have hm := hl.trans_le hb
  dsimp only [VariableEnvelope.cap] at hm
  linarith only [hm]

theorem nextExponent_le_original_root (N : ℝ) (lambda6 : List ℕ → ℝ)
    (history : List ℕ) (hold : inheritedExponent lambda6 history ≤ 299 / 500) :
    nextExponent N lambda6 history ≤ 299 / 500 := by
  unfold nextExponent
  dsimp only
  split_ifs with h
  · exact (active_cap_lt_original_root h).le
  · exact hold

/-- Original 599/1000 binding after at most 1/1000 exponent inflation.
Enumeration support and nonzero-coefficient support are not identified here. -/
theorem nextExponent_add_inflation_le_original_theta
    (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) (delta : ℝ)
    (hold : inheritedExponent lambda6 history ≤ 299 / 500)
    (hdelta : delta ≤ 1 / 1000) :
    nextExponent N lambda6 history + delta ≤ 599 / 1000 := by
  linarith only [nextExponent_le_original_root N lambda6 history hold, hdelta]

def oldContinuation (N : ℝ) (lambda6 : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  frozenParityRosserPolicy false 6 (oldLevel N lambda6)

def nextContinuation (N : ℝ) (lambda6 : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  frozenParityRosserPolicy false 6 (nextLevel N lambda6)

def oldPolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 parent (oldContinuation N lambda6)

def nextPolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 parent (nextContinuation N lambda6)

/-- Every actual ancestor decision through the selected sixth node stays. -/
theorem nextPolicy_through_six (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) (positive : Bool) (history : List ℕ)
    (hlen : history.length ≤ 6) :
    nextPolicy N lambda6 parent positive history = parent positive history := by
  simp only [nextPolicy, firstExitDepthSplicePolicy, if_pos hlen]

theorem nextPolicy_after_six (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) (positive : Bool) (history : List ℕ)
    (hlen : 6 < history.length) :
    nextPolicy N lambda6 parent positive history =
      ordinaryParityRosserPolicy false
        (nextLevel N lambda6 (rosserAncestor 6 history)) positive history := by
  simp only [nextPolicy, nextContinuation, firstExitDepthSplicePolicy,
    if_neg (by omega : ¬history.length ≤ 6), frozenParityRosserPolicy,
    ancestorFrozenPolicy]

theorem oldPolicy_even (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) (hparent : ∀ pre, parent true pre = true)
    (pre : List ℕ) : oldPolicy N lambda6 parent true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    hparent (fun q => frozenParityRosserPolicy_upper_even 6 _ q) pre

theorem nextPolicy_even (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) (hparent : ∀ pre, parent true pre = true)
    (pre : List ℕ) : nextPolicy N lambda6 parent true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    hparent (fun q => frozenParityRosserPolicy_upper_even 6 _ q) pre

/-- Actual stopped continuations, with the exact w-truncated carrier.
Short branches are absent from this frontier and cancel as terminal terms. -/
def signedFrontierCharge (N cap : ℕ) (w z : ℝ)
    (lambda6 : List ℕ → ℝ) (parent : Bool → List ℕ → Bool) : ℝ :=
  ((firstExitDepthFrontier 6 parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap w z)).map (fun state =>
      firstExitRetainedPolynomial (oldContinuation (N : ℝ) lambda6)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
          state.positive state.mass state.remaining -
        firstExitRetainedPolynomial (nextContinuation (N : ℝ) lambda6)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
          state.positive state.mass state.remaining)).sum

theorem signed_frontier_charge (N cap : ℕ) (w z : ℝ)
    (lambda6 : List ℕ → ℝ) (parent : Bool → List ℕ → Bool) :
    firstExitRetainedPolynomial (oldPolicy (N : ℝ) lambda6 parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) -
      firstExitRetainedPolynomial (nextPolicy (N : ℝ) lambda6 parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) =
      signedFrontierCharge N cap w z lambda6 parent := by
  unfold oldPolicy nextPolicy signedFrontierCharge
  rw [firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier,
    firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier,
    add_sub_add_left_eq_sub]
  generalize firstExitDepthFrontier 6 parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap w z) = states
  induction states with
  | nil => simp
  | cons state states ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

/-- Literal same-rho charge at fixed w (in particular any fixed w>0).
The absolute-mass difference is retained with its actual sign. -/
theorem physical_frontier_charge (N cap : ℕ) (w z L : ℝ)
    (lambda6 : List ℕ → ℝ) (parent : Bool → List ℕ → Bool)
    (hparent : ∀ pre, parent true pre = true) :
    let old := oldPolicy (N : ℝ) lambda6 parent false
    let fresh := nextPolicy (N : ℝ) lambda6 parent false
    let lo := reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserMinus N cap w L)
    let hi := reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserPlus N cap w L)
    physicalDensitySum (actualSmallRoughModuli old N cap w z)
        (actualSmallRoughRho old N cap w z L) -
      physicalDensitySum (actualSmallRoughModuli fresh N cap w z)
        (actualSmallRoughRho fresh N cap w z L) =
      ((hi + lo) / 2) * signedFrontierCharge N cap w z lambda6 parent +
        ((hi - lo) / 2) *
          (reciprocalTotientDensity (fixedRoughSupport old N cap w z)
              (fun d => |fixedRoughCoefficient old N cap w z d|) -
            reciprocalTotientDensity (fixedRoughSupport fresh N cap w z)
              (fun d => |fixedRoughCoefficient fresh N cap w z d|)) := by
  dsimp only
  have hpair := P4ASameRhoSignedMassLedger.actual_pair_attachment_density_eq_midpoint_ledger
    (oldPolicy (N : ℝ) lambda6 parent false)
    (nextPolicy (N : ℝ) lambda6 parent false) N cap w z L
  dsimp only at hpair
  have hOld :=
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      (oldPolicy (N : ℝ) lambda6 parent)
      (oldPolicy_even (N : ℝ) lambda6 parent hparent) N cap w z
  have hNew :=
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      (nextPolicy (N : ℝ) lambda6 parent)
      (nextPolicy_even (N : ℝ) lambda6 parent hparent) N cap w z
  rw [← hOld, ← hNew, signed_frontier_charge N cap w z lambda6 parent] at hpair
  exact hpair

end
end ImbalancedChen.P4ASlot9InheritedActualActionSourceOnly
