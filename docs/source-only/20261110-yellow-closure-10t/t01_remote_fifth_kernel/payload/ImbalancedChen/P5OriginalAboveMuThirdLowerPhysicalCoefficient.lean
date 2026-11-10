import ImbalancedChen.HistoricalThirdCoarsePolicy
import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.ActualUpperPolicyFiniteBridge
import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.ActualFrozenFrontierDensity
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two above-mu fallback actions are written on the literal original
firstStop/T3 parent. The second action selects p2 on its open rank-two
region; the third selects p2*p3 on the disjoint open rank-three region.
Their old first cube, all initial full squares, and the extra selected
remaining square follow from v(x)>3x. A depth-two then depth-three splice
keeps the earlier decisions and inherits the old policy outside each
action. The second splice may restore later rank-three nodes; the third
splice retains the old rank-three admission before changing its residual.

This is an ideal, pointwise policy with the physical caps N^v(y) and
N^v(y+z). The third selected-pair branch has an ordinary LOWER residual
because removing its odd rank-three prefix reverses the parity of the
global ordinary UPPER policy. Its full even ranks still bypass, while
the next odd full rank is tested. Therefore the actual odd-first-exit
attachedUpperCoefficient remains the same global signed coefficient.
The paper's common finite compact approximation and its
witness-restricted pre-existing fourth/fifth/sixth actions are separate
implementation dependencies. The auxiliary PP covering exponent is never
used as a physical cap. No density or K assertion occurs here.
-/

namespace ImbalancedChen.P5OriginalAboveMuThirdLowerPhysicalCoefficient

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

def rho : ℝ := 19 / 96
def secondMask : Finset (Fin 2) := {1}
def thirdMask : Finset (Fin 3) := {1, 2}

def SecondRegion (x y : ℝ) : Prop :=
  mu < x ∧ x < rho ∧ 2 * v x - 1 < y ∧ y < x

def ThirdRegion (x y z : ℝ) : Prop :=
  mu < x ∧ x < rho ∧ 0 < z ∧ z < y ∧
    2 * v x - 1 < y + z ∧ y + z < x ∧
    5 / 9 ≤ 2 * z / (y + z) ∧ 2 * z / (y + z) ≤ 1 ∧
    z ≥ 5 / 96 ∧ y < 3 / 16

theorem above_mu_old_cap_gt_cube {x : ℝ}
    (hx : mu < x) (hr : x < rho) : 3 * x < v x := by
  rw [v_eq_C hx.le]
  dsimp [C, rho] at *
  linarith

/-- The first cube is tested at the original initial level. The
firstStop endpoint, with its four-error buffer, pays this separate gate. -/
theorem original_first_cube_from_stop {e x : ℝ}
    (he : 0 ≤ e) (hstop : x ≤ extendedFirstStop - 4 * e) :
    3 * x < HistoricalThirdCoarse.initial e := by
  dsimp [HistoricalThirdCoarse.initial, extendedFirstStop,
    extendedDistributionCap] at *
  linarith

theorem new_cap_gt_old {x t : ℝ}
    (hx : mu < x) (hlo : 2 * v x - 1 < t) (hhi : t < x) :
    v x < v t := by
  have hold : v x = C x := v_eq_C hx.le
  have hA : C x < A t := by
    dsimp [A]
    rw [hold] at hlo
    linarith
  have hC : C x < C t := by
    dsimp [C]
    linarith
  rw [hold, v_eq_min]
  exact lt_min hA hC

/-- Exactly the two full initial squares and the selected-p2 remaining
square. The first cube is retained from the original firstStop parent. -/
theorem second_initial_physical_gates {x y : ℝ} (h : SecondRegion x y) :
    2 * x < v x ∧ x + 2 * y < v x ∧
      2 * x + y < v x ∧ v x < v y := by
  obtain ⟨hx, hr, hlo, hy⟩ := h
  have hcube := above_mu_old_cap_gt_cube hx hr
  refine ⟨?_, ?_, ?_, new_cap_gt_old hx hlo hy⟩ <;> linarith

/-- Mask {p2,p3}: all first three full squares, the old third cube,
and the only extra selected-complement square at p1 lie below v(x).
Thus they also lie below the new physical cap v(y+z). -/
theorem third_initial_physical_gates {x y z : ℝ} (h : ThirdRegion x y z) :
    2 * x < v x ∧ x + 2 * y < v x ∧
      x + y + 2 * z < v x ∧ x + y + 3 * z < v x ∧
      2 * x + y + z < v x ∧ v x < v (y + z) := by
  obtain ⟨hx, hr, hz, hzy, hlo, hsum, _hwlo, _hwhi, _hzcut, _hycut⟩ := h
  have hcube := above_mu_old_cap_gt_cube hx hr
  have hnew := new_cap_gt_old hx hlo hsum
  refine ⟨?_, ?_, ?_, ?_, ?_, hnew⟩ <;> linarith

theorem above_mu_regions_disjoint {x y z : ℝ}
    (h2 : SecondRegion x y) (h3 : ThirdRegion x y z) : False := by
  have h2y : (3 / 16 : ℝ) < y := by
    have hx := h2.1
    have hr := h2.2.1
    have hlow := h2.2.2.1
    rw [v_eq_C hx.le] at hlow
    dsimp [C, rho] at *
    linarith
  rcases h3 with ⟨_, _, _, _, _, _, _, _, _, hycut⟩
  linarith

/-- The old first cube, every initial full square, and the extra
selected-complement square are all tested at the actual initial level.
The ideal replacement's later physical level is distinct from it. -/
theorem second_original_initial_gates {e x y : ℝ}
    (he : 0 ≤ e) (hstop : x ≤ extendedFirstStop - 4 * e)
    (h : SecondRegion x y) :
    3 * x < HistoricalThirdCoarse.initial e ∧
      2 * x < HistoricalThirdCoarse.initial e ∧
      x + 2 * y < HistoricalThirdCoarse.initial e ∧
      2 * x + y < HistoricalThirdCoarse.initial e := by
  have hcube := original_first_cube_from_stop he hstop
  obtain ⟨hx, _, _, hy⟩ := h
  refine ⟨hcube, ?_, ?_, ?_⟩ <;> linarith

theorem third_original_initial_gates {e x y z : ℝ}
    (he : 0 ≤ e) (hstop : x ≤ extendedFirstStop - 4 * e)
    (h : ThirdRegion x y z) :
    3 * x < HistoricalThirdCoarse.initial e ∧
      2 * x < HistoricalThirdCoarse.initial e ∧
      x + 2 * y < HistoricalThirdCoarse.initial e ∧
      x + y + 2 * z < HistoricalThirdCoarse.initial e ∧
      x + y + 3 * z < HistoricalThirdCoarse.initial e ∧
      2 * x + y + z < HistoricalThirdCoarse.initial e := by
  have hcube := original_first_cube_from_stop he hstop
  obtain ⟨hx, _, hz, hzy, _, hsum, _, _, _, _⟩ := h
  refine ⟨hcube, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

def secondGuard (N : ℝ) (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre)
  SecondRegion (t 0) (t 1)

def thirdGuard (N : ℝ) (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
  ThirdRegion (t 0) (t 1) (t 2)

theorem thirdGuard_later_history (N : ℝ) (later history : List ℕ)
    (h : 3 ≤ history.length) :
    thirdGuard N (later ++ history) ↔ thirdGuard N history := by
  simp only [thirdGuard, rosserAncestor_append 3 later history h]

def oldPolicy (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    Bool → List ℕ → Bool :=
  HistoricalThirdCoarse.policy e chi m omega N

/-- At a rank-two hit the later ordinary upper residual uses the
selected-p2 cap. Else it is exactly the old T3 decision. -/
def secondReplacement (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    Bool → List ℕ → Bool :=
  fun positive pre =>
    if secondGuard N pre then
      ordinaryParityRosserPolicy false
        (N ^ v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)) positive pre
    else oldPolicy e chi m omega N positive pre

def secondPolicy (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 2 (oldPolicy e chi m omega N)
    (secondReplacement e chi m omega N)

def thirdQ (N : ℝ) (pre : List ℕ) : ℝ :=
  N ^ v (primeHistoryLogCoordinates N 3 pre 1 +
    primeHistoryLogCoordinates N 3 pre 2)

/-- At a rank-three selected-pair hit, freeze the new physical level.
The global upper policy becomes a lower residual after the odd prefix. -/
def thirdReplacement (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    Bool → List ℕ → Bool :=
  fun positive pre =>
    if thirdGuard N pre then
      ordinaryParityRosserPolicy false
        (thirdQ N (rosserAncestor 3 pre)) positive pre
    else secondPolicy e chi m omega N positive pre

def finalPolicy (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 3 (secondPolicy e chi m omega N)
    (thirdReplacement e chi m omega N)

theorem old_even (e chi : ℝ) (m : ℕ) (omega N : ℝ) (pre : List ℕ) :
    oldPolicy e chi m omega N true pre = true :=
  HistoricalThirdCoarse.policy_even e chi m omega N pre

theorem second_even (e chi : ℝ) (m : ℕ) (omega N : ℝ) (pre : List ℕ) :
    secondPolicy e chi m omega N true pre = true := by
  apply UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 2
  · exact old_even e chi m omega N
  · intro q
    simp [secondReplacement, ordinaryParityRosserPolicy, oddFirstExitPolicy,
      old_even]

theorem final_even (e chi : ℝ) (m : ℕ) (omega N : ℝ) (pre : List ℕ) :
    finalPolicy e chi m omega N true pre = true := by
  apply UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 3
  · exact second_even e chi m omega N
  · intro q
    simp [thirdReplacement, ordinaryParityRosserPolicy, oddFirstExitPolicy,
      second_even]

/-- The next odd full-rank query uses the raised physical cap. The
even full-rank query bypasses by `final_even`. -/
theorem third_hit_odd_test
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (pre : List ℕ)
    (hdepth : 3 < pre.length) (hguard : thirdGuard N pre) :
    finalPolicy e chi m omega N false pre =
      decide (ordinaryRosserPrefixAdmissible false
        (thirdQ N (rosserAncestor 3 pre)) pre) := by
  have hnot : ¬pre.length ≤ 3 := by omega
  simp [finalPolicy, firstExitDepthSplicePolicy, hnot,
    thirdReplacement, hguard, ordinaryParityRosserPolicy,
    oddFirstExitPolicy]

/-- At every strict descendant of a selected third node, the actual
conditional final policy agrees with its frozen ordinary upper tree. -/
theorem third_hit_descendant_policy
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (base later : List ℕ) (positive : Bool)
    (hlen : 3 ≤ base.length) (hguard : thirdGuard N base)
    (hlater : later ≠ []) :
    finalPolicy e chi m omega N positive (later ++ base) =
      frozenParityRosserPolicy false 3 (thirdQ N) positive
        (later ++ base) := by
  have hdepth : 3 < (later ++ base).length := by
    have hpos : 0 < later.length := List.length_pos_iff.mpr hlater
    simp only [List.length_append]
    omega
  have hg : thirdGuard N (later ++ base) :=
    (thirdGuard_later_history N later base hlen).2 hguard
  have hnot : ¬(later ++ base).length ≤ 3 := by omega
  simp [finalPolicy, firstExitDepthSplicePolicy, hnot,
    thirdReplacement, hg, frozenParityRosserPolicy,
    ancestorFrozenPolicy]

/-- Equality of the complete signed continuation, not merely its
next Boolean test. All selected descendants retain the same ancestor. -/
theorem third_hit_polynomial
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (base : List ℕ) (hlen : 3 ≤ base.length)
    (hguard : thirdGuard N base) (h : ℕ → ℝ)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    firstExitRetainedPolynomial (finalPolicy e chi m omega N)
        h base positive mass remaining =
      firstExitRetainedPolynomial
        (frozenParityRosserPolicy false 3 (thirdQ N))
        h base positive mass remaining := by
  have hrec (later : List ℕ) (positive : Bool) (mass : ℝ)
      (remaining : List ℕ) :
      firstExitRetainedPolynomial (finalPolicy e chi m omega N)
          h (later ++ base) positive mass remaining =
        firstExitRetainedPolynomial
          (frozenParityRosserPolicy false 3 (thirdQ N))
          h (later ++ base) positive mass remaining := by
    induction remaining generalizing later positive mass with
    | nil => rfl
    | cons p ps ih =>
        have htest := third_hit_descendant_policy e chi m omega N base
          (p :: later) (!positive) hlen hguard (by simp)
        simp only [firstExitRetainedPolynomial]
        rw [htest, ih later positive mass,
          ih (p :: later) (!positive) (mass * h p)]
  simpa using hrec [] positive mass remaining

/-- The actual old rank-three frontier has negative incoming sign.
Native ordinary continuation divides the physical level by the exact
prefix product and reverses upper to lower at this odd rank. -/
theorem third_frontier_signed_lower_density
    (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 3
      (secondPolicy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z))
    (hthird : ThirdRegion
      (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 0)
      (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 1)
      (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 2))
    (hpre : ordinaryRosserPrefixAdmissible false
      (thirdQ (N : ℝ) state.selectedPrefix) state.selectedPrefix) :
    v (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 0) <
        v (primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 1 +
          primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix 2) ∧
      firstExitRetainedPolynomial
        (finalPolicy e chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
        state.positive state.mass state.remaining =
        -state.mass * actualSmallRosserMinusDensity N cap
          (state.selectedPrefix.headD 0 : ℝ)
          (thirdQ (N : ℝ) state.selectedPrefix /
            (state.selectedPrefix.prod : ℝ)) := by
  obtain ⟨_, _, _, _, _, hcap⟩ := third_initial_physical_gates hthird
  refine ⟨hcap, ?_⟩
  have hlen := firstExitDepthFrontier_selected_length 3
    (secondPolicy e chi m omega (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) []
    (roughPrimeUniverse N cap 0 z) true 1 (by simp) state hstate
  have h := firstExitRetainedPolynomial_frozenParity_frontier_density
    false 3 (by omega) (secondPolicy e chi m omega (N : ℝ))
    (thirdQ (N : ℝ)) N cap z state hstate hpre
  have hg : thirdGuard (N : ℝ) state.selectedPrefix := by
    simpa [thirdGuard, rosserAncestor, hlen] using hthird
  rw [third_hit_polynomial e chi m omega (N : ℝ) state.selectedPrefix
    (by omega) hg (fun p : ℕ => 1 / ((p : ℝ) - 1))
    state.positive state.mass state.remaining]
  simpa [actualFrozenFrontierDensityTerm, ordinaryRosserResidualLower,
    hlen, signedTreeCoefficient_evenListLength_eq_negOnePow] using h

/-- Every integer test, including zero, uses the same fixed signed
rough coefficient of the combined second/third causal policy. -/
theorem final_rough_integer_count_exact
    (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (n : ℤ) :
    firstExitRetainedPolynomial (finalPolicy e chi m omega (N : ℝ))
        (integerDivisorIndicator n) [] true 1
        (roughPrimeUniverse N cap w z) =
      supportedDivisorSum
        (firstExitRetainedModuli (finalPolicy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient
          (finalPolicy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap w z) d : ℝ)) n.natAbs := by
  let R := finalPolicy e chi m omega (N : ℝ)
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum R
    (integerDivisorIndicator n) (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  unfold supportedDivisorSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_integerDivisorIndicator
    (firstExitRetainedModuli_squarefree R
      (roughPrimeUniverse N cap w z)
      (roughPrimeUniverse_nodup N cap w z)
      (fun _ hp => mem_roughPrimeUniverse_prime hp) hd) n]
  by_cases hdn : d ∣ n.natAbs <;> simp [hdn]

/-- Exact reciprocal-totient mean of those same signed rough
coefficients; no new density constant or auxiliary cover appears. -/
theorem final_rough_coprime_mean_exact
    (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial (finalPolicy e chi m omega (N : ℝ))
        (fun p => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity
        (firstExitRetainedModuli (finalPolicy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient
          (finalPolicy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap w z) d : ℝ)) := by
  let R := finalPolicy e chi m omega (N : ℝ)
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum R
    (fun p => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  unfold reciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_reciprocalTotient
    (firstExitRetainedModuli_squarefree R
      (roughPrimeUniverse N cap w z)
      (roughPrimeUniverse_nodup N cap w z)
      (fun _ hp => mem_roughPrimeUniverse_prime hp) hd)]
  simp only [div_eq_mul_inv, one_mul]

/-- The original firstStop and initial odd cube decision are preserved,
including equality at the original cutoff. -/
theorem final_first_test (e chi : ℝ) (m : ℕ) (omega N : ℝ) (p : ℕ) :
    finalPolicy e chi m omega N false [p] = true ↔
      ordinaryRosserPrefixAdmissible false
        (N ^ HistoricalThirdCoarse.initial e) [p] ∧
      HistoricalThirdCoarse.firstStop e m N [p] := by
  change oldPolicy e chi m omega N false [p] = true ↔ _
  rw [HistoricalThirdCoarse.policy_through_two e chi m omega N false [p] (by simp)]
  simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]

theorem retained_first_initial_cube_exponent
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega N : ℝ) (p : ℕ)
    (hretain : finalPolicy e chi m omega N false [p] = true) :
    3 * primeHistoryLogCoordinates N 1 [p] 0 <
      HistoricalThirdCoarse.initial e := by
  have hstop := ((final_first_test e chi m omega N p).mp hretain).2
  rcases hstop with ⟨i, _, hupper, hcut⟩
  exact original_first_cube_from_stop he (hupper.le.trans hcut)

/-- The literal coefficient of the combined fallback policy is the unique
small/rough product coefficient with the sign chosen from its rough
first-exit Möbius value. It is the actual attached counting coefficient
for this policy, not a new abstract scalar or an auxiliary cover. -/
theorem fallback_attached_leaf
    (e chi : ℝ) (m : ℕ) (omega nu r epsilon : ℝ)
    (cap : ℕ → ℕ) (N : ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRootLeaves (finalPolicy e chi m omega (N : ℝ))
      (fun _ => 1)
      (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2))
        ((N : ℝ) ^ (nu * r))))
    (a : ℕ)
    (ha : a ∈ actualSmallRosserSupport N (cap N)
      ((N : ℝ) ^ (nu * epsilon ^ 2))) :
    let retain := fun M : ℕ => (finalPolicy e chi m omega (M : ℝ)) false
    let w := (N : ℝ) ^ (nu * epsilon ^ 2)
    let z := (N : ℝ) ^ (nu * r)
    let L := (N : ℝ) ^ (nu * epsilon)
    let q := a * leaf.selected.prod
    q ∈ attachedUpperModuli nu r epsilon retain cap N ∧
      Squarefree q ∧ q.Coprime N ∧
      |attachedUpperCoefficient nu r epsilon retain cap N q| ≤ 1 ∧
      attachedUpperCoefficient nu r epsilon retain cap N q =
        signAttachedCoefficient
          (firstExitRetainedCoefficient (finalPolicy e chi m omega (N : ℝ))
            (roughPrimeUniverse N (cap N) w z) leaf.selected.prod : ℝ)
          (actualSmallRosserMinus N (cap N) w L a)
          (actualSmallRosserPlus N (cap N) w L a) := by
  dsimp only [attachedUpperModuli, attachedUpperCoefficient]
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let z := (N : ℝ) ^ (nu * r)
  let L := (N : ℝ) ^ (nu * epsilon)
  let R := finalPolicy e chi m omega (N : ℝ)
  let d := leaf.selected.prod
  have hd : d ∈ firstExitRetainedModuli R (roughPrimeUniverse N (cap N) w z) :=
    (mem_firstExitRetainedModuli R _ d).mpr ⟨leaf, hleaf, rfl⟩
  have hfixed : d ∈ fixedRoughSupport (R false) N (cap N) w z := by
    rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
      R (final_even e chi m omega (N : ℝ)) N (cap N) w z]
    exact hd
  have hq : a * d ∈ actualSmallRoughModuli (R false) N (cap N) w z :=
    Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr ⟨ha, hfixed⟩, rfl⟩
  refine ⟨hq, actualSmallRoughModuli_squarefree (R false) N (cap N) w z hq,
    actualSmallRoughModuli_coprime_target (R false) N (cap N) w z hq,
    actualSmallRoughRho_abs_le_one (R false) N (cap N) w z L (a * d), ?_⟩
  change smallRoughRho (actualSmallRosserSupport N (cap N) w)
    (fixedRoughSupport (R false) N (cap N) w z)
    (fixedRoughCoefficient (R false) N (cap N) w z)
    (actualSmallRosserMinus N (cap N) w L)
    (actualSmallRosserPlus N (cap N) w L) (a * d) = _
  rw [smallRoughRho_mul
    (fun _ hx => actualSmallRosserSupport_smallPrimeSupportedAt N (cap N) w hx)
    (fun _ hx => fixedRoughSupport_roughPrimeSupportedAt (R false) N (cap N) w z hx)
    (fixedRoughCoefficient (R false) N (cap N) w z)
    (actualSmallRosserMinus N (cap N) w L)
    (actualSmallRosserPlus N (cap N) w L) ha hfixed]
  change signAttachedCoefficient (fixedRoughCoefficient (R false) N (cap N) w z d)
    (actualSmallRosserMinus N (cap N) w L a)
    (actualSmallRosserPlus N (cap N) w L a) = _
  rw [UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    R (final_even e chi m omega (N : ℝ)) N (cap N) w z d]

/-- Every nonzero coefficient for this literal combined fallback policy has
integer small/rough support, is squarefree and coprime to the target,
and retains the same one bound. The real auxiliary PP cover is absent. -/
theorem fallback_nonzero_attached_support
    (e chi : ℝ) (m : ℕ) (omega nu r epsilon : ℝ)
    (cap : ℕ → ℕ) (N q : ℕ)
    (hq : attachedUpperCoefficient nu r epsilon
      (fun M => (finalPolicy e chi m omega (M : ℝ)) false) cap N q ≠ 0) :
    q ∈ attachedUpperModuli nu r epsilon
        (fun M => (finalPolicy e chi m omega (M : ℝ)) false) cap N ∧
      Squarefree q ∧ q.Coprime N ∧
      |attachedUpperCoefficient nu r epsilon
        (fun M => (finalPolicy e chi m omega (M : ℝ)) false) cap N q| ≤ 1 := by
  let R := finalPolicy e chi m omega (N : ℝ)
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let z := (N : ℝ) ^ (nu * r)
  let L := (N : ℝ) ^ (nu * epsilon)
  change actualSmallRoughRho (R false) N (cap N) w z L q ≠ 0 at hq
  obtain ⟨a, ha, b, hb, hprod, _, _⟩ :=
    actualSmallRoughRho_ne_zero_factors (R false) N (cap N) w z L hq
  have hmem : q ∈ actualSmallRoughModuli (R false) N (cap N) w z := by
    rw [hprod]
    exact Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  exact ⟨hmem,
    actualSmallRoughModuli_squarefree (R false) N (cap N) w z hmem,
    actualSmallRoughModuli_coprime_target (R false) N (cap N) w z hmem,
    actualSmallRoughRho_abs_le_one (R false) N (cap N) w z L q⟩

end
end ImbalancedChen.P5OriginalAboveMuThirdLowerPhysicalCoefficient
