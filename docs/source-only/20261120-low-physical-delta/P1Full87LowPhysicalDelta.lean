import ImbalancedChen.P1Full87CompactWScaleAudit
import ImbalancedChen.P1Full87TrueDUnitBound
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Transport the *already located* five-rough-prime first-disagreement
obstruction to the genuine physical modulus d=a*b. The small Rosser factor
a is nonzero, so b <= d. On every physical d < w^5, the two original
RAW/LICENSED rough coefficients therefore agree at the unique (a,b) pair.
Both policies use the same sign-sensitive beta-minus/plus; the physical
coefficients agree as well. This gives a genuine low-physical-d vanishing
statement for the ORIGINAL trueDDeltaRho, rather than only for its rough
support symmetric difference.

No conclusion about the distribution or ordinary integral is made.
The final epsilon/w/z installation into the full-87 frozen compiler remains
unverified. All strict cutoffs stay strict. No new axiom or PP assumption.
-/

namespace ImbalancedChen.P1Full87LowPhysicalDelta

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaRho)

/-- Below the *original* five-factor threshold, both real rough
coefficients agree pointwise. A one-sided support membership would be an
actual changed-rough modulus, contradicting the earlier rank-five bound.
This is not an artificial mask: both coefficients are the original
fixedRoughCoefficient. -/
private theorem actual_rough_coefficients_agree_below_fifth
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap b : ℕ) (w z : ℝ) (hw : 1 ≤ w)
    (hb : (b : ℝ) < w ^ 5) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    fixedRoughCoefficient (S false) N cap w z b =
      fixedRoughCoefficient (R false) N cap w z b := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let F := fixedRoughSupport (S false) N cap w z
  let O := fixedRoughSupport (R false) N cap w z
  have hF :
      fixedRoughCoefficient (S false) N cap w z b =
        if b ∈ F then (ArithmeticFunction.moebius b : ℝ) else 0 := by
    simp [F, fixedRoughSupport, fixedRoughCoefficient,
      oddFirstExitRetainedCoefficient]
  have hO :
      fixedRoughCoefficient (R false) N cap w z b =
        if b ∈ O then (ArithmeticFunction.moebius b : ℝ) else 0 := by
    simp [O, fixedRoughSupport, fixedRoughCoefficient,
      oddFirstExitRetainedCoefficient]
  have hsame : b ∈ F ↔ b ∈ O := by
    constructor
    · intro hbf
      by_contra hbo
      have hchg :
          b ∈ (F \ O) ∪ (O \ F) := by
        simp [hbf, hbo]
      have hbig :=
        P1Full87ChangedRoughLevelObstruction.actual_full87_changed_rough_wpow_five_le
          delta n e q om N cap b w z hw (by simpa [F, O, R, S] using hchg)
      exact (not_lt_of_ge hbig) hb
    · intro hbo
      by_contra hbf
      have hchg :
          b ∈ (F \ O) ∪ (O \ F) := by
        simp [hbf, hbo]
      have hbig :=
        P1Full87ChangedRoughLevelObstruction.actual_full87_changed_rough_wpow_five_le
          delta n e q om N cap b w z hw (by simpa [F, O, R, S] using hchg)
      exact (not_lt_of_ge hbig) hb
  rw [hF, hO]
  by_cases hbf : b ∈ F
  · simp [hbf, (hsame.mp hbf)]
  · have hbo : b ∉ O := fun h => hbf (hsame.mpr h)
    simp [hbf, hbo]

/-- Lift the actual rough-coefficient equality through the ONE original
small-prime Rosser attachment. A physical d=a*b with nonzero small factor
a has b <= d, so d < w^5 rules out a changed rough coefficient.
The common carrier is only a reindexing of existing supported pairs.
No occurrence or sign is discarded and no mass is estimated. -/
theorem actual_full87_physical_rho_agree_below_fifth
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap d : ℕ) (w z L : ℝ)
    (hw : 1 ≤ w) (hd : (d : ℝ) < w ^ 5) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    actualSmallRoughRho (S false) N cap w z L d =
      actualSmallRoughRho (R false) N cap w z L d := by
  dsimp only
  classical
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let small := actualSmallRosserSupport N cap w
  let rough := fixedRoughSupport (S false) N cap w z ∪
    fixedRoughSupport (R false) N cap w z
  let betaMinus := actualSmallRosserMinus N cap w L
  let betaPlus := actualSmallRosserPlus N cap w L
  have hsmall : ∀ a ∈ small, SmallPrimeSupportedAt w a := by
    intro a ha
    exact actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b := by
    intro b hb
    rcases Finset.mem_union.mp hb with hs | hr
    · exact fixedRoughSupport_roughPrimeSupportedAt (S false) N cap w z hs
    · exact fixedRoughSupport_roughPrimeSupportedAt (R false) N cap w z hr
  have hS : fixedRoughSupport (S false) N cap w z ⊆ rough := by
    intro b hb
    exact Finset.mem_union.mpr (Or.inl hb)
  have hR : fixedRoughSupport (R false) N cap w z ⊆ rough := by
    intro b hb
    exact Finset.mem_union.mpr (Or.inr hb)
  have hphysicalS :
      smallRoughRho small rough (fixedRoughCoefficient (S false) N cap w z)
        betaMinus betaPlus =
      actualSmallRoughRho (S false) N cap w z L :=
    actualSmallRoughRho_eq_on_common_carrier (S false) N cap w z L rough hS
  have hphysicalR :
      smallRoughRho small rough (fixedRoughCoefficient (R false) N cap w z)
        betaMinus betaPlus =
      actualSmallRoughRho (R false) N cap w z L :=
    actualSmallRoughRho_eq_on_common_carrier (R false) N cap w z L rough hR
  have hpair :
      smallRoughRho small rough (fixedRoughCoefficient (S false) N cap w z)
          betaMinus betaPlus d =
        smallRoughRho small rough (fixedRoughCoefficient (R false) N cap w z)
          betaMinus betaPlus d := by
    unfold smallRoughRho
    apply Finset.sum_congr rfl
    intro x hx
    have hmem := (Finset.mem_filter.mp hx).1
    have hprod := (Finset.mem_filter.mp hx).2
    have hmem' : x ∈ small ×ˢ rough := hmem
    obtain ⟨ha, _hb⟩ := Finset.mem_product.mp hmem'
    have hanz : x.1 ≠ 0 := (hsmall x.1 ha).1
    have haone : (1 : ℝ) ≤ (x.1 : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hanz)
    have hbnonneg : (0 : ℝ) ≤ (x.2 : ℝ) := Nat.cast_nonneg _
    have hble : (x.2 : ℝ) ≤ (d : ℝ) := by
      calc
        (x.2 : ℝ) = 1 * (x.2 : ℝ) := by ring
        _ ≤ (x.1 : ℝ) * (x.2 : ℝ) :=
          mul_le_mul_of_nonneg_right haone hbnonneg
        _ = (d : ℝ) := by exact_mod_cast hprod
    have hbelow : (x.2 : ℝ) < w ^ 5 := lt_of_le_of_lt hble hd
    have hcoefficient :
        fixedRoughCoefficient (S false) N cap w z x.2 =
          fixedRoughCoefficient (R false) N cap w z x.2 :=
      actual_rough_coefficients_agree_below_fifth
        delta n e q om N cap x.2 w z hw hbelow
    simp only [smallRoughPairCoefficient, signAttachedCoefficient, hcoefficient]
  simpa only [hphysicalS, hphysicalR] using hpair

/-- The ORIGINAL support-zero-extended signed coefficient itself vanishes
at every physical d below the genuine five-rough-factor threshold. This
is stronger than the earlier claim that merely the rough symmetric
difference has no such b: it includes the small factor, sign-selected
Rosser beta, and the true physical modulus d. -/
theorem actual_full87_true_d_delta_zero_below_fifth
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap d : ℕ) (w z L : ℝ)
    (hw : 1 ≤ w) (hd : (d : ℝ) < w ^ 5) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    trueDDeltaRho (R false) (S false) N cap w z L d = 0 := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  have heq := actual_full87_physical_rho_agree_below_fifth
    delta n e q om N cap d w z L hw hd
  have hS :
      (if d ∈ actualSmallRoughModuli (S false) N cap w z then
         actualSmallRoughRho (S false) N cap w z L d else 0) =
      actualSmallRoughRho (S false) N cap w z L d := by
    by_cases hmem : d ∈ actualSmallRoughModuli (S false) N cap w z
    · simp [hmem]
    · have hz :
          actualSmallRoughRho (S false) N cap w z L d = 0 :=
        smallRoughRho_eq_zero_of_not_mem
          (actualSmallRosserSupport N cap w)
          (fixedRoughSupport (S false) N cap w z)
          (fixedRoughCoefficient (S false) N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L) hmem
      simp [hmem, hz]
  have hR :
      (if d ∈ actualSmallRoughModuli (R false) N cap w z then
         actualSmallRoughRho (R false) N cap w z L d else 0) =
      actualSmallRoughRho (R false) N cap w z L d := by
    by_cases hmem : d ∈ actualSmallRoughModuli (R false) N cap w z
    · simp [hmem]
    · have hz :
          actualSmallRoughRho (R false) N cap w z L d = 0 :=
        smallRoughRho_eq_zero_of_not_mem
          (actualSmallRosserSupport N cap w)
          (fixedRoughSupport (R false) N cap w z)
          (fixedRoughCoefficient (R false) N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L) hmem
      simp [hmem, hz]
  change (if d ∈ actualSmallRoughModuli (S false) N cap w z then
      actualSmallRoughRho (S false) N cap w z L d else 0) -
    (if d ∈ actualSmallRoughModuli (R false) N cap w z then
      actualSmallRoughRho (R false) N cap w z L d else 0) = 0
  rw [hS, hR, heq]
  ring

end
end ImbalancedChen.P1Full87LowPhysicalDelta
