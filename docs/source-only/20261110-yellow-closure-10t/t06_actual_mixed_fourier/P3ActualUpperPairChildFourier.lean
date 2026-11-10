import ImbalancedChen.P3ActualHBChildMixedFourier
import ImbalancedChen.P4BArbitraryWidthUpperPairOccurrence

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.
Same manuscript/Lean/Mathlib pins as P3ActualHBChildMixedFourier.

Concrete actual rank-two upper-pair supplier, with NO abstract Family input.
The original normalized pair, original group owners, complete-product eta,
group psi, individual plateau and arbitrary legal physical width are the
ones in P4BArbitraryWidthUpperPairOccurrence. The existing exact original
signed/attachedUpper HB identity is reused unchanged through that import.
The extra smooth children retain their actual dyadic-to-U translations.

The fixed HB occurrence dimension d<=12 is distinct from atlas resolution
resolution(N). Width=1/(resolution+1) displays the genuine cost
(resolution+1)^24. A polylog bound on that chosen resolution then gives
the explicit logarithmic derivative/Fourier budget before N grows.
No arithmetic PP estimate or total-modulus tail payment is asserted.
-/

namespace ImbalancedChen.P3ActualUpperPairChildFourier
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open P3ActualHBChildMixedFourier P4BOuterRampRoughness
open P4BArbitraryWidthUpperPairOccurrence
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget
open P5Z.AllRankCauchyKernelIntegral
open P5Z.AllWordAmbientOccurrenceBound P5Z.OccurrenceWordFourFactorLeibniz
open P5Z.ActualEuclideanPhysicalFourier P5Z.OccurrenceEuclideanMixedIntegral
open P5Z.ActualAllRankOccurrenceFourierBridge P5Z.ActualEtaPsiOccurrenceBudget
open P5Z.LicensedOriginalIntegerProfile P3HBSmoothThreeWayRatioTwo

def refinedUpper {d : ℕ} (b κ width : ℝ) (N : ℕ)
    (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ)
    (offset : Fin d → ℝ) (child : Fin d → Fin 3) (z : Fin d → ℝ) : ℝ :=
  occurrenceChart b κ width N owner U R κ₀ z * shiftedChildTensor offset child z

def refinedUpperEuclidean {d : ℕ} (b κ width : ℝ) (N : ℕ)
    (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ)
    (offset : Fin d → ℝ) (child : Fin d → Fin 3) : V d → ℂ :=
  euclideanLift d (refinedUpper b κ width N owner U R κ₀ offset child)

theorem refinedUpper_children_sum {d : ℕ} (b κ width : ℝ) (N : ℕ)
    (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ)
    (offset : Fin d → ℝ) (z : Fin d → ℝ) :
    (∑ child : Fin d → Fin 3, refinedUpper b κ width N owner U R κ₀ offset child z) =
      occurrenceChart b κ width N owner U R κ₀ z * ∏ i : Fin d, psiLog (offset i+z i) := by
  simp only [refinedUpper, ← Finset.mul_sum, shiftedChildTensor_children_sum]

theorem refinedUpper_support {d : ℕ} (b κ width : ℝ) (N : ℕ)
    (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ)
    (offset : Fin d → ℝ) (child : Fin d → Fin 3) :
    Function.support (refinedUpper b κ width N owner U R κ₀ offset child) ⊆
      tsupport (occurrenceChart b κ width N owner U R κ₀) := by
  intro z hz
  apply subset_tsupport
  intro heq
  exact hz (by simp [refinedUpper, heq])

/-- Exact source identification at every actual integer atom, including
all twelve possible HB slots and repeated group owners. The normalized
raw upper-pair chart, complete product eta and original group psi remain
the ones in the existing caller's Licence. -/
theorem refinedUpper_integer_atom {d : ℕ} {b κ ν r width : ℝ}
    (hb : 0 < b) (hν : 0 < ν) (hr : 0 < r) (hwidth : 0 < width)
    (hgap : 2*width ≤ baseline b κ-ν*r)
    (N : ℕ) (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ)
    (κ₀ : ℝ) (label : Fin d → ℕ) (child : Fin d → Fin 3) (n : Fin d → ℕ)
    (hU : ∀ i, 0 < U i) (hlo : ∀ i, U i < (n i : ℝ))
    (hhi : ∀ i, (n i : ℝ) ≤ 2*U i) :
    (refinedUpper b κ width N owner U R κ₀
      (fun i => Real.log (U i/(2 : ℝ)^(label i))) child (logOccurrence U n) : ℂ) =
      ((chartAmbient (P4BArbitraryWidthUpperPairProfile.licence hb hν hr hwidth hgap N)
        chi eta (N : ℝ) κ₀ R (fun i => (integerGroupProduct owner n i : ℝ)) /
          ∏ i, Real.log (integerGroupProduct owner n i : ℝ) : ℝ) : ℂ) *
        ∏ i : Fin d, smoothCoord (fun t => (chi t : ℂ))
          (n i : ℝ) (label i) (child i) := by
  have hbase := occurrenceChart_integer_atom hb hν hr hwidth hgap
    N owner U R κ₀ n hU hlo hhi
  have hchild := shiftedChildTensor_physical label child U hU (logOccurrence U n)
  have hcoord (i : Fin d) : U i*Real.exp (logOccurrence U n i) = (n i : ℝ) := by
    have hn : 0 < (n i : ℝ) := (hU i).trans (hlo i)
    rw [logOccurrence, Real.exp_log (div_pos hn (hU i))]
    field_simp [(hU i).ne']
  simp_rw [hcoord] at hchild
  rw [refinedUpper, Complex.ofReal_mul, hbase, hchild]

/-- Uniform actual upper-pair mixed derivative cost; all cross terms
are included by the existing four-factor LIST allocation rule. -/
theorem exists_refinedUpper_word_width_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b κ ν r width : ℝ,
      0 < b → b ≤ 1 → 0 < κ → 0 < ν → 0 < r → 0 < width →
      2*width ≤ baseline b κ-ν*r →
      ∀ (N d : ℕ) (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ)
        (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3)
        (w : List (Fin d)) (z : Fin d → ℝ),
      0 < (N : ℝ) → (∀ i, 0 < U i) → (∀ i, 0 < R i) →
      d ≤ 12 → w.length ≤ 24 →
      |occWord w (refinedUpper b κ width N owner U R κ₀ offset child) z| ≤ C/width^24 := by
  obtain ⟨CA, hCA, bA⟩ := exists_occurrenceChart_width_budget
  obtain ⟨MC, hMC, bC⟩ := exists_childLog_global_budget 24
  let C : ℝ := (4 : ℝ)^24*CA*MC^12
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro b κ ν r width hb hbOne hκ hν hr hwidth hgap
    N d owner U R κ₀ offset child w z hN hU hR hd hw
  have hc (v : List (Fin d)) (hv : v.length ≤ w.length) :
      |occWord v (shiftedChildTensor offset child) z| ≤ MC^12 :=
    (shiftedChildTensor_word_bound offset child v z MC (zero_le_one.trans hMC)
      (fun n hn a u => bC n a u (hn.trans (hv.trans hw)))).trans
      (pow_le_pow_right₀ hMC hd)
  have hraw := occWord_four_bound
    (occurrenceChart b κ width N owner U R κ₀) (shiftedChildTensor offset child)
    (fun _ => 1) (fun _ => 1)
    (occurrenceChart_smooth hb hν hr hwidth hgap N owner U R κ₀)
    (shiftedChildTensor_smooth offset child) contDiff_const contDiff_const
    w z (CA/width^24) (MC^12) 1 1
    (by positivity) (by positivity) zero_le_one zero_le_one
    (fun v hv => bA b κ ν r width hb hbOne hκ hν hr hwidth hgap
      N d owner U R κ₀ v z hN hU hR hd (hv.trans hw)) hc
    (fun v hv => occurrence_one_bound v z) (fun v hv => occurrence_one_bound v z)
  have heq : (fun y => occurrenceChart b κ width N owner U R κ₀ y *
      shiftedChildTensor offset child y * 1 * 1) =
      refinedUpper b κ width N owner U R κ₀ offset child := by
    funext y
    simp [refinedUpper]
  rw [heq] at hraw
  simp only [mul_one] at hraw
  calc
    _ ≤ (4 : ℝ)^w.length*((CA/width^24)*MC^12) := hraw
    _ ≤ (4 : ℝ)^24*((CA/width^24)*MC^12) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw) (by positivity)
    _ = C/width^24 := by dsimp [C]; ring

/-- Original (F) for the concrete actual upper-pair HB chart, with its
true inverse-width cost and without a Family/derivative/Fourier premise. -/
theorem exists_refinedUpper_fourier_width_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b κ ν r width : ℝ,
      0 < b → b ≤ 1 → 0 < κ → 0 < ν → 0 < r → 0 < width →
      2*width ≤ baseline b κ-ν*r →
      ∀ (N d : ℕ) (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ)
        (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3),
      0 < (N : ℝ) → (∀ i, 0 < U i) → (∀ i, 0 < R i) → d ≤ 12 →
      let f := refinedUpperEuclidean b κ width N owner U R κ₀ offset child
      mixedD d f ≤ C/width^24 ∧
      (∀ ξ : Fin d → ℝ, ‖physicalFourier d f ξ‖ ≤
        (C/width^24)*productCauchy d ξ) ∧
      (∫ ξ : Fin d → ℝ, ‖physicalFourier d f ξ‖)/frequencyScale^d ≤
        (C/width^24)/2^d ∧
      ∀ H : ℝ, 0 < H → ∀ z : V d,
        ‖f z-truncatedPhysical d f H z‖ ≤ (d : ℝ)*(C/width^24)/H := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_refinedUpper_word_width_budget
  refine ⟨dimensionBudget 2*C₀,
    mul_nonneg (dimensionBudget_nonneg 2) hC₀, ?_⟩
  intro b κ ν r width hbpos hbOne hκ hν hr hwidth hgap
    N d owner U R κ₀ offset child hN hU hR hd
  let w := refinedUpper b κ width N owner U R κ₀ offset child
  let f := refinedUpperEuclidean b κ width N owner U R κ₀ offset child
  have hw : ContDiff ℝ ∞ w :=
    (occurrenceChart_smooth hbpos hν hr hwidth hgap N owner U R κ₀).mul
      (shiftedChildTensor_smooth offset child)
  have hs := refinedUpper_support b κ width N owner U R κ₀ offset child
  have hc : HasCompactSupport w :=
    (occurrenceChart_compact b κ width N owner U R κ₀).mono' hs
  have hbox : tsupport w ⊆ plateauBox d :=
    (closure_minimal hs isClosed_closure).trans
      (occurrenceChart_tsupport_box b κ width N owner U R κ₀)
  have hf : ContDiff ℝ ∞ f := euclideanLift_smooth d w hw
  have hfc : HasCompactSupport f := euclideanLift_compact d w hc
  have hnonneg : 0 ≤ C₀/width^24 := by positivity
  have hD := mixedD_euclideanLift_le d w hw hc hbox (C₀/width^24) hnonneg
    (fun v hv z => hb b κ ν r width hbpos hbOne hκ hν hr hwidth hgap
      N d owner U R κ₀ offset child v z hN hU hR hd (by omega))
  have hbound : mixedD d f ≤ (dimensionBudget 2*C₀)/width^24 := by
    apply hD.trans
    calc
      _ ≤ dimensionBudget 2*(C₀/width^24) :=
        mul_le_mul_of_nonneg_right (dimension_factor_le (by omega : d ≤ 6*2)) hnonneg
      _ = _ := by ring
  have hp (ξ : Fin d → ℝ) : ‖physicalFourier d f ξ‖ ≤
      ((dimensionBudget 2*C₀)/width^24)*productCauchy d ξ := by
    apply (physicalFourier_pointwise d f hf hfc ξ).trans
    apply mul_le_mul_of_nonneg_right hbound
    unfold productCauchy cauchy
    exact Finset.prod_nonneg (fun i hi => by positivity)
  refine ⟨hbound, hp, (physicalFourier_normalized_l1_le d f hf hfc).trans
    (div_le_div_of_nonneg_right hbound (by positivity)), ?_⟩
  intro H hH z
  exact (actual_uniform_truncation_error d f hf hfc H hH z).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg d)) hH.le)

/-- Actual resolution dependence, distinguished from the HB dimension.
The single C precedes the entire resolution function and target N. -/
theorem exists_refinedUpper_resolution_polylog_budget (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b κ ν r : ℝ,
      0 < b → b ≤ 1 → 0 < κ → 0 < ν → 0 < r →
      ∀ (N d resolution : ℕ), 1 ≤ Real.log (N : ℝ) →
      (resolution+1 : ℝ) ≤ Real.log (N : ℝ)^B →
      2/(resolution+1 : ℝ) ≤ baseline b κ-ν*r →
      ∀ (owner : Fin d → Fin 2) (U : Fin d → ℝ) (R : Fin 2 → ℝ)
        (κ₀ : ℝ) (offset : Fin d → ℝ) (child : Fin d → Fin 3),
      (∀ i, 0 < U i) → (∀ i, 0 < R i) → d ≤ 12 →
      mixedD d (refinedUpperEuclidean b κ (1/(resolution+1 : ℝ))
        N owner U R κ₀ offset child) ≤ C*Real.log (N : ℝ)^(24*B) := by
  obtain ⟨C, hC, hb⟩ := exists_refinedUpper_fourier_width_budget
  refine ⟨C, hC, ?_⟩
  intro b κ ν r hbpos hbOne hκ hν hr N d resolution hlog hres hgap
    owner U R κ₀ offset child hU hR hd
  have hrpos : 0 < (resolution+1 : ℝ) := by positivity
  have hN : 0 < (N : ℝ) := by
    by_contra hn
    have hz : (N : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg N)
    simp [hz] at hlog
  have hwidth : 0 < 1/(resolution+1 : ℝ) := one_div_pos.mpr hrpos
  have hgap' : 2*(1/(resolution+1 : ℝ)) ≤ baseline b κ-ν*r := by
    simpa only [mul_one_div] using hgap
  have hbound := (hb b κ ν r (1/(resolution+1 : ℝ)) hbpos hbOne hκ hν hr
    hwidth hgap' N d owner U R κ₀ offset child hN hU hR hd).1
  have hpow : (resolution+1 : ℝ)^24 ≤ Real.log (N : ℝ)^(24*B) := by
    calc
      _ ≤ (Real.log (N : ℝ)^B)^24 := pow_le_pow_left₀ hrpos.le hres 24
      _ = Real.log (N : ℝ)^(B*24) := (pow_mul _ _ _).symm
      _ = Real.log (N : ℝ)^(24*B) := by rw [Nat.mul_comm B 24]
  calc
    _ ≤ C/(1/(resolution+1 : ℝ))^24 := hbound
    _ = C*(resolution+1 : ℝ)^24 := by rw [one_div_pow, div_one_div]
    _ ≤ C*Real.log (N : ℝ)^(24*B) := mul_le_mul_of_nonneg_left hpow hC

end
end ImbalancedChen.P3ActualUpperPairChildFourier
