import ImbalancedChen.P5U6AdoptedEnhancedHarmonic
import ImbalancedChen.P5U6RetainedExplicitBuffer

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Uniform arithmetic product-buffer removal for the actual adopted U6 harmonic
main. A mask is any predicate on the original labelled arithmetic prime pairs;
it may depend arbitrarily on N. A finite domination argument pays its cutoff
loss by the UNMASKED cutoff loss, whose actual prime-pair limit is proved by
the recovered native enhanced harmonic theorem. Thus no constancy,
measurability, logbox representation or convergence premise is imposed on E.

This does not identify the main term of a moving mask with an integral, prove
the original adopted h248 soundness, or bound the physical retained Y6 count.
Those analytic/causal suppliers remain OPEN.
-/

namespace ImbalancedChen.P5U6UniformMovingMaskBufferSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
open Part5OriginalUpsilon5CausalDictionary
open P5U6RunboEnhancedFloorInterfaceSourceOnly
open P5U6AdoptedH248BindingSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly
open P5U6RetainedExplicitBufferSourceOnly
open P5U6AdoptedEnhancedHarmonicSourceOnly

abbrev Point := Fin 2 → ℝ

def adoptedTest (x : Point) : ℝ :=
  currentChenUpsilon6OrdinaryClippedTest x +
    adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x

def pairWeight (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  adoptedTest (actualPrimeTupleLog N ![t.1, t.2]) / (Nat.totient (t.1 * t.2) : ℝ)

def maskedMain (N : ℕ) (E : ℕ × ℕ → Prop) (eta : ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta, if E t then 0 else pairWeight N t

def fullMain (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6OrdinarySelector N eta, pairWeight N t

/-- The finite harmonic coefficient is exactly the original R expression,
before reciprocal-coordinate harmonic density is inserted. -/
theorem adoptedTest_eq_original {x : Point} (hx : x ∈ currentChenUpsilon6LogRectangle) :
    adoptedTest x = 4 * (Real.log (currentChenUpsilon6OrdinaryProfile x - 1) +
      adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x)) / originalResidual x := by
  rw [adoptedTest, currentChenUpsilon6OrdinaryClippedTest_eq hx]
  unfold currentChenUpsilon6OrdinaryFactor bareCorrection
  rw [originalResidual_eq_a_mul_profile]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact arithmetic mask binding, including N-dependent choices of E. -/
theorem maskedMain_eq_filtered (N : ℕ) (E : ℕ × ℕ → Prop) (eta : ℝ) :
    maskedMain N E eta =
      ∑ t ∈ (currentChenUpsilon6OrdinarySelector N eta).filter (fun t => ¬ E t), pairWeight N t := by
  unfold maskedMain
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : E t <;> simp [ht]

theorem selector_antitone {N : ℕ} (hN : 2 ≤ N) {eta theta : ℝ} (h : eta ≤ theta) :
    currentChenUpsilon6OrdinarySelector N theta ⊆ currentChenUpsilon6OrdinarySelector N eta := by
  intro t ht
  obtain ⟨hp, hq, hx⟩ := (mem_currentChenUpsilon6OrdinarySelector_log_iff hN theta t).mp ht
  apply (mem_currentChenUpsilon6OrdinarySelector_log_iff hN eta t).mpr
  refine ⟨hp, hq, hx.1, hx.2.1, ?_⟩
  have hg := hx.2.2
  change currentChenUpsilon6LogCoordinates N t 0 + currentChenUpsilon6LogCoordinates N t 1 <
    (833 / 2500 : ℝ) - eta
  linarith

theorem adoptedTest_nonneg {x : Point} (hx : x ∈ currentChenUpsilon6LogDomain 0) :
    0 ≤ adoptedTest x := by
  have hs := (profile_range (by norm_num : (0 : ℝ) ≤ 0) hx).1
  have hR : 0 < originalResidual x := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 2 * (417 / 5000 : ℝ))
    (originalResidual_ge_two_a (by norm_num) hx)
  have ho : 0 ≤ currentChenUpsilon6OrdinaryClippedTest x := by
    rw [currentChenUpsilon6OrdinaryClippedTest_eq hx.1]
    unfold currentChenUpsilon6OrdinaryFactor
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
      (mul_nonneg (by linarith) (by norm_num))
  unfold adoptedTest bareCorrection
  exact add_nonneg ho (mul_nonneg (adoptedFloor_nonneg _) (div_nonneg (by norm_num) hR.le))

theorem pairWeight_nonneg {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ currentChenUpsilon6OrdinarySelector N 0) : 0 ≤ pairWeight N t := by
  have hx := ((mem_currentChenUpsilon6OrdinarySelector_log_iff hN 0 t).mp ht).2.2
  have hcoords : currentChenUpsilon6LogCoordinates N t = actualPrimeTupleLog N ![t.1, t.2] := by
    funext i
    fin_cases i <;> rfl
  rw [hcoords] at hx
  exact div_nonneg (adoptedTest_nonneg ⟨hx.1, hx.2.2.le⟩) (Nat.cast_nonneg _)

/-- A mask removes each labelled pair once. On the actual discarded
arithmetic product strip its weight lies between zero and the full weight.
This finite identity/inequality does not require any regularity of E. -/
theorem finite_masked_buffer_loss {N : ℕ} (hN : 2 ≤ N) (E : ℕ × ℕ → Prop)
    {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ maskedMain N E 0 - maskedMain N E eta ∧
      maskedMain N E 0 - maskedMain N E eta ≤ fullMain N 0 - fullMain N eta := by
  have hsub := selector_antitone hN heta
  have hsplit := Finset.sum_sdiff (f := fun t => if E t then 0 else pairWeight N t) hsub
  have hfull := Finset.sum_sdiff (f := pairWeight N) hsub
  have hnonneg : 0 ≤ ∑ t ∈ currentChenUpsilon6OrdinarySelector N 0 \
      currentChenUpsilon6OrdinarySelector N eta, if E t then 0 else pairWeight N t := by
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · exact le_rfl
    · exact pairWeight_nonneg hN (Finset.mem_sdiff.mp ht).1
  have hle : (∑ t ∈ currentChenUpsilon6OrdinarySelector N 0 \
      currentChenUpsilon6OrdinarySelector N eta, if E t then 0 else pairWeight N t) ≤
      ∑ t ∈ currentChenUpsilon6OrdinarySelector N 0 \
        currentChenUpsilon6OrdinarySelector N eta, pairWeight N t := by
    apply Finset.sum_le_sum
    intro t ht
    split_ifs
    · exact pairWeight_nonneg hN (Finset.mem_sdiff.mp ht).1
    · exact le_rfl
  change (∑ t ∈ currentChenUpsilon6OrdinarySelector N 0 \
      currentChenUpsilon6OrdinarySelector N eta, if E t then 0 else pairWeight N t) +
      maskedMain N E eta = maskedMain N E 0 at hsplit
  change (∑ t ∈ currentChenUpsilon6OrdinarySelector N 0 \
      currentChenUpsilon6OrdinarySelector N eta, pairWeight N t) +
      fullMain N eta = fullMain N 0 at hfull
  constructor <;> linarith

private theorem full_domain_box (eta : ℝ) :
    currentChenUpsilon6LogDomain eta ∩
      P5U6SteppedPrimeAdmissibilitySourceOnly.box (fun _ => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) = currentChenUpsilon6LogDomain eta := by
  apply inter_eq_left.mpr
  intro x hx
  obtain ⟨ha, hh, hv, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1
  exact ⟨ha, hh.trans (by norm_num), (by norm_num : (417 / 5000 : ℝ) ≤ 19 / 125).trans hv, hd⟩

private theorem fullMain_eq_native {N : ℕ} (hN : 2 ≤ N) (eta : ℝ) :
    fullMain N eta = nativeEnhancedBoxTest N eta (fun _ => (417 / 5000 : ℝ))
      (fun _ => (59 / 250 : ℝ)) := by
  rw [nativeEnhancedBoxTest_eq_pair_sum]
  unfold fullMain pairWeight adoptedTest
  apply Finset.sum_congr rfl
  intro t ht
  have hx := ((mem_currentChenUpsilon6OrdinarySelector_log_iff hN eta t).mp ht).2.2.1
  have hcoords : currentChenUpsilon6LogCoordinates N t = actualPrimeTupleLog N ![t.1, t.2] := by
    funext i
    fin_cases i <;> rfl
  rw [hcoords] at hx
  obtain ⟨ha, hh, hv, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
  have hb : actualPrimeTupleLog N ![t.1, t.2] ∈
      P5U6SteppedPrimeAdmissibilitySourceOnly.box (fun _ => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ)) :=
    ⟨ha, hh.trans (by norm_num), (by norm_num : (417 / 5000 : ℝ) ≤ 19 / 125).trans hv, hd⟩
  rw [indicator_of_mem hb]

theorem tendsto_fullMain {eta : ℝ} (heta : 0 ≤ eta) :
    Tendsto (fun N => fullMain N eta) atTop (𝓝 (fullIntegral eta)) := by
  have h := tendsto_nativeEnhancedBoxTest eta heta
    (fun _ => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
  rw [full_domain_box] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (fullMain_eq_native hN eta).symm

/-- One threshold precedes EVERY arithmetic pair mask. In particular the
mask may be selected adversarially after N and may vary at every N.
The explicit eta is fixed before that threshold; no moving-mask limit is
postulated or inferred. -/
theorem eventually_uniform_masked_buffer_loss {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop,
      |maskedMain N E 0 - maskedMain N E (epsilon / 1008)| < epsilon := by
  have heta : 0 ≤ epsilon / 1008 := by positivity
  have hbuffer := retained_abs_buffer_loss_le (fun _ : Point => False)
    (by simp) heta
  have heq (theta : ℝ) : retainedEstimatorIntegral (fun _ : Point => False) theta =
      fullIntegral theta := by
    simp [retainedEstimatorIntegral, fullIntegral]
  rw [heq, heq] at hbuffer
  have hupper : fullIntegral 0 - fullIntegral (epsilon / 1008) < epsilon := by
    have h := (le_abs_self _).trans hbuffer
    linarith
  have hlim := (tendsto_fullMain (by norm_num : (0 : ℝ) ≤ 0)).sub (tendsto_fullMain heta)
  have hsmall := hlim.eventually_lt_const hupper
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  intro E
  have hfinite := finite_masked_buffer_loss hN E heta
  rw [abs_of_nonneg hfinite.1]
  exact hfinite.2.trans_lt hsmallN

/-- Direct specialization to arbitrary N-dependent masks. -/
theorem eventually_moving_mask_buffer_loss (E : ℕ → (ℕ × ℕ → Prop))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |maskedMain N (E N) 0 - maskedMain N (E N) (epsilon / 1008)| < epsilon := by
  filter_upwards [eventually_uniform_masked_buffer_loss hepsilon] with N hN
  exact hN (E N)

end

end ImbalancedChen.P5U6UniformMovingMaskBufferSourceOnly
