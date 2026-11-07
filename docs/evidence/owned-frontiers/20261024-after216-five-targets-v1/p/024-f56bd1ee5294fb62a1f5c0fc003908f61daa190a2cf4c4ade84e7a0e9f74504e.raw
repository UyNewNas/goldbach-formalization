import ImbalancedChen.Part3ActualM2FinitePoissonAdapter
import ImbalancedChen.Part3ActualCompletedSquarePushforward

/-!
SOURCEONLY / UNCOMPILED. One actual weighted-to-positive-count supplier.
The original signed upper-f window, fixed t units, nonzero y, full signed
h window and actual common mode coefficients are unchanged. This does not
assert the remaining actual count -> half-open 576 collision embedding.
No norm bound, beta bound, carrier embedding or spectral target is assumed.
-/
namespace ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly
noncomputable section
open Classical Finset CommonSmoothCutoff
open GeneralDActivePairCountSourceOnly GeneralDRootResidueCostSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly ActualFixedFeaturePacketPushforwardSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedSquarePushforwardSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem norm_branch_eq (negative : Bool) (z : ℂ) :
    ‖branch negative z‖ = ‖z‖ := by
  cases negative <;> simp [branch]

private theorem norm_rootT_eq (A : ℕ) [NeZero A] (a : ZMod A)
    (u : (ZMod A)ˣ) (k : ZMod A) (t : (ZMod A)ˣ) :
    ‖rootT A a u k t‖ = 1 := by
  rw [rootT, ZMod.stdAddChar_apply, Circle.norm_coe]

/-- This uses the actual image-of-divisible-s carrier, even when q=0. -/
private theorem baseCarrier_original_window {e : MediumAtom} {q t : ℕ}
    (ht : t ∈ baseCarrier e q) : q*t ∈ factorCarrier e.Q2 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
  obtain ⟨hs, hd⟩ := mem_filter.mp hs
  have he : q*(s/q) = s := by
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel hd
  rwa [he]

private theorem original_innerMultiplier_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) {s : ℕ}
    (hs : s ∈ factorCarrier e.Q2) (n : ℤ) :
    ‖_root_.P3ActualLogAdapterSourceOnly.innerMultiplier e s n‖ ≤ 1 := by
  have hQ : 1 ≤ e.Q2 := he.2.2.2.1
  have hQ0 : 0 < e.Q2 := zero_lt_one.trans_le hQ
  have hslo := (factorCarrier_bounds hQ hs).2.1
  have hU : 1 ≤ _root_.P3ActualLogAdapterSourceOnly.Uu e s := by
    change 1 ≤ (s : ℝ)/e.Q2
    exact (le_div_iff₀ hQ0).mpr (by simpa only [one_mul] using hslo)
  have hU0 := zero_lt_one.trans_le hU
  have hi : (_root_.P3ActualLogAdapterSourceOnly.Uu e s)⁻¹ ≤ (1 : ℝ) := by
    simpa only [one_div] using (div_le_one hU0).mpr hU
  simpa only [_root_.P3ActualLogAdapterSourceOnly.innerMultiplier, norm_mul,
    _root_.P3ActualLogAdapterSourceOnly.norm_innerPhase, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hU0.le)] using hi

/-- Original gamma2(q*t) remains outside the branch conjugation. -/
theorem actualModeLambda_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)] (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) {t : ℕ}
    (ht : t ∈ baseCarrier e (D/delta)) :
    ‖actualModeLambda e D delta g l m negative u k t‖ ≤ 1 := by
  have hs := baseCarrier_original_window ht
  have hg : ‖e.gamma2 (D/delta*t)‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h2, _⟩ := he
    exact (h2 _ hs).1
  have hi := original_innerMultiplier_norm_le he hs m.2
  simp only [actualModeLambda, commonLambda,
    ActualLogModePacketInstanceSourceOnly.modeW, norm_mul,
    norm_branch_eq, norm_rootT_eq, mul_one]
  exact (mul_le_mul hg hi (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Includes the shortened signed h block AND root residue indicator. -/
theorem actualModeOmega_norm_le (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (k : ZMod (g*l)) (h : ℤ) :
    ‖actualModeOmega e D g l Z tag m negative k h‖ ≤ 1 := by
  unfold actualModeOmega commonOmega
  split_ifs
  · simpa only [ActualLogModePacketInstanceSourceOnly.modeOmega, norm_branch_eq] using
      _root_.P3ActualLogAdapterSourceOnly.norm_hMode_le e D Z tag h m.2
  all_goals simp only [norm_zero, zero_le_one]

/-- Literal nonzero part of the completed mode's source, before any
counting enlargement. y=0 remains in the separate existing zeroSource. -/
def actualNonzeroSource (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (negative : Bool) : Finset Source :=
  nonzeroSource (carrier (g*l) (signedResidue negative e.residue)
    (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
    (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g))))

/-- The positive count is on the SAME joint (z,y) fibers. In particular
the auxiliary divisor tests y=f*k, not z or either factor separately. -/
def actualCountEnergy (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (negative : Bool) (nu : ℕ) : ℝ :=
  let U := actualNonzeroSource e D delta g l Z negative
  ∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
    ((fiber U zy).card : ℝ)^2 else 0

section ActualMode
variable {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
variable (he : MediumAdmissible B sigma kappa c0 e)
variable (D delta g l : ℕ) [NeZero (g*l)] (Z : ℝ)
variable (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
variable (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))

include he

private theorem actual_weight_norm_le {s : Source}
    (hs : s ∈ actualNonzeroSource e D delta g l Z negative) :
    ‖weight (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) s‖ ≤ 1 := by
  have hc := (mem_filter.mp hs).1
  have hr := (mem_filter.mp hc).1
  have hp := mem_product.mp (mem_product.mp hr).2
  have ht1 := (mem_product.mp hp.1).1
  have ht2 := (mem_product.mp hp.2).1
  have h1 := actualModeLambda_norm_le he D delta g l m negative u k ht1
  have h2 := actualModeLambda_norm_le he D delta g l m negative u k ht2
  have hh1 := actualModeOmega_norm_le e D g l Z tag m negative k s.2.1.2
  have hh2 := actualModeOmega_norm_le e D g l Z tag m negative k s.2.2.2
  have ha1 : ‖atomCoeff (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) s.2.1‖ ≤ 1 := by
    rw [atomCoeff, norm_mul]
    exact (mul_le_mul h1 hh1 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have ha2 : ‖atomCoeff (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) s.2.2‖ ≤ 1 := by
    rw [atomCoeff, norm_mul]
    exact (mul_le_mul h2 hh2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  rw [weight, norm_mul, norm_star]
  exact (mul_le_mul ha1 ha2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The actual complex weighted coefficient is dominated by the literal
positive count; all mode and original unit/block masks stay on the left. -/
theorem actual_beta_norm_le_count (zy : Output) :
    ‖beta (actualNonzeroSource e D delta g l Z negative)
      (actualModeLambda e D delta g l m negative u k)
      (actualModeOmega e D g l Z tag m negative k) zy‖ ≤
        ((fiber (actualNonzeroSource e D delta g l Z negative) zy).card : ℝ) := by
  unfold beta
  calc
    _ ≤ ∑ s ∈ fiber (actualNonzeroSource e D delta g l Z negative) zy,
        ‖weight (actualModeLambda e D delta g l m negative u k)
          (actualModeOmega e D g l Z tag m negative k) s‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ fiber (actualNonzeroSource e D delta g l Z negative) zy, (1 : ℝ) := by
      apply sum_le_sum
      intro s hs
      exact actual_weight_norm_le he D delta g l Z tag m negative u k (mem_filter.mp hs).1
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one]

/-- Genuine Eq23 intake: no assumed B_nu, carrier embedding, or norm
supplier. The sharp 576/nu counting bound is a SEPARATE remaining step. -/
theorem actual_beta_energy_le_positive_count (nu : ℕ) :
    let U := actualNonzeroSource e D delta g l Z negative
    (∑ zy ∈ U.image output, if (nu : ℤ) ∣ zy.2 then
      ‖beta U (actualModeLambda e D delta g l m negative u k)
        (actualModeOmega e D g l Z tag m negative k) zy‖^2 else 0) ≤
      actualCountEnergy e D delta g l Z negative nu := by
  dsimp only
  unfold actualCountEnergy
  dsimp only
  apply sum_le_sum
  intro zy _
  by_cases hd : (nu : ℤ) ∣ zy.2
  · simp only [if_pos hd]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (actual_beta_norm_le_count he D delta g l Z tag m negative u k zy) 2
  · simp only [if_neg hd, le_refl]

end ActualMode
end
end ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly
