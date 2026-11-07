import ImbalancedChen.ActualThirdOriginalLocalCurvature
import ImbalancedChen.RosserContinuousSourceUniformity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

The right-continuous extension of the literal Suzuki upper factor at one.
No assertion is made that the totalized source-tsum definition at one has
the right endpoint value.  All identifications with the actual kernel have
the strict hypothesis s > 1.  The extension is continuous and bounded on
the CLOSED legal domain, and its max-one extension is continuous on every
positive coordinate box.  No discrete residual mean is an input.
-/

namespace ImbalancedChen.P1FourthNearOneKernel

noncomputable section
open Set Filter Topology MeasureTheory
open scoped Classical BigOperators
open MathlibNt.SieveTheory
open OriginalU2CoupledRecurrenceSourceOnly

/-- A splice strictly inside the known initial strip. -/
def closedUpper (s : ℝ) : ℝ :=
  if s ≤ 2 then A / s else suzukiContinuousUpperFactor s

theorem upper_initial {s : ℝ} (hs : 1 < s) (hs3 : s ≤ 3) :
    suzukiContinuousUpperFactor s = A / s := by
  have h := upper_eq_inv hs hs3
  change suzukiContinuousUpperFactor s / A = 1 / s at h
  have h' := (div_eq_iff (ne_of_gt A_pos)).mp h
  calc
    suzukiContinuousUpperFactor s = (1 / s) * A := h'
    _ = A / s := by ring

theorem closedUpper_eq_actual {s : ℝ} (hs : 1 < s) :
    closedUpper s = suzukiContinuousUpperFactor s := by
  by_cases hs2 : s ≤ 2
  · simp only [closedUpper, if_pos hs2]
    exact (upper_initial hs (by linarith)).symm
  · simp only [closedUpper, if_neg hs2]

@[simp] theorem closedUpper_one : closedUpper 1 = A := by
  norm_num [closedUpper]

/-- Continuity includes the endpoint one; the closed splice is at two. -/
theorem continuousOn_closedUpper : ContinuousOn closedUpper (Ici 1) := by
  have hleft : ContinuousOn closedUpper (Icc 1 2) := by
    have hbase : ContinuousOn (fun s : ℝ => A / s) (Icc 1 2) :=
      continuousOn_const.div continuousOn_id
        (fun s hs => (show (0 : ℝ) < s by linarith [hs.1]).ne')
    apply hbase.congr
    intro s hs
    simp only [closedUpper, if_pos hs.2]
  have hright : ContinuousOn closedUpper (Ici 2) := by
    apply (continuousOn_suzukiContinuousUpperFactor.mono
      (fun s hs => (show (1 : ℝ) < s by linarith [hs]))).congr
    intro s hs
    exact closedUpper_eq_actual (by linarith [hs])
  have hu : Icc (1 : ℝ) 2 ∪ Ici 2 = Ici 1 := by
    ext s
    simp only [mem_union, mem_Icc, mem_Ici]
    constructor
    · rintro (⟨h, _⟩ | h) <;> linarith
    · intro h
      by_cases h2 : s ≤ 2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (le_of_not_ge h2)
  rw [← hu]
  exact hleft.union_of_isClosed hright isClosed_Icc isClosed_Ici

theorem tendsto_closedUpper_one :
    Tendsto closedUpper (𝓝[>] 1) (𝓝 A) := by
  have h : ContinuousWithinAt closedUpper (Ioi 1) 1 :=
    (continuousOn_closedUpper 1 (by simp)).mono (fun _ hs => hs.le)
  change Tendsto closedUpper (𝓝[>] 1) (𝓝 (closedUpper 1)) at h
  simpa only [closedUpper_one] using h

/-- Endpoint limit of the real source on its actual legal domain. -/
theorem tendsto_actualUpper_one :
    Tendsto suzukiContinuousUpperFactor (𝓝[>] 1) (𝓝 A) := by
  apply tendsto_closedUpper_one.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact closedUpper_eq_actual hs

theorem tendsto_actualUpper_div_one (u : ℝ) :
    Tendsto (fun s : ℝ => suzukiContinuousUpperFactor s / u)
      (𝓝[>] 1) (𝓝 (A / u)) :=
  tendsto_actualUpper_one.div_const u

theorem normalization :
    (2 * Real.exp (-Real.eulerMascheroniConstant)) * A = 4 := by
  calc
    (2 * Real.exp (-Real.eulerMascheroniConstant)) * A =
        4 * (Real.exp (-Real.eulerMascheroniConstant) *
          Real.exp Real.eulerMascheroniConstant) := by unfold A; ring
    _ = 4 := by rw [← Real.exp_add]; simp

theorem closedUpper_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ closedUpper s := by
  by_cases hs2 : s ≤ 2
  · simp only [closedUpper, if_pos hs2]
    exact div_nonneg A_pos.le (by linarith)
  · rw [closedUpper_eq_actual (by linarith)]
    unfold suzukiContinuousUpperFactor
      MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiProposition118SourceTPlus
    exact add_nonneg (by norm_num) (tsum_nonneg (fun k =>
      MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer_one_two_odd_nonneg
        (by linarith) k))

/-- A global bound, without an upper bound on s. -/
theorem closedUpper_le_amplitude {s : ℝ} (hs : 1 ≤ s) : closedUpper s ≤ A := by
  by_cases hs2 : s ≤ 2
  · simp only [closedUpper, if_pos hs2]
    exact (div_le_iff₀ (show 0 < s by linarith)).mpr
      (by nlinarith [A_pos])
  · have hs2' : 2 ≤ s := le_of_not_ge hs2
    have h := upper_antitone (show (2 : ℝ) ∈ Ici 2 from le_rfl) hs2' hs2'
    rw [upper_eq_inv (by norm_num) (by norm_num)] at h
    change suzukiContinuousUpperFactor s / A ≤ 1 / 2 at h
    have h' := (div_le_iff₀ A_pos).mp h
    rw [closedUpper_eq_actual (by linarith)]
    nlinarith [A_pos]

def residual (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  (lambda - ∑ i, t i) / t (Fin.last 3)

/-- The exact normalized literal profile, with the endpoint filled in. -/
def normalized (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  closedUpper (residual lambda t) / t (Fin.last 3)

def density (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant)) * normalized lambda t

def legal (a lambda : ℝ) : Set (Fin 4 → ℝ) :=
  {t | a ≤ t (Fin.last 3) ∧ (∑ i, t i) + t (Fin.last 3) ≤ lambda}

theorem isClosed_legal (a lambda : ℝ) : IsClosed (legal a lambda) := by
  have hlast : Continuous (fun t : Fin 4 → ℝ => t (Fin.last 3)) := by fun_prop
  have hsumlast : Continuous (fun t : Fin 4 → ℝ => (∑ i, t i) + t (Fin.last 3)) := by
    fun_prop
  exact (isClosed_le continuous_const hlast).inter
    (isClosed_le hsumlast continuous_const)

theorem residual_one_le {a lambda : ℝ} (ha : 0 < a) {t : Fin 4 → ℝ}
    (ht : t ∈ legal a lambda) : 1 ≤ residual lambda t := by
  apply (le_div_iff₀ (ha.trans_le ht.1)).mpr
  dsimp only [residual]
  linarith [ht.2]

theorem continuousOn_normalized {a lambda : ℝ} (ha : 0 < a) :
    ContinuousOn (normalized lambda) (legal a lambda) := by
  have hlast : Continuous (fun t : Fin 4 → ℝ => t (Fin.last 3)) := by fun_prop
  have hsum : Continuous (fun t : Fin 4 → ℝ => ∑ i, t i) := by fun_prop
  have hne : ∀ t ∈ legal a lambda, t (Fin.last 3) ≠ 0 :=
    fun t ht => (ha.trans_le ht.1).ne'
  have hr : ContinuousOn (residual lambda) (legal a lambda) :=
    (continuousOn_const.sub hsum.continuousOn).div hlast.continuousOn hne
  exact (continuousOn_closedUpper.comp hr
    (fun t ht => residual_one_le ha ht)).div hlast.continuousOn hne

theorem continuousOn_density {a lambda : ℝ} (ha : 0 < a) :
    ContinuousOn (density lambda) (legal a lambda) :=
  continuousOn_const.mul (continuousOn_normalized ha)

/-- The closed-domain normalized bound needs only t4 >= a and s >= 1. -/
theorem abs_normalized_le {a lambda : ℝ} (ha : 0 < a) {t : Fin 4 → ℝ}
    (ht : t ∈ legal a lambda) : |normalized lambda t| ≤ A / a := by
  have hp := ha.trans_le ht.1
  have hs := residual_one_le ha ht
  rw [normalized, abs_of_nonneg (div_nonneg (closedUpper_nonneg hs) hp.le)]
  exact (div_le_div_of_nonneg_right (closedUpper_le_amplitude hs) hp.le).trans
    (div_le_div_of_nonneg_left A_pos.le ha ht.1)

theorem abs_density_le {a lambda : ℝ} (ha : 0 < a) {t : Fin 4 → ℝ}
    (ht : t ∈ legal a lambda) : |density lambda t| ≤ 4 / a := by
  rw [density, abs_mul, abs_of_pos (show 0 < 2 *
    Real.exp (-Real.eulerMascheroniConstant) by positivity)]
  calc
    (2 * Real.exp (-Real.eulerMascheroniConstant)) * |normalized lambda t| ≤
        (2 * Real.exp (-Real.eulerMascheroniConstant)) * (A / a) :=
      mul_le_mul_of_nonneg_left (abs_normalized_le ha ht) (by positivity)
    _ = 4 / a := by rw [← mul_div_assoc, normalization]

theorem normalized_eq_actual (lambda : ℝ) (t : Fin 4 → ℝ)
    (hs : 1 < residual lambda t) :
    normalized lambda t =
      suzukiContinuousUpperFactor ((lambda - ∑ i, t i) / t (Fin.last 3)) /
        t (Fin.last 3) := by
  rw [normalized, closedUpper_eq_actual hs]
  rfl

/-- The literal dictionary profile is recovered at every strict legal tuple. -/
theorem density_eq_actual (lambda : ℝ) (t : Fin 4 → ℝ)
    (hs : 1 < residual lambda t) :
    density lambda t =
      (2 * Real.exp (-Real.eulerMascheroniConstant) / t (Fin.last 3)) *
        suzukiContinuousUpperFactor ((lambda - ∑ i, t i) / t (Fin.last 3)) := by
  rw [density, normalized, closedUpper_eq_actual hs]
  dsimp only [residual]
  ring

theorem normalized_at_wall {lambda : ℝ} {t : Fin 4 → ℝ}
    (hwall : residual lambda t = 1) : normalized lambda t = A / t (Fin.last 3) := by
  simp only [normalized, hwall, closedUpper_one]

theorem density_at_wall {lambda : ℝ} {t : Fin 4 → ℝ}
    (hwall : residual lambda t = 1) : density lambda t = 4 / t (Fin.last 3) := by
  rw [density, normalized_at_wall hwall, ← mul_div_assoc, normalization]

/-- Any compact part of the closed legal domain has an integrable real kernel. -/
theorem integrableOn_normalized_compact {a lambda : ℝ} (ha : 0 < a)
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) (hlegal : K ⊆ legal a lambda) :
    IntegrableOn (normalized lambda) K :=
  ((continuousOn_normalized ha).mono hlegal).integrableOn_compact hK

theorem integrableOn_density_compact {a lambda : ℝ} (ha : 0 < a)
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) (hlegal : K ⊆ legal a lambda) :
    IntegrableOn (density lambda) K :=
  ((continuousOn_density ha).mono hlegal).integrableOn_compact hK

theorem integrableOn_density_legalBox {a b lambda : ℝ} (ha : 0 < a) :
    IntegrableOn (density lambda)
      (univ.pi (fun _ : Fin 4 => Icc a b) ∩ legal a lambda) :=
  integrableOn_density_compact ha
    ((isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right (isClosed_legal a lambda))
    (fun _ ht => ht.2)

/-- Global positive-coordinate extension for compact-box integration. -/
def maxOneNormalized (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  closedUpper (max 1 (residual lambda t)) / t (Fin.last 3)

theorem maxOneNormalized_eq {a lambda : ℝ} (ha : 0 < a) {t : Fin 4 → ℝ}
    (ht : t ∈ legal a lambda) : maxOneNormalized lambda t = normalized lambda t := by
  simp only [maxOneNormalized, normalized, max_eq_right (residual_one_le ha ht)]

theorem continuousOn_maxOneNormalized {a b lambda : ℝ} (ha : 0 < a) :
    ContinuousOn (maxOneNormalized lambda)
      (univ.pi (fun _ : Fin 4 => Icc a b)) := by
  have hlast : Continuous (fun t : Fin 4 → ℝ => t (Fin.last 3)) := by fun_prop
  have hsum : Continuous (fun t : Fin 4 → ℝ => ∑ i, t i) := by fun_prop
  have hne : ∀ t ∈ univ.pi (fun _ : Fin 4 => Icc a b), t (Fin.last 3) ≠ 0 :=
    fun t ht => (ha.trans_le (ht _ (mem_univ _)).1).ne'
  have hr : ContinuousOn (residual lambda) (univ.pi (fun _ : Fin 4 => Icc a b)) :=
    (continuousOn_const.sub hsum.continuousOn).div hlast.continuousOn hne
  exact (continuousOn_closedUpper.comp (continuousOn_const.sup hr)
    (fun t _ => le_max_left _ _)).div hlast.continuousOn hne

theorem integrableOn_maxOneNormalized {a b lambda : ℝ} (ha : 0 < a) :
    IntegrableOn (maxOneNormalized lambda)
      (univ.pi (fun _ : Fin 4 => Icc a b)) :=
  (continuousOn_maxOneNormalized ha).integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))

end
end ImbalancedChen.P1FourthNearOneKernel
