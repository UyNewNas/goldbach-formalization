import ImbalancedChen.CurrentChenUpsilon6OrdinarySieveKernel
import ImbalancedChen.P5U6RunboProductSlices
import ImbalancedChen.P5U6RunboBufferLimit

/-!
SOURCE_ONLY / UNCOMPILED. Auxiliary a-denominator finite-floor model only.
The two additional imports are the adjacent source-only drafts; they must be
installed under those module names before any later authorized compilation.

The finite floor below is defined from supplied knot and coefficient data.
The functions auxiliaryEnhancement and auxiliaryEnhancedKernel use denominator
a and are purely auxiliary algebraic models. They are NOT the original
manuscript h248 enhancement, whose denominator is R=a*s. The original model
and adopted binding are in P5U6AdoptedH248Binding.lean. Its finite integration
here is genuine reciprocal mass on true affine profile bands.
No Row00..31 data, shared coordinate API or adopted numerical endpoint is used.
-/

namespace ImbalancedChen.P5U6RunboEnhancedFloorInterfaceSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

abbrev Point := Fin 2 → ℝ

def reciprocal (x : Point) : ℝ := 1 / (x 0 * x 1)

theorem profile_range {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    currentChenUpsilon6OrdinaryProfile x ∈ Icc (2 : ℝ) (1323 / 417) := by
  constructor
  · exact (currentChenUpsilon6OrdinaryProfile_mem_firstInterval heta hx).1
  · obtain ⟨ha, _, hh, _⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1
    unfold currentChenUpsilon6OrdinaryProfile
    norm_num
    linarith

/-- The upper endpoint is attained at the literal lower corner, so 1323/417
is the exact upper bound on the unbuffered corrected domain. -/
theorem profile_upper_attained :
    ∃ x ∈ currentChenUpsilon6LogDomain 0,
      currentChenUpsilon6OrdinaryProfile x = (1323 / 417 : ℝ) := by
  refine ⟨![(417 / 5000 : ℝ), 19 / 125], ?_, ?_⟩
  · constructor
    · rw [mem_currentChenUpsilon6LogRectangle]
      norm_num
    · change (417 / 5000 : ℝ) + (19 / 125 : ℝ) ≤ (833 / 2500 : ℝ) - 0
      norm_num
  · norm_num [currentChenUpsilon6OrdinaryProfile]

/-- The original normalized continuous linear lower factor is wholly inside
its exact logarithmic interval, including s=2 at the corrected product wall. -/
theorem linear_lower_factor_eq_log {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    suzukiContinuousLowerFactor (currentChenUpsilon6OrdinaryProfile x) =
      2 * Real.exp Real.eulerMascheroniConstant *
        Real.log (currentChenUpsilon6OrdinaryProfile x - 1) /
          currentChenUpsilon6OrdinaryProfile x := by
  have hp := profile_range heta hx
  have hp4 : currentChenUpsilon6OrdinaryProfile x ≤ 4 := hp.2.trans (by norm_num)
  rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract hp.1 hp4,
    suzukiLowerSieveFactorFirstInterval_eq_log hp.1 hp4,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]

def profileBand (lo hi : ℝ) : Set Point :=
  {x | currentChenUpsilon6OrdinaryProfile x ∈ Ico lo hi}

theorem measurableSet_profileBand (lo hi : ℝ) : MeasurableSet (profileBand lo hi) := by
  have hc : Continuous currentChenUpsilon6OrdinaryProfile := by
    unfold currentChenUpsilon6OrdinaryProfile
    fun_prop
  exact measurableSet_Ico.preimage hc.measurable

/-- A half-open profile interval is exactly this slanted sum band. The upper
profile endpoint becomes a strict lower sum wall, and the lower one weak. -/
theorem profileBand_eq_slanted (lo hi : ℝ) :
    profileBand lo hi = {x : Point |
      (1 / 2 : ℝ) - (417 / 5000 : ℝ) * hi < x 0 + x 1 ∧
        x 0 + x 1 ≤ (1 / 2 : ℝ) - (417 / 5000 : ℝ) * lo} := by
  ext x
  change (lo ≤ currentChenUpsilon6OrdinaryProfile x ∧
    currentChenUpsilon6OrdinaryProfile x < hi) ↔ _
  unfold currentChenUpsilon6OrdinaryProfile
  constructor
  · rintro ⟨hl, hh⟩
    constructor <;> norm_num at * <;> linarith
  · rintro ⟨hh, hl⟩
    constructor <;> norm_num at * <;> linarith

/-- Proper adjacent table intervals have disjoint pullbacks; a shared knot
is owned only by the interval whose lower endpoint is that knot. -/
theorem profileBand_disjoint {lo₁ hi₁ lo₂ hi₂ : ℝ} (horder : hi₁ ≤ lo₂) :
    Disjoint (profileBand lo₁ hi₁) (profileBand lo₂ hi₂) := by
  apply Set.disjoint_left.mpr
  intro x hx₁ hx₂
  have hh : currentChenUpsilon6OrdinaryProfile x < hi₁ := hx₁.2
  have hl : lo₂ ≤ currentChenUpsilon6OrdinaryProfile x := hx₂.1
  linarith

/-- A literal finite floor function with adjacent knot intervals. Monotonic
knots are not needed for the exact sum identity; actual table binding remains
a separate obligation, rather than being silently asserted by this definition. -/
def finiteFloor {n : ℕ} (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin n, if s ∈ Ico (knots i.castSucc) (knots i.succ) then c i else 0

def auxiliaryEnhancement (h : ℝ → ℝ) (x : Point) : ℝ :=
  4 * h (currentChenUpsilon6OrdinaryProfile x) /
    ((417 / 5000 : ℝ) * x 0 * x 1)

def auxiliaryEnhancedKernel (h : ℝ → ℝ) (x : Point) : ℝ :=
  currentChenUpsilon6OrdinaryKernel x + auxiliaryEnhancement h x

theorem enhancement_finiteFloor_eq_sum {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (x : Point) :
    auxiliaryEnhancement (finiteFloor knots c) x =
      ∑ i : Fin n, (4 * c i / (417 / 5000 : ℝ)) *
        (profileBand (knots i.castSucc) (knots i.succ)).indicator reciprocal x := by
  unfold auxiliaryEnhancement finiteFloor
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : currentChenUpsilon6OrdinaryProfile x ∈
      Ico (knots i.castSucc) (knots i.succ)
  · have hx : x ∈ profileBand (knots i.castSucc) (knots i.succ) := hi
    rw [if_pos hi, indicator_of_mem hx]
    unfold reciprocal
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · have hx : x ∉ profileBand (knots i.castSucc) (knots i.succ) := hi
    rw [if_neg hi, indicator_of_notMem hx]
    ring

theorem integrableOn_bandReciprocal (lo hi : ℝ) :
    IntegrableOn ((profileBand lo hi).indicator reciprocal)
      currentChenUpsilon6LogRectangle :=
  integrableOn_currentChenUpsilon6LogRectangle.indicator (measurableSet_profileBand lo hi)

theorem integrableOn_floorEnhancement {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    IntegrableOn (auxiliaryEnhancement (finiteFloor knots c)) currentChenUpsilon6LogRectangle := by
  have heq : auxiliaryEnhancement (finiteFloor knots c) = fun x =>
      ∑ i : Fin n, (4 * c i / (417 / 5000 : ℝ)) *
        (profileBand (knots i.castSucc) (knots i.succ)).indicator reciprocal x := by
    funext x
    exact enhancement_finiteFloor_eq_sum knots c x
  rw [heq]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (integrableOn_bandReciprocal (knots i.castSucc) (knots i.succ)).const_mul _)

/-- The complete finite auxiliaryEnhancement integral is the sum of true reciprocal
masses of the slanted bands, with all factors 4/a retained exactly once. -/
theorem integral_floorEnhancement_eq_band_sum {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta, auxiliaryEnhancement (finiteFloor knots c) x) =
      ∑ i : Fin n, (4 * c i / (417 / 5000 : ℝ)) *
        ∫ x in currentChenUpsilon6LogDomain eta ∩
          profileBand (knots i.castSucc) (knots i.succ), reciprocal x := by
  simp_rw [enhancement_finiteFloor_eq_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    ((integrableOn_bandReciprocal (knots i.castSucc) (knots i.succ)).const_mul
      (4 * c i / (417 / 5000 : ℝ))).mono_set inter_subset_left)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, setIntegral_indicator (measurableSet_profileBand _ _)]

/-- Full enhanced integral additivity is justified by actual integrability
of every finite-floor term, with no enhanced-integrability hypothesis. -/
theorem integral_enhancedFloor_eq_ordinary_add {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta, auxiliaryEnhancedKernel (finiteFloor knots c) x) =
      (∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x) +
        ∑ i : Fin n, (4 * c i / (417 / 5000 : ℝ)) *
          ∫ x in currentChenUpsilon6LogDomain eta ∩
            profileBand (knots i.castSucc) (knots i.succ), reciprocal x := by
  unfold auxiliaryEnhancedKernel
  rw [integral_add (integrableOn_currentChenUpsilon6OrdinaryKernel_domain eta)
    ((integrableOn_floorEnhancement knots c).mono_set inter_subset_left),
    integral_floorEnhancement_eq_band_sum]

theorem finiteFloor_nonneg {n : ℕ} (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (s : ℝ) : 0 ≤ finiteFloor knots c s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hc i
  · exact le_rfl

theorem enhancement_nonneg {n : ℕ} (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) {x : Point} (hx : x ∈ currentChenUpsilon6LogRectangle) :
    0 ≤ auxiliaryEnhancement (finiteFloor knots c) x := by
  obtain ⟨h0, h1⟩ := currentChenUpsilon6LogRectangle_coordinates_pos hx
  unfold auxiliaryEnhancement
  exact div_nonneg (mul_nonneg (by norm_num) (finiteFloor_nonneg knots c hc _))
    (mul_nonneg (mul_nonneg (by norm_num) h0.le) h1.le)

/-- Nonnegative table entries yield a genuine nonnegative integral gain on
the corrected domain; this is an analytic statement about the defined table. -/
theorem ordinary_integral_le_enhancedFloor {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x) ≤
      ∫ x in currentChenUpsilon6LogDomain eta, auxiliaryEnhancedKernel (finiteFloor knots c) x := by
  have hnonneg : 0 ≤ ∫ x in currentChenUpsilon6LogDomain eta,
      auxiliaryEnhancement (finiteFloor knots c) x := by
    apply setIntegral_nonneg (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta)
    intro x hx
    exact enhancement_nonneg knots c hc hx.1
  unfold auxiliaryEnhancedKernel
  rw [integral_add (integrableOn_currentChenUpsilon6OrdinaryKernel_domain eta)
    ((integrableOn_floorEnhancement knots c).mono_set inter_subset_left)]
  exact le_add_of_nonneg_right hnonneg

/-- Each individual floor band's true integral has the original corrected
Runbo moving slices, by the previously written volume-preserving Fubini step. -/
theorem integral_floorBand_eq_nested (lo hi eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta ∩ profileBand lo hi, reciprocal x) =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        ∫ t in P5U6RunboProductSlicesSourceOnly.productSlice eta u,
          (profileBand lo hi).indicator reciprocal ![u, t] := by
  rw [← setIntegral_indicator (measurableSet_profileBand lo hi)]
  exact P5U6RunboProductSlicesSourceOnly.integral_productDomain_eq_nested eta
    ((profileBand lo hi).indicator reciprocal) (integrableOn_bandReciprocal lo hi)

/-- The finite enhanced kernel has its own proved buffer limit. This uses
the general fixed-integrable-kernel DCT, not an assumed h248 buffer estimate. -/
theorem tendsto_enhancedFloor_integral {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    Tendsto (fun eta : ℝ => ∫ x in currentChenUpsilon6LogDomain eta,
      auxiliaryEnhancedKernel (finiteFloor knots c) x) (𝓝 0)
        (𝓝 (∫ x in currentChenUpsilon6LogDomain 0, auxiliaryEnhancedKernel (finiteFloor knots c) x)) := by
  exact P5U6RunboBufferLimitSourceOnly.tendsto_integral_productDomain
    (auxiliaryEnhancedKernel (finiteFloor knots c))
    (integrableOn_currentChenUpsilon6OrdinaryKernel.add (integrableOn_floorEnhancement knots c))

end

end ImbalancedChen.P5U6RunboEnhancedFloorInterfaceSourceOnly
