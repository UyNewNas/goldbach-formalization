import Mathlib
import ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily
import ImbalancedChen.Part3TwoLongContinuousModeReconstruction
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual original admissible all-rank Family, its per-group psi and
complete-product eta, and literal HB dyadic blocks determine the compact
log-chart below. Fourier coefficients are constructed on EuclideanSpace,
not by installing an incompatible inner product on ordinary Pi space.
The physical frequency measure is explicitly the pushforward xi=2*pi*nu;
this keeps the precise inverse normalization without a hidden Jacobian.
-/

namespace ImbalancedChen.Part3.ActualHBCompactLogChart
noncomputable section
open Classical Set Filter MeasureTheory FourierTransform SchwartzMap
open scoped BigOperators Topology FourierTransform SchwartzMap RealInnerProductSpace
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
open ImbalancedChen.P5Z.HBRightClosedDyadicRoles
open ImbalancedChen.P5Z.ActualHBDyadicProductWindow
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongContinuousModeReconstruction
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b
open ImbalancedChen.Part3.TwoLongJointSharpStripDiscrepancy

/-- Exact input data from the original smooth test class and its HB chart.
No arithmetic discrepancy or Fourier-reconstruction conclusion is a field. -/
structure OriginalChart (kStar r : ℕ) where
  family : Family kStar
  target : ℕ
  rank : Fin (kStar + 1)
  chi eta : ℝ → ℝ
  chi_smooth : ContDiff ℝ ∞ chi
  eta_smooth : ContDiff ℝ ∞ eta
  kappa0 : ℝ
  groupScale : Fin rank.val → ℝ
  slots : Fin rank.val → Finset (Fin r)
  blocks : Fin r → Block

def occurrenceScale {K r : ℕ} (C : OriginalChart K r) (a : Fin r) : ℝ :=
  lower (C.blocks a)

theorem occurrenceScale_pos {K r : ℕ} (C : OriginalChart K r) (a : Fin r) :
    0 < occurrenceScale C a := by exact_mod_cast lower_pos (C.blocks a)

/-- The literal smooth geometric factor, retaining every original psi,
eta of the COMPLETE product, and the same Family integer extension. -/
def rawHB {K r : ℕ} (C : OriginalChart K r) (v : Fin r → ℝ) : ℝ :=
  chartAmbient (licence C.family C.target C.rank) C.chi C.eta
    (C.target : ℝ) C.kappa0 C.groupScale (groupedProducts C.slots v)

theorem rawHB_smooth {K r : ℕ} (C : OriginalChart K r) : ContDiff ℝ ∞ (rawHB C) :=
  smooth_hb_pullback C.family C.target C.rank C.chi C.eta
    C.chi_smooth C.eta_smooth C.kappa0 C.groupScale C.slots

def liftLog {K r : ℕ} (C : OriginalChart K r) (z : Fin r → ℝ) : Fin r → ℝ :=
  fun a => occurrenceScale C a * Real.exp (z a)

def logCutoff {r : ℕ} (z : Fin r → ℝ) : ℝ :=
  ∏ a, cutoff (Real.exp (z a))

/-- The finite occurrence cutoff is one on the entire literal dyadic
rectangle and compact in logarithmic coordinates in EVERY finite rank. -/
def logChartPi {K r : ℕ} (C : OriginalChart K r) (z : Fin r → ℝ) : ℂ :=
  ((rawHB C (liftLog C z) * logCutoff z : ℝ) : ℂ)

theorem logChartPi_smooth {K r : ℕ} (C : OriginalChart K r) :
    ContDiff ℝ ∞ (logChartPi C) := by
  have hLift : ContDiff ℝ ∞ (liftLog C) := by unfold liftLog; fun_prop
  have hcut : ContDiff ℝ ∞ (logCutoff (r := r)) := by
    have hc := cutoff_smooth
    unfold logCutoff
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp (((rawHB_smooth C).comp hLift).mul hcut)

theorem logChartPi_support {K r : ℕ} (C : OriginalChart K r) :
    Function.support (logChartPi C) ⊆
      Icc (fun _ : Fin r => Real.log (1 / 2 : ℝ))
        (fun _ : Fin r => Real.log (5 / 2 : ℝ)) := by
  intro z hz
  have hp : logCutoff z ≠ 0 := by
    intro h
    exact hz (by simp [logChartPi, h])
  have ha (a : Fin r) : Real.exp (z a) ∈ Icc (1 / 2 : ℝ) (5 / 2) :=
    cutoff_support ((Finset.prod_ne_zero_iff.mp hp) a (Finset.mem_univ a))
  constructor
  · intro a
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (ha a).1
    simpa only [Real.log_exp] using h
  · intro a
    have h := Real.log_le_log (Real.exp_pos (z a)) (ha a).2
    simpa only [Real.log_exp] using h

theorem logChartPi_compact {K r : ℕ} (C : OriginalChart K r) :
    HasCompactSupport (logChartPi C) := by
  change IsCompact (closure (Function.support (logChartPi C)))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (logChartPi_support C) isClosed_Icc)

abbrev E (r : ℕ) := EuclideanSpace ℝ (Fin r)

def coordEquiv (r : ℕ) : E r ≃L[ℝ] (Fin r → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℝ)

def logChart {K r : ℕ} (C : OriginalChart K r) : E r → ℂ :=
  logChartPi C ∘ coordEquiv r

theorem logChart_smooth {K r : ℕ} (C : OriginalChart K r) :
    ContDiff ℝ ∞ (logChart C) :=
  (logChartPi_smooth C).comp (coordEquiv r).contDiff

theorem logChart_compact {K r : ℕ} (C : OriginalChart K r) :
    HasCompactSupport (logChart C) :=
  (logChartPi_compact C).comp_homeomorph (coordEquiv r).toHomeomorph

/-- The Fourier coefficient is constructed from the actual chart, not
an arbitrary A with an assumed representation identity. -/
def chartFourier {K r : ℕ} (C : OriginalChart K r) : E r → ℂ := 𝓕 (logChart C)

theorem chartFourier_integrable {K r : ℕ} (C : OriginalChart K r) :
    Integrable (chartFourier C) := by
  let F : 𝓢(E r, ℂ) := (logChart_compact C).toSchwartzMap (logChart_smooth C)
  have hf := (𝓕 F).integrable
  simpa only [SchwartzMap.fourier_coe] using hf

theorem chartFourier_inverse {K r : ℕ} (C : OriginalChart K r) :
    𝓕⁻ (chartFourier C) = logChart C :=
  (logChart_smooth C).continuous.fourierInv_fourier_eq
    ((logChart_smooth C).continuous.integrable_of_hasCompactSupport (logChart_compact C))
    (chartFourier_integrable C)

/-- A typed physical-frequency change of variable; neither the norm on
Pi nor a Fourier normalization is silently altered. -/
def physicalFrequencyEquiv (r : ℕ) : E r ≃ᵐ (Fin r → ℝ) where
  toEquiv :=
    { toFun := fun nu a => (2 * Real.pi) * nu a
      invFun := fun xi => PiLp.toLp 2 (fun a => xi a / (2 * Real.pi))
      left_inv := by
        intro nu
        ext a
        change (2 * Real.pi * nu a) / (2 * Real.pi) = nu a
        field_simp [Real.pi_ne_zero]
      right_inv := by
        intro xi
        funext a
        change (2 * Real.pi) * (xi a / (2 * Real.pi)) = xi a
        field_simp [Real.pi_ne_zero] }
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

def physicalFrequencyMeasure (r : ℕ) : Measure (Fin r → ℝ) :=
  Measure.map (physicalFrequencyEquiv r) (volume : Measure (E r))

def physicalCoefficient {K r : ℕ} (C : OriginalChart K r) (xi : Fin r → ℝ) : ℂ :=
  chartFourier C ((physicalFrequencyEquiv r).symm xi)

theorem physicalCoefficient_integrable {K r : ℕ} (C : OriginalChart K r) :
    Integrable (physicalCoefficient C) (physicalFrequencyMeasure r) := by
  rw [physicalFrequencyMeasure, integrable_map_equiv]
  simpa only [Function.comp_def, physicalCoefficient, MeasurableEquiv.symm_apply_apply]
    using chartFourier_integrable C

/-- Exact L1 mass preservation under the physical-frequency pushforward. -/
theorem physicalCoefficient_L1 {K r : ℕ} (C : OriginalChart K r) :
    (∫ xi, ‖physicalCoefficient C xi‖ ∂physicalFrequencyMeasure r) =
      ∫ nu : E r, ‖chartFourier C nu‖ := by
  rw [physicalFrequencyMeasure, integral_map_equiv]
  simp only [physicalCoefficient, MeasurableEquiv.symm_apply_apply]

private theorem phase_product (r : ℕ) (nu : E r) (z : Fin r → ℝ) :
    (∏ a, Complex.exp (Complex.I * (((physicalFrequencyEquiv r) nu a) : ℂ) * (z a : ℂ))) =
      Complex.exp (((2 * Real.pi * ⟪nu, PiLp.toLp 2 z⟫_ℝ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  have hi : ⟪nu, PiLp.toLp 2 z⟫_ℝ = ∑ a : Fin r, nu a * z a := by
    simp [PiLp.inner_apply, RCLike.inner_apply]
  rw [hi]
  change (∑ a : Fin r, Complex.I * ((2 * Real.pi * nu a : ℝ) : ℂ) * (z a : ℂ)) = _
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Actual all-rank inverse Fourier representation with the precise
physical measure and the literal logarithmic occurrence phases. -/
theorem physicalCoefficient_inverse {K r : ℕ} (C : OriginalChart K r)
    (z : Fin r → ℝ) :
    (∫ xi, physicalCoefficient C xi *
      ∏ a, Complex.exp (Complex.I * (xi a : ℂ) * (z a : ℂ))
      ∂physicalFrequencyMeasure r) = logChartPi C z := by
  rw [physicalFrequencyMeasure, integral_map_equiv]
  simp only [physicalCoefficient, MeasurableEquiv.symm_apply_apply]
  simp_rw [phase_product]
  have hInv := congrFun (chartFourier_inverse C) (PiLp.toLp 2 z)
  rw [fourierInv_eq'] at hInv
  simpa only [smul_eq_mul, mul_comm, logChart, Function.comp_def,
    coordEquiv, PiLp.continuousLinearEquiv_apply, PiLp.ofLp_toLp] using hInv

/-- Integer occurrence coordinates from the SAME actual HB blocks. -/
def normalizedWord {K r : ℕ} (C : OriginalChart K r) (n : Fin r → ℕ) : Fin r → ℝ :=
  fun a => (n a : ℝ) / occurrenceScale C a

def wordLog {K r : ℕ} (C : OriginalChart K r) (n : Fin r → ℕ) : Fin r → ℝ :=
  fun a => Real.log (normalizedWord C n a)

theorem owned_normalized_mem {K r : ℕ} (C : OriginalChart K r) (n : Fin r → ℕ)
    (hn : ∀ a, Owns (C.blocks a) (n a)) (a : Fin r) :
    normalizedWord C n a ∈ Icc (1 : ℝ) 2 := by
  have hb := owns_bounds (hn a)
  have hU := occurrenceScale_pos C a
  constructor
  · apply (le_div_iff₀ hU).2
    exact_mod_cast hb.1
  · apply (div_le_iff₀ hU).2
    exact_mod_cast hb.2

theorem owned_logChart_identity {K r : ℕ} (C : OriginalChart K r) (n : Fin r → ℕ)
    (hn : ∀ a, Owns (C.blocks a) (n a)) :
    logChartPi C (wordLog C n) = ((rawHB C (fun a => (n a : ℝ)) : ℝ) : ℂ) := by
  have hpos (a : Fin r) : 0 < normalizedWord C n a :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (owned_normalized_mem C n hn a).1
  have hcut : logCutoff (wordLog C n) = 1 := by
    apply Finset.prod_eq_one
    intro a ha
    rw [wordLog, Real.exp_log (hpos a)]
    exact cutoff_one (owned_normalized_mem C n hn a)
  have hlift : liftLog C (wordLog C n) = fun a => (n a : ℝ) := by
    funext a
    rw [liftLog, wordLog, Real.exp_log (hpos a)]
    unfold normalizedWord
    field_simp [(occurrenceScale_pos C a).ne']
  simp [logChartPi, hcut, hlift]

/-- The original actual HB geometric coefficient is now the proved
inverse integral, rather than an unbound representation premise. -/
theorem owned_originalHB_inverse {K r : ℕ} (C : OriginalChart K r) (n : Fin r → ℕ)
    (hn : ∀ a, Owns (C.blocks a) (n a)) :
    (∫ xi, physicalCoefficient C xi * ∏ a, phase (xi a) (normalizedWord C n a)
      ∂physicalFrequencyMeasure r) = ((rawHB C (fun a => (n a : ℝ)) : ℝ) : ℂ) := by
  have h := physicalCoefficient_inverse C (wordLog C n)
  simpa only [phase, wordLog, owned_logChart_identity C n hn] using h

/-- On the actual owned dyadic rectangle, the batch-30b reconstructed
profile is EXACTLY the original all-rank HB geometric coefficient. -/
theorem owned_reconstructedProfile_identity {K r : ℕ}
    (C : OriginalChart K r) (n : Fin r → ℕ) (hn : ∀ a, Owns (C.blocks a) (n a))
    (i j : Fin r) (hij : i ≠ j) {d₁ d₂ u v : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hi : n i = d₁ * u) (hj : n j = d₂ * v) :
    reconstructedProfile (physicalFrequencyMeasure r) (physicalCoefficient C)
      (wordLog C n) i j (occurrenceScale C i) (occurrenceScale C j) d₁ d₂ (u,v) =
      ((rawHB C (fun a => (n a : ℝ)) : ℝ) : ℂ) := by
  have hratio₁ : (u : ℝ) / (occurrenceScale C i / d₁) = normalizedWord C n i := by
    unfold normalizedWord
    rw [hi, Nat.cast_mul]
    field_simp [(occurrenceScale_pos C i).ne', (by exact_mod_cast Nat.ne_of_gt hd₁ : (d₁ : ℝ) ≠ 0)]
    ring
  have hratio₂ : (v : ℝ) / (occurrenceScale C j / d₂) = normalizedWord C n j := by
    unfold normalizedWord
    rw [hj, Nat.cast_mul]
    field_simp [(occurrenceScale_pos C j).ne', (by exact_mod_cast Nat.ne_of_gt hd₂ : (d₂ : ℝ) ≠ 0)]
    ring
  unfold reconstructedProfile
  rw [hratio₁, hratio₂]
  calc
    _ = ∫ xi, physicalCoefficient C xi *
        ∏ a, phase (xi a) (normalizedWord C n a) ∂physicalFrequencyMeasure r := by
      apply integral_congr_ae
      filter_upwards with xi
      exact selected_fourier_mode_exact (physicalCoefficient C) xi (normalizedWord C n)
        i j hij (owned_normalized_mem C n hn i) (owned_normalized_mem C n hn j)
    _ = _ := owned_originalHB_inverse C n hn

/-- Insert the two literal Brun-scaled long integers in their original
occurrence positions; every other occurrence stays fixed before q. -/
def withLongs {r : ℕ} (n : Fin r → ℕ) (i j : Fin r)
    (d₁ d₂ : ℕ) (u : ℕ × ℕ) : Fin r → ℕ :=
  Function.update (Function.update n i (d₁*u.1)) j (d₂*u.2)

/-- Only the short occurrences enter the selected amplitude; replacing
the two long coordinates cannot alter that q-independent coefficient. -/
theorem selectedAmplitude_withLongs {K r : ℕ} (C : OriginalChart K r)
    (A : (Fin r → ℝ) → ℂ) (xi : Fin r → ℝ) (n : Fin r → ℕ)
    (i j : Fin r) (d₁ d₂ : ℕ) (u : ℕ × ℕ) :
    selectedAmplitude A xi (wordLog C (withLongs n i j d₁ d₂ u)) i j =
      selectedAmplitude A xi (wordLog C n) i j := by
  unfold selectedAmplitude
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  have haj : a ≠ j := (Finset.mem_erase.mp ha).1
  have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
  simp [wordLog, normalizedWord, withLongs, hai, haj]

def ownedCarrier {K r : ℕ} (C : OriginalChart K r) (i j : Fin r)
    (d₁ d₂ : ℕ) : Finset (ℕ × ℕ) :=
  ((wideWindow (occurrenceScale C i / d₁)).product
    (wideWindow (occurrenceScale C j / d₂))).filter
      (fun u => Owns (C.blocks i) (d₁*u.1) ∧ Owns (C.blocks j) (d₂*u.2))

theorem withLongs_owned {K r : ℕ} (C : OriginalChart K r)
    (n : Fin r → ℕ) (i j : Fin r) (hij : i ≠ j) (d₁ d₂ : ℕ)
    (hshort : ∀ a, a ≠ i → a ≠ j → Owns (C.blocks a) (n a))
    {u : ℕ × ℕ} (hu : u ∈ ownedCarrier C i j d₁ d₂) :
    ∀ a, Owns (C.blocks a) (withLongs n i j d₁ d₂ u a) := by
  have hlong := (Finset.mem_filter.mp hu).2
  intro a
  by_cases haj : a = j
  · subst a
    simpa [withLongs] using hlong.2
  · by_cases hai : a = i
    · subst a
      simpa [withLongs,hij] using hlong.1
    · simpa [withLongs,hai,haj] using hshort a hai haj

/-- The actual geometric HB coefficient, not an abstract beta with a
putative Fourier-representation hypothesis. -/
def ownedBeta {K r : ℕ} (C : OriginalChart K r) (n : Fin r → ℕ)
    (i j : Fin r) (d₁ d₂ : ℕ) (u : ℕ × ℕ) : ℂ :=
  ((rawHB C (fun a => (withLongs n i j d₁ d₂ u a : ℝ)) : ℝ) : ℂ)

theorem ownedBeta_reconstruction {K r : ℕ} (C : OriginalChart K r)
    (n : Fin r → ℕ) (i j : Fin r) (hij : i ≠ j) {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hshort : ∀ a, a ≠ i → a ≠ j → Owns (C.blocks a) (n a))
    {u : ℕ × ℕ} (hu : u ∈ ownedCarrier C i j d₁ d₂) :
    ownedBeta C n i j d₁ d₂ u =
      ∫ xi, modeIntegrand (physicalCoefficient C) (wordLog C n) i j
        ((u.1 : ℝ) / (occurrenceScale C i / d₁))
        ((u.2 : ℝ) / (occurrenceScale C j / d₂)) xi
        ∂physicalFrequencyMeasure r := by
  have hown := withLongs_owned C n i j hij d₁ d₂ hshort hu
  have hi : withLongs n i j d₁ d₂ u i = d₁*u.1 := by simp [withLongs,hij]
  have hj : withLongs n i j d₁ d₂ u j = d₂*u.2 := by simp [withLongs]
  have h := owned_reconstructedProfile_identity C (withLongs n i j d₁ d₂ u)
    hown i j hij hd₁ hd₂ hi hj
  unfold reconstructedProfile modeIntegrand at h
  simp_rw [selectedAmplitude_withLongs] at h
  exact h.symm


def shortProduct {r : ℕ} (n : Fin r → ℕ) (i j : Fin r) : ℕ :=
  ∏ a ∈ (Finset.univ.erase i).erase j, n a

/-- The complete arithmetic word in the kernel is the product of the
SAME original HB occurrence tuple, with its actual short product. -/
theorem withLongs_complete_product {r : ℕ} (n : Fin r → ℕ)
    (i j : Fin r) (hij : i ≠ j) (d₁ d₂ : ℕ) (u : ℕ × ℕ) :
    (∏ a, withLongs n i j d₁ d₂ u a) =
      (shortProduct n i j * d₁ * d₂) * u.1 * u.2 := by
  let F := withLongs n i j d₁ d₂ u
  have hj : j ∈ (Finset.univ : Finset (Fin r)).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ _⟩
  have hsplit : (∏ a, F a) = F i * F j *
      ∏ a ∈ (Finset.univ.erase i).erase j, F a := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin r)) F (Finset.mem_univ i),
      ← Finset.mul_prod_erase ((Finset.univ : Finset (Fin r)).erase i) F hj]
    ring
  have hshort : (∏ a ∈ (Finset.univ.erase i).erase j, F a) = shortProduct n i j := by
    apply Finset.prod_congr rfl
    intro a ha
    have haj : a ≠ j := (Finset.mem_erase.mp ha).1
    have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [F,withLongs,hai,haj]
  change (∏ a, F a) = _
  rw [hsplit,hshort]
  simp only [F,withLongs,Function.update_same,Function.update_of_ne hij]
  ring

/-- Exact original owned-rectangle geometric count/coprime-mean core.
The original strict-left/closed-right HB `Owns` is still visible. -/
def ownedGeometricCore {K r : ℕ} (C : OriginalChart K r) (n : Fin r → ℕ)
    (i j : Fin r) (m d₁ d₂ a q : ℕ) : ℂ :=
  physicalDiscrepancy (ownedCarrier C i j d₁ d₂) (fun _ => m*d₁*d₂)
    Prod.fst Prod.snd a q (ownedBeta C n i j d₁ d₂)

/-- The all-rank original HB coefficient is bound to the actual same-mean
core integral, not supplied via hUpperExact/hGapExact. The owned dyadic
indicator is deliberately retained until the proved strip sandwich is used. -/
theorem ownedGeometricCore_eq_integral {K r : ℕ} (C : OriginalChart K r)
    (n : Fin r → ℕ) (i j : Fin r) (hij : i ≠ j) (m a q : ℕ)
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hshort : ∀ a, a ≠ i → a ≠ j → Owns (C.blocks a) (n a)) :
    ownedGeometricCore C n i j m d₁ d₂ a q =
      ∫ xi, physicalDiscrepancy (ownedCarrier C i j d₁ d₂) (fun _ => m*d₁*d₂)
        Prod.fst Prod.snd a q (fun u => modeIntegrand (physicalCoefficient C)
          (wordLog C n) i j ((u.1 : ℝ)/(occurrenceScale C i/d₁))
            ((u.2 : ℝ)/(occurrenceScale C j/d₂)) xi)
        ∂physicalFrequencyMeasure r := by
  let R := ownedCarrier C i j d₁ d₂
  have hterm (u : ℕ × ℕ) : Integrable (fun xi =>
      residueWeight (m*d₁*d₂) a q u * modeIntegrand (physicalCoefficient C)
        (wordLog C n) i j ((u.1 : ℝ)/(occurrenceScale C i/d₁))
          ((u.2 : ℝ)/(occurrenceScale C j/d₂)) xi)
        (physicalFrequencyMeasure r) :=
    (modeIntegrand_integrable (physicalCoefficient C) (physicalCoefficient_integrable C)
      (wordLog C n) i j _ _).const_mul _
  calc
    _ = ∑ u ∈ R, residueWeight (m*d₁*d₂) a q u * ownedBeta C n i j d₁ d₂ u :=
      physicalDiscrepancy_eq_kernel _ _ _ _ _
    _ = ∑ u ∈ R, ∫ xi, residueWeight (m*d₁*d₂) a q u *
        modeIntegrand (physicalCoefficient C) (wordLog C n) i j
          ((u.1 : ℝ)/(occurrenceScale C i/d₁))
          ((u.2 : ℝ)/(occurrenceScale C j/d₂)) xi ∂physicalFrequencyMeasure r := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [ownedBeta_reconstruction C n i j hij hd₁ hd₂ hshort hu,integral_const_mul]
    _ = ∫ xi, ∑ u ∈ R, residueWeight (m*d₁*d₂) a q u *
        modeIntegrand (physicalCoefficient C) (wordLog C n) i j
          ((u.1 : ℝ)/(occurrenceScale C i/d₁))
          ((u.2 : ℝ)/(occurrenceScale C j/d₂)) xi ∂physicalFrequencyMeasure r :=
      (integral_finset_sum R (fun u hu => hterm u)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with xi
      exact (physicalDiscrepancy_eq_kernel _ _ _ _ _).symm


end
end ImbalancedChen.Part3.ActualHBCompactLogChart
