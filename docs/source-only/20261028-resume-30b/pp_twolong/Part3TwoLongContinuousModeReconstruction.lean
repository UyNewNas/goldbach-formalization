import Mathlib
import ImbalancedChen.Part3TwoLongLiteralMellinModes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Continuous-frequency N2 mass for the ACTUAL literal Mellin modes from
batch 30, followed by a finite AP-count / exact-coprime-mean Fubini
reconstruction. No P2 estimate and no three-core equality is assumed.
The reconstructed profile is the explicit Fourier-mode integral below.
Identification with the original HB upper/gap profiles remains separate.
-/

namespace ImbalancedChen.Part3.TwoLongContinuousModeReconstruction

noncomputable section
open Classical Set Filter MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongJointSharpStripDiscrepancy

/-- The earlier positive-x second derivative extends through x=0 because
all cutoff jets are zero there. This is an equality of actual functions. -/
theorem twist_secondDeriv_all (t x : ℝ) :
    deriv (deriv (twist t)) x = secondJet t x := by
  by_cases hx : 0 < x
  · exact twist_secondDeriv t hx
  · have hout : x ∉ Icc (1 / 2 : ℝ) (5 / 2) := by
      intro h; linarith [h.1]
    have hs : tsupport cutoff ⊆ Icc (1 / 2 : ℝ) (5 / 2) :=
      closure_minimal cutoff_support isClosed_Icc
    have hc : cutoff x = 0 := by
      by_contra h
      exact hout (cutoff_support h)
    have hd1 : bumpD1 x = 0 :=
      deriv_of_notMem_tsupport (fun h => hout (hs h))
    have hs1 : tsupport bumpD1 ⊆ Icc (1 / 2 : ℝ) (5 / 2) :=
      tsupport_deriv_subset.trans hs
    have hd2 : bumpD2 x = 0 :=
      deriv_of_notMem_tsupport (fun h => hout (hs1 h))
    have hst : tsupport (twist t) ⊆ Icc (1 / 2 : ℝ) (5 / 2) :=
      closure_minimal (twist_support t) isClosed_Icc
    have hst1 : tsupport (deriv (twist t)) ⊆ Icc (1 / 2 : ℝ) (5 / 2) :=
      tsupport_deriv_subset.trans hst
    rw [deriv_of_notMem_tsupport (fun h => hout (hst1 h))]
    simp [secondJet, hc, hd1, hd2]

/-- Parameter measurability is proved from the literal jet, rather than
assumed for the norm-valued frequency cost. -/
theorem secondJet_measurable : Measurable (fun z : ℝ × ℝ => secondJet z.1 z.2) := by
  have h0 : Measurable cutoff := cutoff_smooth.continuous.measurable
  have h1 : Measurable bumpD1 := bumpD1_smooth.continuous.measurable
  have h2 : Measurable bumpD2 := bumpD2_smooth.continuous.measurable
  unfold secondJet phase
  fun_prop

/-- All literal N2 frequency costs are strongly measurable. The Bochner
parameter integral API applies even before proving its integrability. -/
theorem N2_twist_stronglyMeasurable : StronglyMeasurable (fun t : ℝ => N2 (twist t)) := by
  have hJ : StronglyMeasurable (fun t : ℝ => ∫ x : ℝ, ‖secondJet t x‖) :=
    secondJet_measurable.stronglyMeasurable.norm.integral_prod_right'
  have heq : (fun t : ℝ => N2 (twist t)) =
      fun t => L0 + ∫ x : ℝ, ‖secondJet t x‖ := by
    funext t
    unfold N2
    simp_rw [twist_norm, twist_secondDeriv_all]
    rfl
  rw [heq]
  exact stronglyMeasurable_const.add hJ

/-- The cost charged against the Fourier amplitude. -/
def modeMass {E : Type*} (A : E → ℂ) (t₁ t₂ : E → ℝ) (v : E) : ℝ :=
  ‖A v‖ * N2 (twist (t₁ v)) * N2 (twist (t₂ v))

def cubeCost (H : ℝ) : ℝ := modeConstant ^ 2 * (1 + H) ^ 4

theorem cubeCost_nonneg (H : ℝ) : 0 ≤ cubeCost H := by
  unfold cubeCost
  positivity

theorem modeMass_nonneg {E : Type*} (A : E → ℂ) (t₁ t₂ : E → ℝ) (v : E) :
    0 ≤ modeMass A t₁ t₂ v := by
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (twist_N2_nonneg _))
    (twist_N2_nonneg _)

/-- The two actual profile norms obey a single pointwise fixed polynomial
bound on each retained frequency cube. -/
theorem modeMass_le {E : Type*} (A : E → ℂ) (t₁ t₂ : E → ℝ)
    {H : ℝ} (hH : 0 ≤ H) (v : E) (h₁ : |t₁ v| ≤ H) (h₂ : |t₂ v| ≤ H) :
    modeMass A t₁ t₂ v ≤ cubeCost H * ‖A v‖ := by
  have hC := modeConstant_nonneg
  unfold modeMass cubeCost
  calc
    _ ≤ ‖A v‖ * (modeConstant * (1 + H) ^ 2) *
        (modeConstant * (1 + H) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (twist_N2_le_cube hH h₁) (norm_nonneg _))
        (twist_N2_le_cube hH h₂) (twist_N2_nonneg _) (by positivity)
    _ = _ := by ring

/-- No integrability of the unknown N2 cost is assumed: measurability plus
the literal polynomial bound derives it from the amplitude's L1 norm. -/
theorem modeMass_integrable {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (A : E → ℂ) (t₁ t₂ : E → ℝ) (hA : Integrable A μ)
    (ht₁ : Measurable t₁) (ht₂ : Measurable t₂) {H : ℝ} (hH : 0 ≤ H)
    (hfreq : ∀ᵐ v ∂μ, |t₁ v| ≤ H ∧ |t₂ v| ≤ H) :
    Integrable (modeMass A t₁ t₂) μ := by
  have hN₁ := N2_twist_stronglyMeasurable.comp_measurable ht₁
  have hN₂ := N2_twist_stronglyMeasurable.comp_measurable ht₂
  have hmeas : AEStronglyMeasurable (modeMass A t₁ t₂) μ :=
    (hA.norm.aestronglyMeasurable.mul hN₁.aestronglyMeasurable).mul
      hN₂.aestronglyMeasurable
  apply (hA.norm.const_mul (cubeCost H)).mono' hmeas
  filter_upwards [hfreq] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (modeMass_nonneg A t₁ t₂ v)]
  exact modeMass_le A t₁ t₂ hH v hv.1 hv.2

/-- Continuous-frequency analogue of batch 30's finite mode mass. -/
theorem continuous_mode_N2_mass {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (A : E → ℂ) (t₁ t₂ : E → ℝ) (hA : Integrable A μ)
    (ht₁ : Measurable t₁) (ht₂ : Measurable t₂) {H : ℝ} (hH : 0 ≤ H)
    (hfreq : ∀ᵐ v ∂μ, |t₁ v| ≤ H ∧ |t₂ v| ≤ H) :
    (∫ v, modeMass A t₁ t₂ v ∂μ) ≤ cubeCost H * ∫ v, ‖A v‖ ∂μ := by
  calc
    _ ≤ ∫ v, cubeCost H * ‖A v‖ ∂μ := by
      apply integral_mono_ae
        (modeMass_integrable A t₁ t₂ hA ht₁ ht₂ hH hfreq)
        (hA.norm.const_mul (cubeCost H))
      filter_upwards [hfreq] with v hv
      exact modeMass_le A t₁ t₂ hH v hv.1 hv.2
    _ = _ := integral_const_mul _ _

/-- The retained cube is the actual coordinate frequency cube. -/
def frequencyCube (r : ℕ) (H : ℝ) : Set (Fin r → ℝ) :=
  {xi | ∀ a, |xi a| ≤ H}

theorem frequencyCube_measurable (r : ℕ) (H : ℝ) : MeasurableSet (frequencyCube r H) := by
  change MeasurableSet (⋂ a : Fin r, {xi : Fin r → ℝ | |xi a| ≤ H})
  exact MeasurableSet.iInter fun a => measurableSet_le (by fun_prop) measurable_const

/-- A direct all-rank caller for the actual Fourier coefficient A. The
unit short-phase factor is charged with exactly |A| on the same cube. -/
theorem selected_continuous_N2_mass_cube {r : ℕ}
    (A : (Fin r → ℝ) → ℂ) (z : Fin r → ℝ) (i j : Fin r)
    {H : ℝ} (hH : 0 ≤ H)
    (hA : IntegrableOn A (frequencyCube r H)) :
    (∫ xi in frequencyCube r H,
      ‖selectedAmplitude A xi z i j‖ * N2 (twist (xi i)) * N2 (twist (xi j))) ≤
      cubeCost H * ∫ xi in frequencyCube r H, ‖A xi‖ := by
  simp_rw [selectedAmplitude_norm]
  apply continuous_mode_N2_mass A (fun xi => xi i) (fun xi => xi j) hA
    (by fun_prop) (by fun_prop) hH
  filter_upwards [ae_restrict_mem (frequencyCube_measurable r H)] with xi hxi
  exact ⟨hxi i, hxi j⟩

/-- The actual two-long separated Fourier integrand. Profiles and short
amplitude are chosen before q; the physical marked word never enters. -/
def modeIntegrand {r : ℕ} (A : (Fin r → ℝ) → ℂ)
    (z : Fin r → ℝ) (i j : Fin r) (x y : ℝ) (xi : Fin r → ℝ) : ℂ :=
  selectedAmplitude A xi z i j * twist (xi i) x * twist (xi j) y

theorem modeIntegrand_norm_le {r : ℕ} (A : (Fin r → ℝ) → ℂ)
    (z : Fin r → ℝ) (i j : Fin r) (x y : ℝ) (xi : Fin r → ℝ) :
    ‖modeIntegrand A z i j x y xi‖ ≤ ‖A xi‖ := by
  have hx0 := cutoff_nonneg x
  have hy0 := cutoff_nonneg y
  have hx1 := cutoff_le_one x
  have hy1 := cutoff_le_one y
  simp only [modeIntegrand, norm_mul, selectedAmplitude_norm, twist_norm]
  calc
    _ ≤ ‖A xi‖ * 1 * 1 := by gcongr
    _ = _ := by ring

/-- The integrability needed for arithmetic Fubini is derived for every
literal integer pair, rather than supplied as a new hypothesis. -/
theorem modeIntegrand_integrable {r : ℕ} {μ : Measure (Fin r → ℝ)}
    (A : (Fin r → ℝ) → ℂ) (hA : Integrable A μ)
    (z : Fin r → ℝ) (i j : Fin r) (x y : ℝ) :
    Integrable (modeIntegrand A z i j x y) μ := by
  have hshort : Continuous (fun xi : Fin r → ℝ =>
      ∏ a ∈ (Finset.univ.erase i).erase j,
        Complex.exp (Complex.I * (xi a : ℂ) * (z a : ℂ))) := by fun_prop
  have hlong₁ : Continuous (fun xi : Fin r → ℝ => twist (xi i) x) := by
    unfold twist phase
    fun_prop
  have hlong₂ : Continuous (fun xi : Fin r → ℝ => twist (xi j) y) := by
    unfold twist phase
    fun_prop
  have hmeas : AEStronglyMeasurable (modeIntegrand A z i j x y) μ :=
    ((hA.aestronglyMeasurable.mul hshort.aestronglyMeasurable).mul
      hlong₁.aestronglyMeasurable).mul hlong₂.aestronglyMeasurable
  exact hA.norm.mono' hmeas (Filter.Eventually.of_forall
    (modeIntegrand_norm_le A z i j x y))

/-- Exact AP/coprime-mean residue weight, retaining the complete product. -/
def residueWeight (m a q : ℕ) (u : ℕ × ℕ) : ℂ :=
  (if m * u.1 * u.2 % q = a % q then 1 else 0) -
    (((Nat.totient q : ℝ)⁻¹ : ℂ) *
      if Nat.Coprime (m * u.1 * u.2) q then 1 else 0)

theorem physicalDiscrepancy_eq_kernel (R : Finset (ℕ × ℕ))
    (m a q : ℕ) (beta : (ℕ × ℕ) → ℂ) :
    physicalDiscrepancy R (fun _ => m) Prod.fst Prod.snd a q beta =
      ∑ u ∈ R, residueWeight m a q u * beta u := by
  unfold physicalDiscrepancy physicalCount exactCoprimeMean residueWeight productWord
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> ring

/-- A literal q-independent reconstructed long profile. -/
def reconstructedProfile {r : ℕ} (μ : Measure (Fin r → ℝ))
    (A : (Fin r → ℝ) → ℂ) (z : Fin r → ℝ) (i j : Fin r)
    (U V : ℝ) (d₁ d₂ : ℕ) (u : ℕ × ℕ) : ℂ :=
  ∫ xi, modeIntegrand A z i j ((u.1 : ℝ) / (U / d₁))
    ((u.2 : ℝ) / (V / d₂)) xi ∂μ

/-- The precise literal finite core receiving the reconstructed profile. -/
def reconstructedCore {r : ℕ} (μ : Measure (Fin r → ℝ))
    (A : (Fin r → ℝ) → ℂ) (z : Fin r → ℝ) (i j : Fin r)
    (U V : ℝ) (m d₁ d₂ a q : ℕ) : ℂ :=
  physicalDiscrepancy ((wideWindow (U / d₁)).product (wideWindow (V / d₂)))
    (fun _ => m * d₁ * d₂) Prod.fst Prod.snd a q
    (reconstructedProfile μ A z i j U V d₁ d₂)

/-- Every actual literal mode core is integrable in the continuous
frequency variable. This also supplies the finite Brun Fubini guard. -/
theorem literalCore_integrable {r : ℕ} {μ : Measure (Fin r → ℝ)}
    (A : (Fin r → ℝ) → ℂ) (hA : Integrable A μ)
    (z : Fin r → ℝ) (i j : Fin r) (U V : ℝ) (m d₁ d₂ a q : ℕ) :
    Integrable (fun xi => literalModeCore (selectedAmplitude A xi z i j)
      (xi i) (xi j) U V m d₁ d₂ a q) μ := by
  have heq : (fun xi => literalModeCore (selectedAmplitude A xi z i j)
      (xi i) (xi j) U V m d₁ d₂ a q) =
      fun xi => ∑ u ∈ (wideWindow (U / d₁)).product (wideWindow (V / d₂)),
        residueWeight (m * d₁ * d₂) a q u *
          modeIntegrand A z i j ((u.1 : ℝ) / (U / d₁))
            ((u.2 : ℝ) / (V / d₂)) xi := by
    funext xi
    exact physicalDiscrepancy_eq_kernel _ _ _ _ _
  rw [heq]
  exact integrable_finset_sum _ fun u hu =>
    (modeIntegrand_integrable A hA z i j _ _).const_mul _

/-- No equality of integral cores is assumed: finite arithmetic Fubini
proves the count AND the exact same-coefficient coprime mean identity. -/
theorem reconstructedCore_eq_integral {r : ℕ} {μ : Measure (Fin r → ℝ)}
    (A : (Fin r → ℝ) → ℂ) (hA : Integrable A μ)
    (z : Fin r → ℝ) (i j : Fin r) (U V : ℝ) (m d₁ d₂ a q : ℕ) :
    reconstructedCore μ A z i j U V m d₁ d₂ a q =
      ∫ xi, literalModeCore (selectedAmplitude A xi z i j)
        (xi i) (xi j) U V m d₁ d₂ a q ∂μ := by
  let R := (wideWindow (U / d₁)).product (wideWindow (V / d₂))
  have hterm (u : ℕ × ℕ) : Integrable (fun xi =>
      residueWeight (m * d₁ * d₂) a q u *
        modeIntegrand A z i j ((u.1 : ℝ) / (U / d₁))
          ((u.2 : ℝ) / (V / d₂)) xi) μ :=
    (modeIntegrand_integrable A hA z i j _ _).const_mul _
  calc
    _ = ∑ u ∈ R, residueWeight (m * d₁ * d₂) a q u *
        reconstructedProfile μ A z i j U V d₁ d₂ u :=
      physicalDiscrepancy_eq_kernel _ _ _ _ _
    _ = ∑ u ∈ R, ∫ xi, residueWeight (m * d₁ * d₂) a q u *
        modeIntegrand A z i j ((u.1 : ℝ) / (U / d₁))
          ((u.2 : ℝ) / (V / d₂)) xi ∂μ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (integral_const_mul _ _).symm
    _ = ∫ xi, ∑ u ∈ R, residueWeight (m * d₁ * d₂) a q u *
        modeIntegrand A z i j ((u.1 : ℝ) / (U / d₁))
          ((u.2 : ℝ) / (V / d₂)) xi ∂μ :=
      (integral_finset_sum R (fun u hu => hterm u)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with xi
      exact (physicalDiscrepancy_eq_kernel _ _ _ _ _).symm

/-- Three independent finite Brun coefficient banks (upper/gap1/gap2)
may now use the SAME proved reconstruction, with no per-core hExact. -/
theorem threeBrun_integral {r : ℕ} {μ : Measure (Fin r → ℝ)}
    (A : (Fin r → ℝ) → ℂ) (hA : Integrable A μ)
    (z : Fin r → ℝ) (i j : Fin r) (U V : ℝ) (m a q : ℕ)
    (D : Finset (ℕ × ℕ)) (c : Fin 3 → (ℕ × ℕ) → ℂ) (label : Fin 3) :
    (∑ d ∈ D, c label d * reconstructedCore μ A z i j U V m d.1 d.2 a q) =
      ∫ xi, ∑ d ∈ D, c label d *
        literalModeCore (selectedAmplitude A xi z i j) (xi i) (xi j)
          U V m d.1 d.2 a q ∂μ := by
  simp_rw [reconstructedCore_eq_integral A hA]
  calc
    _ = ∑ d ∈ D, ∫ xi, c label d *
        literalModeCore (selectedAmplitude A xi z i j) (xi i) (xi j)
          U V m d.1 d.2 a q ∂μ := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (integral_const_mul _ _).symm
    _ = _ := (integral_finset_sum D (fun d hd =>
      (literalCore_integrable A hA z i j U V m d.1 d.2 a q).const_mul _)).symm

/-- The finite physical signed rho can be retained outside BOTH the
count and coprime mean while commuting the same mode integral. -/
theorem sameRho_threeBrun_integral {r : ℕ} {μ : Measure (Fin r → ℝ)}
    (A : (Fin r → ℝ) → ℂ) (hA : Integrable A μ)
    (z : Fin r → ℝ) (i j : Fin r) (U V : ℝ) (m a : ℕ)
    (D : Finset (ℕ × ℕ)) (c : Fin 3 → (ℕ × ℕ) → ℂ) (label : Fin 3)
    (Q : Finset ℕ) (rho : ℕ → ℂ) :
    (∑ q ∈ Q, rho q * ∑ d ∈ D,
      c label d * reconstructedCore μ A z i j U V m d.1 d.2 a q) =
      ∫ xi, ∑ q ∈ Q, rho q * ∑ d ∈ D, c label d *
        literalModeCore (selectedAmplitude A xi z i j) (xi i) (xi j)
          U V m d.1 d.2 a q ∂μ := by
  simp_rw [threeBrun_integral A hA]
  calc
    _ = ∑ q ∈ Q, ∫ xi, rho q * ∑ d ∈ D, c label d *
        literalModeCore (selectedAmplitude A xi z i j) (xi i) (xi j)
          U V m d.1 d.2 a q ∂μ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (integral_const_mul _ _).symm
    _ = _ := (integral_finset_sum Q (fun q hq =>
      (integrable_finset_sum D (fun d hd =>
        (literalCore_integrable A hA z i j U V m d.1 d.2 a q).const_mul _)).const_mul _)).symm

/-- q=1 has exactly zero discrepancy before any norm estimate. -/
theorem literalModeCore_one (alpha : ℂ) (t₁ t₂ U V : ℝ)
    (m d₁ d₂ a : ℕ) : literalModeCore alpha t₁ t₂ U V m d₁ d₂ a 1 = 0 := by
  rw [literalModeCore_exact]
  simp

end
end ImbalancedChen.Part3.TwoLongContinuousModeReconstruction
