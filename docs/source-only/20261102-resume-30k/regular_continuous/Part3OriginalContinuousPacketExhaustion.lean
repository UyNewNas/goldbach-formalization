import ImbalancedChen.Part3RegularPositiveMeasureExhaustion
import ImbalancedChen.Part3Gamma0ActualCusps
import ImbalancedChen.Part3ActualConjugatedPacket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The carrier is Mathlib's actual finite cusp-orbit quotient of Gamma0(z),
at the level of the original CoprimePacket. The measure is the cusp sum
of dt/cosh(pi*t), and the fixed Kuznetsov 1/(4*pi) stays outside it.
The two coefficient functionals use literal PacketData and R(n)=sqrt(n)rho(n).
The raw rho maps and their primitive finite-height quadratic forms still
need their automorphic realization. This file does not define those maps
to be Eisenstein coefficients and does not assert a trace formula.
-/

namespace ImbalancedChen.Part3.OriginalContinuousPacketExhaustion20261102
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate Topology MatrixGroups
open Matrix Matrix.SpecialLinearGroup
open Gamma0ActualCuspsSourceOnly
open RegularCumulativeShellPayment20261102 RegularPositiveMeasureExhaustion20261102
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualConjugatedPacketP3SourceOnly (completed_weight_neg_frequency)

/-- The integer Gamma0 matrix giving the representative 1/z of the
infinity orbit, used to evaluate the printed classical cusp density. -/
def infinityDenominatorMatrix (z : ℕ) : SL(2, ℤ) :=
  ⟨!![1,0;(z : ℤ),1],by simp [Matrix.det_fin_two_of]⟩

theorem infinityDenominatorMatrix_mem (z : ℕ) :
    infinityDenominatorMatrix z ∈ CongruenceSubgroup.Gamma0 z := by
  rw [gamma0_mem_iff_level_dvd_c]
  simp [infinityDenominatorMatrix]

theorem infinityDenominatorMatrix_action (z : ℕ) [NeZero z] :
    mapGL ℝ (infinityDenominatorMatrix z) • (∞ : OnePoint ℝ) =
      ((1/(z : ℝ) : ℝ) : OnePoint ℝ) := by
  have hz : (z : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne z
  simp [smul_infty_eq_ite,infinityDenominatorMatrix,mapGL_coe_matrix,hz]

/-- The arithmetic density mu(a)=(w,q/w)/q in Drappeau Prop.4.7,
where a has a reduced representative u/w and w divides q. -/
def classicalCuspDensity (z w : ℕ) : ℝ := (Nat.gcd w (z/w) : ℝ)/(z : ℝ)

theorem cuspOne_density (z : ℕ) : classicalCuspDensity z 1 = 1/(z : ℝ) := by
  simp [classicalCuspDensity]

theorem cuspInfinity_density (z : ℕ) [NeZero z] :
    classicalCuspDensity z z = 1/(z : ℝ) := by
  have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
  simp [classicalCuspDensity,Nat.div_self hz]

/-- Genuine Gamma0 cusp orbits. No selected subset of cusps is substituted. -/
def Gamma0Cusp (z : ℕ) : Type :=
  CuspOrbits (CongruenceSubgroup.Gamma0 z : Subgroup (GL (Fin 2) ℝ))

instance gamma0CuspFinite (z : ℕ) [NeZero z] : Finite (Gamma0Cusp z) := by
  unfold Gamma0Cusp
  infer_instance

instance gamma0CuspFintype (z : ℕ) [NeZero z] : Fintype (Gamma0Cusp z) := Fintype.ofFinite _

instance gamma0CuspMeasurableSpace (z : ℕ) : MeasurableSpace (Gamma0Cusp z) := ⊤

instance gamma0CuspMeasurableSingleton (z : ℕ) : MeasurableSingletonClass (Gamma0Cusp z) :=
  ⟨fun _ => trivial⟩

abbrev ContinuousPoint (z : ℕ) := Gamma0Cusp z × ℝ

/-- The actual positive continuous weight. No t power or level factor
is introduced by this definition. -/
def sechDensity (t : ℝ) : ℝ≥0 :=
  ⟨1/Real.cosh (Real.pi*t),one_div_nonneg.mpr (Real.cosh_pos _).le⟩

theorem sechDensity_measurable : Measurable sechDensity := by
  have hh : Continuous (fun t : ℝ => 1/Real.cosh (Real.pi*t)) :=
    continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      (fun t => (Real.cosh_pos _).ne')
  exact hh.measurable.subtype_mk

def continuousHeightMeasure : Measure ℝ :=
  volume.withDensity (fun t => (sechDensity t : ℝ≥0∞))

instance continuousHeightMeasure_sigmaFinite : SigmaFinite continuousHeightMeasure := by
  unfold continuousHeightMeasure
  infer_instance

def continuousMeasure (z : ℕ) : Measure (ContinuousPoint z) :=
  (Measure.count : Measure (Gamma0Cusp z)).prod continuousHeightMeasure

/-- Full cusp sum and exact density, derived by Fubini. -/
theorem integral_continuousMeasure (z : ℕ) [NeZero z] (F : ContinuousPoint z → ℂ)
    (hF : Integrable F (continuousMeasure z)) :
    (∫ p, F p ∂continuousMeasure z) =
      ∑ c : Gamma0Cusp z, ∫ t : ℝ, (1/Real.cosh (Real.pi*t)) • F (c,t) := by
  rw [continuousMeasure,integral_prod _ hF,integral_count]
  apply Finset.sum_congr rfl
  intro c hc
  rw [continuousHeightMeasure,integral_withDensity_eq_integral_smul sechDensity_measurable]
  rfl

theorem continuousCut_eq_prod (z : ℕ) (T : ℝ) :
    spectralCut (Prod.snd : ContinuousPoint z → ℝ) T =
      (Set.univ : Set (Gamma0Cusp z)) ×ˢ Set.Icc (-T) T := by
  ext p
  simp only [spectralCut,Set.mem_setOf_eq,Set.mem_prod,Set.mem_univ,true_and,Set.mem_Icc,abs_le]

/-- Exact finite-height positive quadratic form used by the classical
continuous large sieve: every cusp, both signs of t, and dt/cosh(pi*t). -/
theorem continuous_quadratic_form (z : ℕ) [NeZero z] (A : ContinuousPoint z → ℂ)
    (T : ℝ) (hA : MemLp A 2 ((continuousMeasure z).restrict (spectralCut Prod.snd T))) :
    (∫ p in spectralCut Prod.snd T, ‖A p‖^2 ∂continuousMeasure z) =
      ∑ c : Gamma0Cusp z, ∫ t in Set.Icc (-T) T, ‖A (c,t)‖^2/Real.cosh (Real.pi*t) := by
  have hm : (continuousMeasure z).restrict (spectralCut Prod.snd T) =
      (Measure.count : Measure (Gamma0Cusp z)).prod (continuousHeightMeasure.restrict (Set.Icc (-T) T)) := by
    rw [continuousMeasure,continuousCut_eq_prod,← Measure.prod_restrict,Measure.restrict_univ]
  have hi : Integrable (fun p => ‖A p‖^2)
      ((Measure.count : Measure (Gamma0Cusp z)).prod (continuousHeightMeasure.restrict (Set.Icc (-T) T))) := by
    rw [← hm]
    exact hA.norm.integrable_sq
  rw [hm,integral_prod _ hi,integral_count]
  apply Finset.sum_congr rfl
  intro c hc
  rw [continuousHeightMeasure,
    setIntegral_withDensity_eq_setIntegral_smul sechDensity_measurable _ measurableSet_Icc]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change (1/Real.cosh (Real.pi*t))*‖A (c,t)‖^2 = ‖A (c,t)‖^2/Real.cosh (Real.pi*t)
    ring

/-- The normalization is on the Fourier coefficient, not on the
original coefficient energy. For the positive natural n carrier this
is precisely R(n)=sqrt(|n|)*rho(n). -/
def normalizedR {z : ℕ} (rho : ContinuousPoint z → ℕ → ℂ)
    (p : ContinuousPoint z) (n : ℕ) : ℂ := (Real.sqrt (n : ℝ) : ℂ)*rho p n

/-- The Fourier sign is selected by the SAME original cusp flag as
the signed coefficient phase. It is not a second independent sign. -/
def signedRho {z : ℕ} (negative : Bool) (rho : ContinuousPoint z → ℤ → ℂ)
    (p : ContinuousPoint z) (n : ℕ) : ℂ :=
  rho p (if negative then -(n : ℤ) else (n : ℤ))

theorem normalizedR_norm_sq {z : ℕ} (rho : ContinuousPoint z → ℕ → ℂ)
    (p : ContinuousPoint z) (n : ℕ) :
    ‖normalizedR rho p n‖^2 = (n : ℝ)*‖rho p n‖^2 := by
  rw [normalizedR,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The two normalized coefficients reproduce the exact sqrt(m*n)
factor of Drappeau (4.16)/(4.18), with the infinity conjugation intact. -/
theorem normalizedR_pair {z : ℕ} (rhoInf rhoOne : ContinuousPoint z → ℕ → ℂ)
    (p : ContinuousPoint z) (m n : ℕ) :
    conj (normalizedR rhoInf p m)*normalizedR rhoOne p n =
      (Real.sqrt ((m : ℝ)*(n : ℝ)) : ℂ)*conj (rhoInf p m)*rhoOne p n := by
  unfold normalizedR
  rw [map_mul,Complex.conj_ofReal,Real.sqrt_mul (Nat.cast_nonneg m),Complex.ofReal_mul]
  ring

variable {ρ : Type*}

/-- The completed phase is the same k1/(64*V) for every cusp, height,
level row and m. It is not replaced by an arbitrary spectral weight. -/
theorem originalM_rho_formula (P : PacketData ρ) (k : D4 → ℤ) {z : ℕ}
    (rho : ContinuousPoint z → ℕ → ℂ) (p : ContinuousPoint z) :
    originalMFunctional P k (normalizedR rho) p =
      ∑ m ∈ P.mCarrier,
        P3Period64NativeReconstructionSourceOnly.e ((k 1 : ℝ)/64*((m : ℝ)/P.V)) *
          (Real.sqrt (m : ℝ) : ℂ)*rho p m := by
  unfold originalMFunctional
  apply Finset.sum_congr rfl
  intro m hm
  rw [P.completed_weight_mem k m hm,normalizedR]
  ring

/-- The original signed n coefficient is independent of the cusp and
height. Both the coprime gate and the exact plus/minus n/z phase are retained. -/
theorem originalN_rho_formula (P : PacketData ρ) (k : D4 → ℤ) (r : ρ) {z : ℕ}
    (rho : ContinuousPoint z → ℕ → ℂ) (p : ContinuousPoint z) :
    originalNFunctional P k r (normalizedR rho) p =
      ∑ n ∈ P.nCarrier r,
        (if Nat.Coprime n (P.packet r).residue then
          (P.packet r).beta ((P.packet r).multiplier*n) (P.packet r).level *
            cuspPhase P.negativeCusp (P.packet r).level n *
            P3Period64NativeReconstructionSourceOnly.e
              ((k 2 : ℝ)/64*((((P.packet r).multiplier*n : ℕ) : ℝ)/P.U)+
                (k 3 : ℝ)/64*(((P.packet r).level : ℝ)/P.Z))
        else 0) * (Real.sqrt (n : ℝ) : ℂ)*rho p n := by
  unfold originalNFunctional
  apply Finset.sum_congr rfl
  intro n hn
  rw [signedCoefficient_modePacket]
  unfold signedCoefficient normalizedR
  split_ifs <;> ring

theorem originalM_measurable (P : PacketData ρ) (k : D4 → ℤ) {z : ℕ}
    (rho : ContinuousPoint z → ℕ → ℂ) (hrho : ∀ n, Measurable (fun p => rho p n)) :
    Measurable (originalMFunctional P k (normalizedR rho)) := by
  unfold originalMFunctional normalizedR
  apply Finset.measurable_sum
  intro n hn
  exact measurable_const.mul (measurable_const.mul (hrho n))

theorem originalN_measurable (P : PacketData ρ) (k : D4 → ℤ) (r : ρ) {z : ℕ}
    (rho : ContinuousPoint z → ℕ → ℂ) (hrho : ∀ n, Measurable (fun p => rho p n)) :
    Measurable (originalNFunctional P k r (normalizedR rho)) := by
  unfold originalNFunctional normalizedR
  apply Finset.measurable_sum
  intro n hn
  exact measurable_const.mul (measurable_const.mul (hrho n))

/-- Conjugation on the infinity Fourier coefficient is on the
classical trace formula side. Reflecting the common frequency before
that conjugation leaves the ORIGINAL +k completed-variable phase. -/
def originalTraceIntegrand (P : PacketData ρ) (k : D4 → ℤ) (r : ρ) {z : ℕ}
    (rhoInf rhoOne : ContinuousPoint z → ℕ → ℂ) (H : ℝ → ℂ)
    (p : ContinuousPoint z) : ℂ :=
  H p.2*conj (originalMFunctional P (-k) (normalizedR rhoInf) p)*
    originalNFunctional P k r (normalizedR rhoOne) p

/-- The trace integrand is the literal finite m,n source, including
which Fourier coefficient is conjugated. Neither beta nor either cusp
phase is assumed real, and no conjugation of the original beta occurs. -/
theorem originalTraceIntegrand_eq_source
    (P : PacketData ρ) (k : D4 → ℤ) (r : ρ) {z : ℕ}
    (rhoInf rhoOne : ContinuousPoint z → ℕ → ℂ) (H : ℝ → ℂ)
    (p : ContinuousPoint z) :
    originalTraceIntegrand P k r rhoInf rhoOne H p =
      ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier r,
        (P.completed k).weight m *
          signedCoefficient P.negativeCusp (modePacket (P.packet r) k P.U P.Z) n *
          (H p.2*conj (normalizedR rhoInf p m)*normalizedR rhoOne p n) := by
  have hw (m : ℕ) : conj ((P.completed (-k)).weight m) = (P.completed k).weight m := by
    rw [completed_weight_neg_frequency,Complex.star_def,Complex.conj_conj]
  unfold originalTraceIntegrand originalMFunctional originalNFunctional
  simp only [map_sum,map_mul,hw]
  calc
    _ = H p.2 *
        ((∑ m ∈ P.mCarrier, (P.completed k).weight m*conj (normalizedR rhoInf p m)) *
          ∑ n ∈ P.nCarrier r,
            signedCoefficient P.negativeCusp (modePacket (P.packet r) k P.U P.Z) n*
              normalizedR rhoOne p n) := by ring
    _ = H p.2 * (∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier r,
        ((P.completed k).weight m*conj (normalizedR rhoInf p m)) *
          (signedCoefficient P.negativeCusp (modePacket (P.packet r) k P.U P.Z) n*
            normalizedR rhoOne p n)) := by rw [Finset.sum_mul_sum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- Fixed 1/(4*pi) from the normalized continuous Kuznetsov term.
No assertion that this is the physical Kloosterman sum is made. -/
def continuousKuznetsovValue (z : ℕ) (F : ContinuousPoint z → ℂ) : ℂ :=
  (1/(4*Real.pi) : ℝ) • ∫ p, F p ∂continuousMeasure z

theorem continuousKuznetsovValue_eq_cusp_sum (z : ℕ) [NeZero z]
    (F : ContinuousPoint z → ℂ) (hF : Integrable F (continuousMeasure z)) :
    continuousKuznetsovValue z F =
      (1/(4*Real.pi) : ℝ) •
        ∑ c : Gamma0Cusp z, ∫ t : ℝ, (1/Real.cosh (Real.pi*t)) • F (c,t) := by
  rw [continuousKuznetsovValue,integral_continuousMeasure z F hF]

theorem continuousKuznetsovValue_norm (z : ℕ) (F : ContinuousPoint z → ℂ) :
    ‖continuousKuznetsovValue z F‖ ≤ (1/(4*Real.pi))*(∫ p, ‖F p‖ ∂continuousMeasure z) := by
  rw [continuousKuznetsovValue,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1/(4*Real.pi))]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) (by positivity)

/-- A genuine continuous consumer at the packet's ACTUAL level. The
classical premises are only the two local positive quadratic forms and
the transform estimates. Their RHS coefficient norms are eliminated by
the already proved literal identities; full L1 and exhaustion are not
premises. The raw rho functions must still be realized automorphically.
The z parameter is tied to the packet by hz, so the cusp carrier is not
silently allowed to vary independently of the original source. -/
theorem original_packet_continuous_exhaustion
    (P : PacketData ρ) (k : D4 → ℤ) (r : ρ)
    (z : ℕ) [NeZero z] (hz : z = (P.packet r).level)
    (rhoInf : ContinuousPoint z → ℕ → ℂ) (rhoOne : ContinuousPoint z → ℤ → ℂ)
    (hrhoInf : ∀ n, Measurable (fun p => rhoInf p n))
    (hrhoOne : ∀ n, Measurable (fun p => rhoOne p n))
    (H : ℝ → ℂ) (hH : Measurable H)
    {C ε C1 C2 : ℝ} (hC : 0 ≤ C) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hMA : ∀ T : ℝ, 1 ≤ T → MemLp (originalMFunctional P (-k) (normalizedR rhoInf)) 2
      ((continuousMeasure z).restrict (spectralCut Prod.snd T)))
    (hMB : ∀ T : ℝ, 1 ≤ T → MemLp (originalNFunctional P k r (normalizedR (signedRho P.negativeCusp rhoOne))) 2
      ((continuousMeasure z).restrict (spectralCut Prod.snd T)))
    (hCumM : ∀ T : ℝ, 1 ≤ T →
      (∑ c : Gamma0Cusp z, ∫ t in Set.Icc (-T) T,
        ‖originalMFunctional P (-k) (normalizedR rhoInf) (c,t)‖^2/Real.cosh (Real.pi*t)) ≤
          (T^2+P.V^(1+ε)/(z : ℝ)) *
            (C1*∑ m ∈ P.mCarrier, ‖(P.completed (-k)).weight m‖^2))
    (hCumN : ∀ T : ℝ, 1 ≤ T →
      (∑ c : Gamma0Cusp z, ∫ t in Set.Icc (-T) T,
        ‖originalNFunctional P k r (normalizedR (signedRho P.negativeCusp rhoOne)) (c,t)‖^2/Real.cosh (Real.pi*t)) ≤
          (T^2+(P.U/((P.packet r).multiplier : ℝ))^(1+ε)/(z : ℝ)) *
            (C2*∑ n ∈ P.nCarrier r,
              ‖signedCoefficient P.negativeCusp (modePacket (P.packet r) k P.U P.Z) n‖^2))
    (hlow : ∀ t : ℝ, |t| ≤ regularBase P.Y0 → ‖H t‖ ≤ C*(1+|Real.log P.Y0|)/(1+P.Y0))
    (hdecay : ∀ t : ℝ, regularBase P.Y0 ≤ |t| →
      ‖H t‖ ≤ C*(1/(|t|^2*Real.sqrt |t|)+P.Y0/|t|^3)) :
    let F := originalTraceIntegrand P k r rhoInf (signedRho P.negativeCusp rhoOne) H
    Integrable F (continuousMeasure z) ∧
      (∫ p, ‖F p‖ ∂continuousMeasure z) ≤
        516*C*(1+|Real.log P.Y0|)/(1+P.Y0) *
          Real.sqrt (((1+P.Y0^2+P.V^(1+ε)/(z : ℝ))*(C1*(P.mCarrier.card : ℝ))) *
            ((1+P.Y0^2+(P.U/((P.packet r).multiplier : ℝ))^(1+ε)/(z : ℝ))*(C2*originalNEnergy P r))) ∧
      Tendsto (fun j : ℕ => ∫ p in spectralCut Prod.snd ((4 : ℝ)^j*regularBase P.Y0), F p
        ∂continuousMeasure z) atTop (𝓝 (∫ p, F p ∂continuousMeasure z)) ∧
      (P.packet r).residue.Coprime z := by
  dsimp only
  have hzpos : (0 : ℝ) < z := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne z)
  have hu : 0 ≤ P.V^(1+ε)/(z : ℝ) :=
    div_nonneg (Real.rpow_nonneg P.V_pos.le _) hzpos.le
  have hv : 0 ≤ (P.U/((P.packet r).multiplier : ℝ))^(1+ε)/(z : ℝ) :=
    div_nonneg (Real.rpow_nonneg (div_nonneg P.U_pos.le (Nat.cast_nonneg _)) _) hzpos.le
  have he : 0 ≤ originalNEnergy P r := Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hm := originalM_measurable P (-k) rhoInf hrhoInf
  have hn := originalN_measurable P k r (signedRho P.negativeCusp rhoOne)
    (fun n => hrhoOne (if P.negativeCusp then -(n : ℤ) else (n : ℤ)))
  have hF : AEStronglyMeasurable (fun p : ContinuousPoint z =>
      H p.2*originalNFunctional P k r (normalizedR (signedRho P.negativeCusp rhoOne)) p*
        conj (originalMFunctional P (-k) (normalizedR rhoInf) p)) (continuousMeasure z) := by
    exact (((hH.comp measurable_snd).mul hn).mul hm.star).aestronglyMeasurable
  obtain ⟨hi,hb⟩ := regular_R1_integrable (continuousMeasure z) Prod.snd
    (fun p => H p.2) (originalNFunctional P k r (normalizedR (signedRho P.negativeCusp rhoOne)))
    (originalMFunctional P (-k) (normalizedR rhoInf))
    (A2 := C2*originalNEnergy P r) (B2 := C1*(P.mCarrier.card : ℝ)) measurable_snd hF
    hC P.Y0_pos hv hu (by positivity) (by positivity) hMB hMA
    (fun T hT => by
      rw [continuous_quadratic_form z _ T (hMB T hT)]
      simpa only [originalN_coefficient_norm] using hCumN T hT)
    (fun T hT => by
      rw [continuous_quadratic_form z _ T (hMA T hT)]
      simpa only [originalM_coefficient_norm] using hCumM T hT)
    (fun p hp => hlow p.2 hp) (fun p hp => hdecay p.2 hp)
  have hid : (fun p : ContinuousPoint z =>
      H p.2*originalNFunctional P k r (normalizedR (signedRho P.negativeCusp rhoOne)) p*
        conj (originalMFunctional P (-k) (normalizedR rhoInf) p)) =
      originalTraceIntegrand P k r rhoInf (signedRho P.negativeCusp rhoOne) H := by
    funext p
    unfold originalTraceIntegrand
    ring
  rw [hid] at hi
  have hidp (p : ContinuousPoint z) :
      H p.2*originalNFunctional P k r (normalizedR (signedRho P.negativeCusp rhoOne)) p*
        conj (originalMFunctional P (-k) (normalizedR rhoInf) p) =
      originalTraceIntegrand P k r rhoInf (signedRho P.negativeCusp rhoOne) H p := congrFun hid p
  simp_rw [hidp] at hb
  refine ⟨hi,?_,?_,?_⟩
  · simpa only [mul_comm
      ((1+P.Y0^2+(P.U/((P.packet r).multiplier : ℝ))^(1+ε)/(z : ℝ))*(C2*originalNEnergy P r))
      ((1+P.Y0^2+P.V^(1+ε)/(z : ℝ))*(C1*(P.mCarrier.card : ℝ)))] using hb
  · exact regular_integral_exhaustion (continuousMeasure z) Prod.snd _ measurable_snd hi (le_max_left _ _)
  · simpa only [hz] using (P.packet r).residue_coprime

end
end ImbalancedChen.Part3.OriginalContinuousPacketExhaustion20261102
