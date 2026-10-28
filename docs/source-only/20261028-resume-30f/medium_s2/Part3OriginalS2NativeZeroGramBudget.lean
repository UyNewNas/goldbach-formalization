import ImbalancedChen.Part3OriginalS2SameSourcePrincipal
import ImbalancedChen.Part3OriginalS2NativePhysicalRange
import ImbalancedChen.Part3OriginalSmoothCollapsedDivisorMoment
import ImbalancedChen.Part3OriginalS2RoughZLargeXGate
import Mathlib.Tactic

/-! Pay the actual same-source zero/Gram density error at V(D), using
the native whole-d coefficient geometry and an ordinary divisor mean.
No variance estimate or pointwise x^epsilon divisor loss is used here.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalS2NativeZeroGramBudget

open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2OneCongruencePoisson
open ImbalancedChen.Part3OriginalS2ZeroGramCompiler
open ImbalancedChen.Part3OriginalS2ZeroGramErrorPayment
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3OriginalS2ActualTailTransfer
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2NativeKeyTail
open ImbalancedChen.Part3OriginalS2NativeKeyTailPayment
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2NativePhysicalRange
open ImbalancedChen.Part3OriginalS2FullMixedTailPayment
open ImbalancedChen.Part3OriginalSmoothCollapsedDivisorMoment
open ImbalancedChen.Part3OriginalS2RoughZLargeXGate
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.Part3.OriginalPaperPsiCoprimeCount
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

def nativeZeroLogs (d : MediumAtom) : ℝ :=
  logBudget (nativePhysicalCap d) * (1 + Real.log (roughCap d)) ^ 4 *
    (1 + Real.log (nativePhysicalCap d : ℝ)) ^ 16

theorem primitiveMass_norm_le_freeCount
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (ell r : ℕ) :
    ‖primitiveMass d ell r‖ ≤ freeAlphaCount d (ell * r) := by
  have he : star (primitiveMass d ell r) = freeAlphaMass d (ell * r) := by
    simp only [primitiveMass, freeAlphaMass, star_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime (ell * r) <;> simp [hc]
  rw [← norm_star, he]
  exact freeAlphaMass_norm_le_count hd (ell * r)

theorem actual_error_pair_native_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    {z : ℝ} (hz : 4 ≤ z)
    (hlarge : 4 * Real.log d.scale / (z * Real.log 2) ≤ 1)
    (k : Key) (c : CoefficientIndex) (hc : c ∈ nativeKeyFamily d z k) :
    ‖actualZeroGramErrorPair d (strictReceiverCutoff z) (roughY d.scale) k
      c.1.1 c.1.2 c.2.1 c.2.2‖ ≤
      (roughEulerDelta d z * |d.V * paperMass| * (2 * d.U)) *
        (coefficientCost d c / ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ)) := by
  obtain ⟨hsource, hsmall, _⟩ := Finset.mem_filter.mp hc
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hsource
  have hq := nativeQ_data (by linarith [hd.2.2.1]) (Finset.mem_product.mp hqd).1
  have hdpos := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hrpos := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
  have hspos := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hleft := keyKept_norm_le_tau hd d.scale z k c.1.2 c.2.1 (Nat.mul_pos hdpos hrpos)
  have hright := keyKept_norm_le_tau hd d.scale z k c.1.2 c.2.2 (Nat.mul_pos hdpos hspos)
  rw [keyKept_eq_actual_lambdaTrim hd d.scale z (by linarith) k c.1.2 c.2.1 hsmall] at hleft
  rw [keyKept_eq_actual_lambdaTrim hd d.scale z (by linarith) k c.1.2 c.2.2 hsmall] at hright
  have hB₁ := primitiveMass_norm_le_freeCount hd (c.1.1 * c.1.2) c.2.1
  have hB₂ := primitiveMass_norm_le_freeCount hd (c.1.1 * c.1.2) c.2.2
  have hN := freeAlphaCount_le_two_U hd (c.1.1 * c.1.2 * c.2.1)
  have hdiff := native_density_difference_le hd hsigma hz hlarge c.1.2
    (c.1.1 * c.1.2) c.2.1 c.2.2 (Finset.mem_product.mp hrs).2
    (Nat.mul_pos hq.2.2.2 hdpos) hrpos
  have hqweight : ‖(paperQWeight d c.1.1 : ℂ)‖ ≤ 1 :=
    ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter.actualPsiQWeight_norm_le_one d c.1.1
  have hqweightR : |paperQWeight d c.1.1| ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hqweight
  have hcost : (tauR (c.1.2 * c.2.1) * tauR (c.1.2 * c.2.2) *
      freeAlphaCount d (c.1.1 * c.1.2 * c.2.2) /
        (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) ≤ coefficientCost d c := by
    have hn := freeAlphaCount_nonneg d (c.1.1 * c.1.2 * c.2.2)
    have hτr := tauR_nonneg (c.1.2 * c.2.1)
    have hτs := tauR_nonneg (c.1.2 * c.2.2)
    dsimp [tauR] at hτr hτs
    unfold coefficientCost tauR
    nlinarith [div_nonneg (mul_nonneg (mul_nonneg hτr hτs) hn)
      (Nat.cast_nonneg (Nat.totient (c.1.1 * c.1.2 * c.2.2)))]
  have hdelta : 0 ≤ roughEulerDelta d z := by
    unfold roughEulerDelta
    have hx := hd.2.2.2.2.2.1
    have he : 1 < Real.exp (Real.exp 1) := Real.one_lt_exp.mpr (Real.exp_pos 1)
    have hlog := Real.log_nonneg (show 1 ≤ d.scale by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  unfold actualZeroGramErrorPair
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 1 * tauR (c.1.2 * c.2.1) * tauR (c.1.2 * c.2.2) *
        |d.V * paperMass| * (roughEulerDelta d z * nativeZeroDensity
          (c.1.1 * c.1.2) c.2.1 c.2.2) *
        ((2 * d.U) * freeAlphaCount d (c.1.1 * c.1.2 * c.2.2)) := by
      gcongr <;> first | exact hqweightR | exact hleft | exact hright | exact hdiff |
        exact hB₁.trans hN | exact hB₂ | positivity
    _ = (roughEulerDelta d z * |d.V * paperMass| * (2 * d.U)) *
        ((tauR (c.1.2 * c.2.1) * tauR (c.1.2 * c.2.2) *
          freeAlphaCount d (c.1.1 * c.1.2 * c.2.2) /
          (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) /
            ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ)) := by
      unfold nativeZeroDensity
      ring
    _ ≤ _ := by
      gcongr

theorem actualZeroGramError_eq_native_family
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (hz : 0 ≤ z) (k : Key) :
    actualZeroGramError d (strictReceiverCutoff z) (roughY d.scale) k =
      ∑ c ∈ nativeKeyFamily d z k,
        actualZeroGramErrorPair d (strictReceiverCutoff z) (roughY d.scale) k
          c.1.1 c.1.2 c.2.1 c.2.2 := by
  have hraw : actualZeroGramError d (strictReceiverCutoff z) (roughY d.scale) k =
      ∑ c ∈ rawKeyFamily d k,
        actualZeroGramErrorPair d (strictReceiverCutoff z) (roughY d.scale) k
          c.1.1 c.1.2 c.2.1 c.2.2 := by
    simp only [actualZeroGramError, rawKeyFamily, Finset.sum_sigma, Finset.sum_product]
  rw [hraw]
  symm
  apply Finset.sum_subset (nativeKeyFamily_subset_raw d z k)
  intro c hc hn
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hsmall := (Finset.mem_product.mp hqd).2
  have hnot : ¬((c.1.2 ∈ dCarrier d z ∧ c.2.1 ∈ roughFiber d z c.1.2) ∧
      (c.1.2 ∈ dCarrier d z ∧ c.2.2 ∈ roughFiber d z c.1.2)) := by
    rintro ⟨⟨hdc, hr⟩, ⟨_, hs⟩⟩
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr
      ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hqd).1, hdc⟩,
        Finset.mem_product.mpr ⟨hr, hs⟩⟩,
      hsmall, (Finset.mem_product.mp hrs).1, (Finset.mem_product.mp hrs).2⟩)
  rcases not_and_or.mp hnot with hl | hr
  · have hK := (keyCoefficients_zero_outside d d.scale z k c.1.2 c.2.1 hl).2.1
    rw [keyKept_eq_actual_lambdaTrim hd d.scale z hz k c.1.2 c.2.1 hsmall] at hK
    simp [actualZeroGramErrorPair, hK]
  · have hK := (keyCoefficients_zero_outside d d.scale z k c.1.2 c.2.2 hr).2.1
    rw [keyKept_eq_actual_lambdaTrim hd d.scale z hz k c.1.2 c.2.2 hsmall] at hK
    simp [actualZeroGramErrorPair, hK]

theorem native_cost_reciprocal_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key) :
    (∑ c ∈ nativeKeyFamily d z k,
      coefficientCost d c / ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ)) ≤
      (24 * d.U / (d.Q1 * (2 : ℝ) ^ k.d)) * nativeZeroLogs d := by
  let S := nativeKeyFamily d z k
  let I := Finset.Icc 1 (nativePhysicalCap d)
  let Y := d.Q1 * (2 : ℝ) ^ k.d / 2
  have hY : 0 < Y := by
    dsimp [Y]
    have hQ : 0 < d.Q1 := by linarith [hd.2.2.1]
    positivity
  have hmaps : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 ∈ I := by
    intro c hc
    have hsrc := (Finset.mem_filter.mp hc).1
    obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hsrc
    have hq := (nativeQ_data (by linarith [hd.2.2.1]) (Finset.mem_product.mp hqd).1).2.2.2
    have hsmall := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
    have hr := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
    exact Finset.mem_Icc.mpr ⟨by positivity, (native_supported_modulus_le hd z c hsrc).1⟩
  have hcap : 1 ≤ nativePhysicalCap d := by
    have hQ1 : 1 ≤ d.Q1 := hd.2.2.1
    have hQ2 : 1 ≤ d.Q2 := hd.2.2.2.1
    have hQ3 : 1 ≤ d.Q3 := hd.2.2.2.2.1
    have h12 := mul_le_mul hQ1 hQ2 zero_le_one (by linarith : 0 ≤ d.Q1)
    have h123 := mul_le_mul h12 hQ3 zero_le_one (by positivity)
    apply Nat.le_floor
    nlinarith
  have hgroup := Finset.sum_fiberwise_of_maps_to' (s := S) (t := I)
    (g := fun c : CoefficientIndex => c.1.1 * c.1.2 * c.2.1)
    hmaps (fun c => coefficientCost d c / ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ))
  have hmoment := ordinaryTau_power_reciprocal_prefix_bound 4 (nativePhysicalCap d) hcap
  calc
    _ = ∑ l ∈ I, ∑ c ∈ S.filter (fun c => c.1.1 * c.1.2 * c.2.1 = l),
        coefficientCost d c / ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ) := hgroup.symm
    _ ≤ ∑ l ∈ I, nativeGeometryFactor d Y l / (l : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      let T := S.filter (fun c => c.1.1 * c.1.2 * c.2.1 = l)
      have hT : T ⊆ nativeCoefficientCarrier d z :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hmod : ∀ c ∈ T, c.1.1 * c.1.2 * c.2.1 = l :=
        fun c hc => (Finset.mem_filter.mp hc).2
      have hlevel : ∀ c ∈ T, Y ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) :=
        fun c hc => nativeKey_level hd z k c (Finset.mem_filter.mp hc).1
      have hgeom := nativeGeometry_le hd z Y hY T hT l
        (Finset.mem_Icc.mp hl).1 hmod hlevel
      have heq : (∑ c ∈ T, coefficientCost d c /
          ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ)) =
          (∑ c ∈ T, coefficientCost d c) / (l : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro c hc
        rw [hmod c hc]
      rw [heq]
      exact div_le_div_of_nonneg_right hgeom (Nat.cast_nonneg _)
    _ = (12 * d.U / Y) * logBudget (nativePhysicalCap d) *
        (1 + Real.log (roughCap d)) ^ 4 *
        ∑ l ∈ I, tauR l ^ 4 / (l : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      unfold nativeGeometryFactor
      ring
    _ ≤ (12 * d.U / Y) * logBudget (nativePhysicalCap d) *
        (1 + Real.log (roughCap d)) ^ 4 *
          (1 + Real.log (nativePhysicalCap d : ℝ)) ^ 16 := by
      apply mul_le_mul_of_nonneg_left
        (by simpa only [tauR, ordinaryTau] using hmoment)
      have hU : 0 ≤ d.U := by linarith [hd.1]
      have hlog := logBudget_nonneg (nativePhysicalCap d)
      positivity
    _ = _ := by unfold nativeZeroLogs Y; ring

theorem actualZeroGramError_le_native_logs
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    {z : ℝ} (hz : 4 ≤ z)
    (hlarge : 4 * Real.log d.scale / (z * Real.log 2) ≤ 1) (k : Key) :
    ‖actualZeroGramError d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
      48 * |paperMass| * roughEulerDelta d z * fixedDScale d ((2 : ℝ) ^ k.d) *
        nativeZeroLogs d := by
  rw [actualZeroGramError_eq_native_family hd z (by linarith) k]
  have hdelta : 0 ≤ roughEulerDelta d z := by
    unfold roughEulerDelta
    have hx := hd.2.2.2.2.2.1
    have he : 1 < Real.exp (Real.exp 1) := Real.one_lt_exp.mpr (Real.exp_pos 1)
    have hlog := Real.log_nonneg (show 1 ≤ d.scale by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  calc
    _ ≤ ∑ c ∈ nativeKeyFamily d z k,
        ‖actualZeroGramErrorPair d (strictReceiverCutoff z) (roughY d.scale) k
          c.1.1 c.1.2 c.2.1 c.2.2‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ nativeKeyFamily d z k,
        (roughEulerDelta d z * |d.V * paperMass| * (2 * d.U)) *
          (coefficientCost d c / ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun c hc => actual_error_pair_native_bound hd hsigma hz hlarge k c hc)
    _ = (roughEulerDelta d z * |d.V * paperMass| * (2 * d.U)) *
        ∑ c ∈ nativeKeyFamily d z k,
          coefficientCost d c / ((c.1.1 * c.1.2 * c.2.1 : ℕ) : ℝ) :=
      (Finset.mul_sum ..).symm
    _ ≤ (roughEulerDelta d z * |d.V * paperMass| * (2 * d.U)) *
        ((24 * d.U / (d.Q1 * (2 : ℝ) ^ k.d)) * nativeZeroLogs d) := by
      apply mul_le_mul_of_nonneg_left (native_cost_reciprocal_sum_le hd z k)
      have hU : 0 ≤ d.U := by linarith [hd.1]
      positivity
    _ = _ := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ d.V by linarith [hd.2.1])]
      unfold fixedDScale
      ring

theorem nativeZeroLogs_le_fixed_logs
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hx : 1 ≤ d.scale) (hlog : 1 ≤ Real.log d.scale)
    (hphysical : nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    nativeZeroLogs d ≤ (2 : ℝ) ^ (21 : ℕ) * Real.log d.scale ^ (21 : ℕ) := by
  have hP : (nativePhysicalCap d : ℝ) ≤ d.scale := by
    calc
      _ ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) := by exact_mod_cast hphysical
      _ ≤ d.scale ^ ((4 : ℝ) / 5) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
      _ ≤ d.scale := Real.rpow_le_self_of_one_le hx (by norm_num)
  have hcap : physicalCap d ≤ nativePhysicalCap d := by
    apply Nat.floor_mono
    have hQ1 : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    have hQ2 : 0 ≤ d.Q2 := by linarith [hd.2.2.2.1]
    have hQ3 : 0 ≤ d.Q3 := by linarith [hd.2.2.2.2.1]
    nlinarith [mul_nonneg (mul_nonneg hQ1 hQ2) hQ3]
  have hRP : roughCap d ≤ (nativePhysicalCap d : ℝ) :=
    (roughCap_le_physicalCap hd).trans (by exact_mod_cast hcap)
  have hR := hRP.trans hP
  have hR1 := one_le_roughCap hd
  have hP1 : (1 : ℝ) ≤ nativePhysicalCap d := hR1.trans hRP
  have hRlog := Real.log_nonneg hR1
  have hPlog := Real.log_nonneg hP1
  have hp : 1 + Real.log (nativePhysicalCap d : ℝ) ≤ 2 * Real.log d.scale := by
    have hh := Real.log_le_log (by linarith : (0 : ℝ) < nativePhysicalCap d) hP
    linarith
  have hr : 1 + Real.log (roughCap d) ≤ 2 * Real.log d.scale := by
    have hh := Real.log_le_log (by linarith : 0 < roughCap d) hR
    linarith
  have hphi : logBudget (nativePhysicalCap d) ≤ 2 * Real.log d.scale := by
    unfold logBudget
    rw [max_eq_right hP1]
    exact hp
  unfold nativeZeroLogs
  calc
    _ ≤ (2 * Real.log d.scale) * (2 * Real.log d.scale) ^ 4 *
        (2 * Real.log d.scale) ^ 16 := by
      gcongr <;> first | exact hphi | exact hr | exact hp | positivity
    _ = _ := by ring

def zeroGramPaymentConstant : ℝ :=
  48 * (|paperMass| + 1) * (8 / Real.log 2) * (2 : ℝ) ^ (21 : ℕ)

/-- The actual same-source Gram mismatch is paid before any filtered
variance is used. Threshold and constant precede all keys and residues.
The physical cap is deduced from the original medium range, not assumed. -/
theorem exists_actualZeroGramError_arbitrary_log (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → X ≤ d.scale →
        ‖actualZeroGramError d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨Xgate, hXgate, hgate⟩ := exists_roughZ_zeroGram_gate
  obtain ⟨Xratio, hXratio, hratio⟩ :=
    exists_roughZ_ratio_inverse_log_power (A + 21) (by linarith)
  let X := max (max Xgate Xratio)
    (max ((10 : ℝ) ^ (10 : ℕ)) (Real.exp (Real.exp 1) + Real.exp 1 + 1))
  have hconst : 0 < zeroGramPaymentConstant := by
    unfold zeroGramPaymentConstant
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨zeroGramPaymentConstant, X, hconst, ?_, ?_⟩
  · have he : 0 < Real.exp 1 := Real.exp_pos 1
    exact (by linarith : Real.exp (Real.exp 1) < Real.exp (Real.exp 1) + Real.exp 1 + 1).trans_le
      ((le_max_right _ _).trans (le_max_right _ _))
  intro B sigma kappa c0 d k hd hsigma hc0 hXd
  have hleft : max Xgate Xratio ≤ d.scale := (le_max_left _ _).trans hXd
  have hright : max ((10 : ℝ) ^ (10 : ℕ))
      (Real.exp (Real.exp 1) + Real.exp 1 + 1) ≤ d.scale := (le_max_right _ _).trans hXd
  obtain ⟨hz, hlarge⟩ := hgate d.scale ((le_max_left _ _).trans hleft)
  have hratio' := hratio d.scale ((le_max_right _ _).trans hleft)
  have hphysical := nativePhysicalCap_le_original_range hd hsigma
    (residue_ne_zero_of_original_c0 hd hc0) ((le_max_left _ _).trans hright)
  have hx : 1 ≤ d.scale := le_trans hXgate.le ((le_max_left _ _).trans hleft)
  have hlog : 1 ≤ Real.log d.scale := by
    have he : Real.exp 1 ≤ d.scale := by
      have h := (le_max_right _ _).trans hright
      linarith [Real.exp_pos (Real.exp 1)]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hLpos : 0 < Real.log d.scale := by linarith
  have hlogs := nativeZeroLogs_le_fixed_logs hd hx hlog hphysical
  have hV : 0 ≤ fixedDScale d ((2 : ℝ) ^ k.d) := by
    unfold fixedDScale
    have hM : 0 ≤ d.V := by linarith [hd.2.1]
    have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    positivity
  have hcancel : Real.log d.scale ^ (21 : ℕ) / Real.log d.scale ^ (A + 21) =
      Real.log d.scale ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hLpos]
    congr 1
    ring
  calc
    _ ≤ 48 * |paperMass| * roughEulerDelta d (roughZ d.scale) *
        fixedDScale d ((2 : ℝ) ^ k.d) * nativeZeroLogs d :=
      actualZeroGramError_le_native_logs hd hsigma hz hlarge k
    _ ≤ 48 * (|paperMass| + 1) *
        ((8 / Real.log 2) / Real.log d.scale ^ (A + 21)) *
        fixedDScale d ((2 : ℝ) ^ k.d) *
          ((2 : ℝ) ^ (21 : ℕ) * Real.log d.scale ^ (21 : ℕ)) := by
      have hdelta : 0 ≤ roughEulerDelta d (roughZ d.scale) := by
        unfold roughEulerDelta
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity
      have hlogs0 : 0 ≤ nativeZeroLogs d := by
        unfold nativeZeroLogs
        have hh := logBudget_nonneg (nativePhysicalCap d)
        positivity
      gcongr <;> first | linarith | exact hratio' | exact hlogs | positivity
    _ = zeroGramPaymentConstant *
        (fixedDScale d ((2 : ℝ) ^ k.d) * Real.log d.scale ^ (-A)) := by
      calc
        _ = zeroGramPaymentConstant * fixedDScale d ((2 : ℝ) ^ k.d) *
            (Real.log d.scale ^ (21 : ℕ) / Real.log d.scale ^ (A + 21)) := by
          unfold zeroGramPaymentConstant
          ring
        _ = _ := by rw [hcancel]; ring

end
end ImbalancedChen.Part3OriginalS2NativeZeroGramBudget
