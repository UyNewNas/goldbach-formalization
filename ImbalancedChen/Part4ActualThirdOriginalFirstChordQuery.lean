import ImbalancedChen.Part4ActualThirdOriginalCompactDomain
import ImbalancedChen.Certificates.RationalLogCertificate
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
SOURCEONLY / UNCOMPILED / OPEN30. A concrete original U2 query primitive.
Every off-grid rational query in (2, 2+1/16384) is enclosed using exactly the
first 112-bit ChordTable node, its original curvature allowance and both
outward division rounds. No node enclosure or final query bound is assumed.
This is one whole query cell, not a sampled rational evaluation and not the
complete [2,12] table. No adaptive tree, saved numerical bound, or replay is
claimed. K, C, rho, h, DEN=48000*2^24, kernel, domain and reserves are unchanged.
The actual first-interval Suzuki lower factor supplies the analytic formula;
the negative-delay gap DDE is not replaced by positive-delay Buchstab.
-/

namespace ImbalancedChen.OriginalU2FirstChordCellSourceOnly

noncomputable section
open Set
open Certificates
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Actual canonical lower factor on the original first analytic interval. -/
theorem actual_lower_eq_log {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    actualExtendedThirdLowerFactor s = Real.log (s - 1) / s := by
  have hA := suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract
  rw [actualExtendedThirdLowerFactor_of_two_le hs2, thirdTailLowerFactor,
    suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract hs2 hs4,
    suzukiLowerSieveFactorFirstInterval_eq_log hs2 hs4, hA]
  field_simp [ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]

private theorem log_plus_square_convex :
    ConvexOn ℝ (Ici 1) (fun t : ℝ => Real.log t + t^2 / 2) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun t : ℝ => t⁻¹ + t)
    (f'' := fun t : ℝ => 1 - (t^2)⁻¹) (convex_Ici 1)
  · have hl : ContinuousOn Real.log (Ici (1 : ℝ)) :=
      Real.continuousOn_log.mono (by
        intro x hx
        simp only [mem_compl_iff, mem_singleton_iff]
        change 1 ≤ x at hx
        linarith)
    exact hl.add ((continuous_id.pow 2).div_const 2).continuousOn
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    have hx0 : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
    have hd := (Real.hasDerivAt_log hx0).add (((hasDerivAt_id x).pow 2).div_const 2)
    have hd' : HasDerivAt (fun t : ℝ => Real.log t + t^2 / 2) (x⁻¹ + x) x :=
      hd.congr_deriv (by
        change x⁻¹ + (2 : ℝ) * x ^ (2 - 1) * 1 / 2 = x⁻¹ + x
        ring)
    exact hd'.hasDerivWithinAt
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    have hx0 : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
    have hd := (hasDerivAt_inv hx0).add (hasDerivAt_id x)
    have hd' : HasDerivAt (fun t : ℝ => t⁻¹ + t) (1 - (x^2)⁻¹) x :=
      hd.congr_deriv (by ring)
    exact hd'.hasDerivWithinAt
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    have hx2 : (1 : ℝ) ≤ x^2 := by nlinarith
    have h := (div_le_one (by nlinarith : (0 : ℝ) < x^2)).2 hx2
    simpa only [one_div, sub_nonneg] using h

/-- The exact one-sided log chord error used by the first original query cell.
Curvature is derived from the actual logarithm, not a certificate premise. -/
theorem log_first_chord {a h : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hh : 0 ≤ h) :
    a * Real.log (1 + h) ≤ Real.log (1 + a*h) ∧
      Real.log (1 + a*h) ≤ a * Real.log (1 + h) + h^2 / 8 := by
  have hconcave : ConcaveOn ℝ (Ioi (0 : ℝ)) Real.log :=
    _root_.strictConcaveOn_log_Ioi.concaveOn
  rcases hconcave with ⟨_, hchord⟩
  have hl := hchord
    (x := (1 : ℝ)) (y := 1 + h) (a := 1 - a) (b := a)
    (by norm_num : (1 : ℝ) ∈ Ioi 0)
    (by change 0 < 1 + h; linarith : 1 + h ∈ Ioi (0 : ℝ))
    (sub_nonneg.mpr ha1) ha0 (by ring : 1 - a + a = 1)
  rcases log_plus_square_convex with ⟨_, hupperChord⟩
  have hu := hupperChord
    (x := (1 : ℝ)) (y := 1 + h) (a := 1 - a) (b := a)
    (show (1 : ℝ) ∈ Ici (1 : ℝ) from (le_rfl : (1 : ℝ) ≤ 1))
    (by change 1 ≤ 1 + h; linarith : 1 + h ∈ Ici (1 : ℝ))
    (sub_nonneg.mpr ha1) ha0 (by ring : 1 - a + a = 1)
  have harg : (1-a)*1+a*(1+h) = 1+a*h := by ring
  simp only [smul_eq_mul, harg, Real.log_one, mul_zero, zero_add] at hl
  simp only [smul_eq_mul, harg, Real.log_one] at hu
  have he : (1-a)*(0+1^2/2)+a*(Real.log (1+h)+(1+h)^2/2) -
      (1+a*h)^2/2 = a*Real.log (1+h)+a*(1-a)*h^2/2 := by ring
  have herr : a*(1-a)*h^2/2 ≤ h^2/8 := by
    nlinarith [mul_nonneg (sq_nonneg (a-1/2)) (sq_nonneg h)]
  exact ⟨hl, by linarith only [hu, he, herr]⟩

/-- These are exactly weights(j)'s logarithm numerators at j=16384. -/
def P : ℤ := 2^112
def c : ℤ := 60*16384^4-30*16384^3+20*16384^2-15*16384
def d : ℤ := 60*16384^5
def firstLo : ℤ := c*P/d
def firstHi : ℤ := -(-((c+12)*P)/d)
def curvature : ℤ := 2^81

/-- In the first query cell, ceil(P/(8*n*(i-n))) is exact. -/
theorem curvature_eq_original :
    curvature = -(-P / (8*16384*(32768-16384))) ∧
    (curvature : ℝ)/(P : ℝ) = ((1/16384 : ℝ)^2)/8 := by
  norm_num [curvature, P]

def firstNodeCertificate : RationalLogCertificate where
  argument := 16385/16384
  terms := 4
  lower := (firstLo : ℚ)/(P : ℚ)
  upper := (firstHi : ℚ)/(P : ℚ)

/-- A finite rational check of the exact original first node, not an analytic
hypothesis or a record imported from a previous computation. -/
theorem firstNode_checked : firstNodeCertificate.check = true := by
  unfold RationalLogCertificate.check
  apply decide_eq_true
  norm_num [RationalLogCertificate.Valid, firstNodeCertificate, firstLo, firstHi,
    c, d, P, logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ]

theorem firstNode_encloses :
    (firstLo : ℝ)/(P : ℝ) ≤ Real.log (1+(1/16384 : ℝ)) ∧
      Real.log (1+(1/16384 : ℝ)) ≤ (firstHi : ℝ)/(P : ℝ) := by
  have h := firstNodeCertificate.check_sound firstNode_checked
  norm_num [firstNodeCertificate] at h ⊢
  exact h

def weight (q : ℚ) : ℚ := 16384*(q-2)
def numeratorLo (q : ℚ) : ℤ := ⌊(firstLo : ℚ)*weight q⌋
def numeratorHi (q : ℚ) : ℤ := ⌈(firstHi : ℚ)*weight q⌉ + curvature
def queryLo (q : ℚ) : ℤ := ⌊(numeratorLo q : ℚ)/q⌋
def queryHi (q : ℚ) : ℤ := ⌈(numeratorHi q : ℚ)/q⌉

/-- The rational divmod quotient is the original first nonconstant cell.
Its residual interpolation weight is n*q-32768 = n*(q-2). -/
theorem query_cell_index {q : ℚ} (hq0 : 2 < q) (hq1 : q < 2+1/16384) :
    ⌊q*16384⌋ = (32768 : ℤ) ∧ weight q = q*16384-32768 := by
  constructor
  · apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  · unfold weight
    ring

/-- All real numerator values in the first cell satisfy the original rounded
chord bound; no supplied endpoint interval or interpolation assertion occurs. -/
theorem numerator_encloses {q : ℚ} (hq0 : 2 ≤ q) (hq1 : q ≤ 2+1/16384) :
    (numeratorLo q : ℝ)/(P : ℝ) ≤ Real.log ((q : ℝ)-1) ∧
      Real.log ((q : ℝ)-1) ≤ (numeratorHi q : ℝ)/(P : ℝ) := by
  have hp : (0 : ℝ) < (P : ℝ) := by norm_num [P]
  have ha0Q : 0 ≤ weight q := by unfold weight; linarith
  have ha1Q : weight q ≤ 1 := by unfold weight; linarith
  have ha0 : (0 : ℝ) ≤ (weight q : ℝ) := by exact_mod_cast ha0Q
  have ha1 : (weight q : ℝ) ≤ 1 := by exact_mod_cast ha1Q
  have hc := log_first_chord ha0 ha1 (by norm_num : (0 : ℝ) ≤ 1/16384)
  have harg : (1 : ℝ)+(weight q : ℝ)*(1/16384) = (q : ℝ)-1 := by
    simp only [weight, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat]
    ring
  rw [harg] at hc
  have hlo : (numeratorLo q : ℝ) ≤ (firstLo : ℝ)*(weight q : ℝ) := by
    exact_mod_cast (Int.floor_le ((firstLo : ℚ)*weight q))
  have hhi : (firstHi : ℝ)*(weight q : ℝ) ≤
      (numeratorHi q : ℝ)-(curvature : ℝ) := by
    have hh := Int.le_ceil ((firstHi : ℚ)*weight q)
    have hhR : (firstHi : ℝ)*(weight q : ℝ) ≤
        (⌈(firstHi : ℚ)*weight q⌉ : ℤ) := by exact_mod_cast hh
    simpa [numeratorHi] using hhR
  have hlow := mul_le_mul_of_nonneg_right firstNode_encloses.1 ha0
  have hhigh := mul_le_mul_of_nonneg_right firstNode_encloses.2 ha0
  have hloDiv := div_le_div_of_nonneg_right hlo hp.le
  have hhiDiv := div_le_div_of_nonneg_right hhi hp.le
  have hcurv := curvature_eq_original.2
  constructor
  · calc
      (numeratorLo q : ℝ)/(P : ℝ) ≤
          ((firstLo : ℝ)/(P : ℝ))*(weight q : ℝ) := by
        simpa only [div_mul_eq_mul_div₀] using hloDiv
      _ ≤ (weight q : ℝ)*Real.log (1+(1/16384 : ℝ)) := by
        simpa only [mul_comm] using hlow
      _ ≤ Real.log ((q : ℝ)-1) := hc.1
  · have hh : (weight q : ℝ)*Real.log (1+(1/16384 : ℝ)) ≤
        (numeratorHi q : ℝ)/(P : ℝ)-(curvature : ℝ)/(P : ℝ) := by
      calc
        _ ≤ ((firstHi : ℝ)/(P : ℝ))*(weight q : ℝ) := by
          simpa only [mul_comm] using hhigh
        _ ≤ _ := by
          simpa only [div_mul_eq_mul_div₀, sub_div] using hhiDiv
    linarith only [hh, hc.2, hcurv]

/-- Original 112-bit off-grid lower-factor query soundness on one complete
nontrivial cell. Both outward division rounds match IndependentSieve.at. -/
theorem original_first_cell_query_encloses {q : ℚ}
    (hq0 : 2 < q) (hq1 : q < 2+1/16384) :
    (queryLo q : ℝ)/(P : ℝ) ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (queryHi q : ℝ)/(P : ℝ) := by
  have hp : (0 : ℝ) < (P : ℝ) := by norm_num [P]
  have hq0R : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq1R : (q : ℝ) < 2+1/16384 := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
      (Rat.cast_strictMono (K := ℝ) hq1)
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  rw [actual_lower_eq_log hq0R.le (by linarith)]
  have hn := numerator_encloses hq0.le hq1.le
  have hl : (queryLo q : ℝ) ≤ (numeratorLo q : ℝ)/(q : ℝ) := by
    exact_mod_cast (Int.floor_le ((numeratorLo q : ℚ)/q))
  have hu : (numeratorHi q : ℝ)/(q : ℝ) ≤ (queryHi q : ℝ) := by
    exact_mod_cast (Int.le_ceil ((numeratorHi q : ℚ)/q))
  constructor
  · calc
      (queryLo q : ℝ)/(P : ℝ) ≤ ((numeratorLo q : ℝ)/(q : ℝ))/(P : ℝ) :=
        div_le_div_of_nonneg_right hl hp.le
      _ = ((numeratorLo q : ℝ)/(P : ℝ))/(q : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hn.1 hqpos.le
  · calc
      _ ≤ ((numeratorHi q : ℝ)/(P : ℝ))/(q : ℝ) :=
        div_le_div_of_nonneg_right hn.2 hqpos.le
      _ = ((numeratorHi q : ℝ)/(q : ℝ))/(P : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hu hp.le

/-- The independent compact wrapper rescales 112-bit query numerators by
2^48 into its 160-bit interval format. This introduces no additional error. -/
theorem original_first_cell_160bit_query_encloses {q : ℚ}
    (hq0 : 2 < q) (hq1 : q < 2+1/16384) :
    (((queryLo q * 2^48 : ℤ) : ℝ) / 2^160) ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (((queryHi q * 2^48 : ℤ) : ℝ) / 2^160) := by
  have hs (k : ℤ) : (((k*2^48 : ℤ) : ℝ)/2^160) = (k : ℝ)/(P : ℝ) := by
    push_cast
    norm_num [P]
    ring
  rw [hs, hs]
  exact original_first_cell_query_encloses hq0 hq1

end
end ImbalancedChen.OriginalU2FirstChordCellSourceOnly

