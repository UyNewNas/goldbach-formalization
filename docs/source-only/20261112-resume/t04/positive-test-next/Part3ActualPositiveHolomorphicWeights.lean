import ImbalancedChen.Part3ActualGeneralJBessel
import ImbalancedChen.Part3OriginalFullModulusTestJets
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Integer-order ordinary Bessel functions and the even weight transform
of the original period-64 test in Drappeau (4.9). The estimates are at
the given positive scale. -/
namespace ImbalancedChen.Part3.ActualPositiveHolomorphicWeights20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open ActualGeneralJBesselSourceOnly GeneralComplexISeriesSourceOnly GeneralICoreDifferential20261025a
open OriginalFullModulusTestJets20261102

def intJ (n : ℕ) (q : ℝ) : ℂ := generalJ (n:ℂ) q

def moment (n : ℕ) (Φ : ℝ → ℂ) : ℂ := ∫ q in Ioi (0:ℝ), intJ n q*Φ q/(q:ℂ)

/-- The index j=0 denotes weight two. -/
def holWeight (j : ℕ) (Φ : ℝ → ℂ) : ℂ := 4*I^(2*(j+1))*moment (2*j+1) Φ

private theorem intJ_eq (n : ℕ) (q : ℝ) :
    intJ n q=((q/2:ℝ):ℂ)^n*generalICore (n:ℂ) (-(((q/2:ℝ):ℂ)^2)) := by
  simp only [intJ,generalJ,Complex.cpow_natCast]

theorem intJ_continuous (n : ℕ) : Continuous (intJ n) := by
  rw [funext (intJ_eq n)]
  exact (by fun_prop).mul ((continuous_generalICore (by simp : -1<(n:ℂ).re)).comp (by fun_prop))

/-- A single fixed-scale majorant, summable in the integer Bessel order. -/
def expMass (B : ℝ) : ℝ := ∑' k : ℕ, (B/2)^(2*k)/(k.factorial:ℝ)

private theorem expMass_summable (B : ℝ) : Summable (fun k : ℕ => (B/2)^(2*k)/(k.factorial:ℝ)) := by
  simpa only [pow_mul] using Real.summable_pow_div_factorial ((B/2)^2)

theorem expMass_nonneg (B : ℝ) : 0≤expMass B :=
  tsum_nonneg fun k => div_nonneg (by rw [pow_mul]; positivity) (Nat.cast_nonneg _)

private theorem coeff_bound (n k : ℕ) :
    ‖generalICoeff (n:ℂ) k‖ ≤ (n.factorial:ℝ)⁻¹/(k.factorial:ℝ) := by
  have H := generalICoeff_norm_le (show -1<(n:ℂ).re by simp) k
  rw [Complex.Gamma_nat_eq_factorial, norm_inv,Complex.norm_natCast,Complex.natCast_re] at H
  apply H.trans
  apply div_le_div_of_nonneg_left (inv_nonneg.mpr (Nat.cast_nonneg _))
    (by exact_mod_cast Nat.factorial_pos k)
  calc
    (k.factorial:ℝ)=1*(k.factorial:ℝ) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_pow₀ (by linarith only [Nat.cast_nonneg (R:=ℝ) n] : (1:ℝ)≤n+1)) (Nat.cast_nonneg _)

theorem intJ_bound (n : ℕ) {q B : ℝ} (hq : 0≤q) (hB : q≤B) :
    ‖intJ n q‖≤((B/2)^n/(n.factorial:ℝ))*expMass B := by
  let c := (B/2)^n/(n.factorial:ℝ)
  have b : 0≤B/2 := by linarith
  have h := generalJ_hasSum (show -1<(n:ℂ).re by simp) q
  have S := summable_norm_generalJ (show -1<(n:ℂ).re by simp) q
  change ‖generalJ (n:ℂ) q‖≤_
  rw [← h.tsum_eq]
  apply (norm_tsum_le_tsum_norm S).trans
  change _ ≤ c*expMass B
  rw [expMass,← tsum_mul_left]
  apply S.tsum_le_tsum _ ((expMass_summable B).mul_left c)
  intro k
  rw [generalJTerm,Complex.cpow_natCast,norm_mul,norm_pow,norm_mul,norm_mul,norm_pow,
    norm_pow,Complex.norm_real,Real.norm_of_nonneg (by linarith : 0≤q/2),norm_neg,norm_one,one_pow,one_mul]
  calc
    _ ≤ (B/2)^n*((n.factorial:ℝ)⁻¹/(k.factorial:ℝ)*(B/2)^(2*k)) := by
      gcongr <;> first | exact coeff_bound n k | linarith
    _ = c*((B/2)^(2*k)/(k.factorial:ℝ)) := by dsimp [c]; ring

private theorem input_support (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    tsupport (spectralTest ell Y)⊆Icc (Y/16) (16*Y) := fun _ h =>
  ⟨(spectralTest_tsupport_strict ell hY h).1.le,(spectralTest_tsupport_strict ell hY h).2.le⟩

theorem moment_L1 (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Integrable (fun q => intJ n q*spectralTest ell Y q/(q:ℂ)) (volume.restrict (Ioi 0)) := by
  have h := spectralTest_div_q_integrable ell hY
  have H := h.norm.integrableOn (s:=Ioi (0:ℝ))
  let D := ((16*Y/2)^n/(n.factorial:ℝ))*expMass (16*Y)
  apply (H.const_mul D).mono' (((intJ_continuous n).stronglyMeasurable.mul
    (spectralTest_contDiff ell Y).continuous.stronglyMeasurable).div Complex.continuous_ofReal.stronglyMeasurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  by_cases hq0 : spectralTest ell Y q=0
  · simp [hq0]
  · rw [mul_div_assoc,norm_mul]
    exact mul_le_mul_of_nonneg_right (intJ_bound n hq.le (input_support ell hY (subset_tsupport _ hq0)).2) (norm_nonneg _)

theorem moment_factorial (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,‖moment n (spectralTest ell Y)‖≤C*(8*Y)^n/(n.factorial:ℝ) := by
  let a := ∫ q in Ioi (0:ℝ), ‖spectralTest ell Y q/(q:ℂ)‖
  have ha : 0≤a := integral_nonneg fun _ => norm_nonneg _
  have H := (spectralTest_div_q_integrable ell hY).norm.integrableOn (s:=Ioi (0:ℝ))
  refine ⟨expMass (16*Y)*a,mul_nonneg (expMass_nonneg _) ha,fun n => ?_⟩
  let D := ((16*Y/2)^n/(n.factorial:ℝ))*expMass (16*Y)
  calc
    ‖moment n (spectralTest ell Y)‖ ≤ ∫ q in Ioi (0:ℝ),D*‖spectralTest ell Y q/(q:ℂ)‖ := by
      apply norm_integral_le_of_norm_le (H.const_mul D)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      by_cases z : spectralTest ell Y q=0
      · simp [z]
      · rw [mul_div_assoc,norm_mul]
        exact mul_le_mul_of_nonneg_right (intJ_bound n hq.le (input_support ell hY (subset_tsupport _ z)).2) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; dsimp [D,a]; rw [show 16*Y/2=8*Y by ring]; ring

/-- The contiguous relation uses precisely the original Gamma series. -/
theorem intJ_three_term (n : ℕ) (q : ℝ) :
    ((n:ℂ)+1)*intJ (n+1) q = ((q/2:ℝ):ℂ)*(intJ n q+intJ (n+2) q) := by
  let x : ℂ := ((q/2:ℝ):ℂ)
  let z := -(x^2)
  have H := generalICore_contiguous (nu:=(n:ℂ)) (show -1<(n:ℂ).re by simp) z
  simp only [intJ_eq,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  change ((n:ℂ)+1)*(x^(n+1)*generalICore ((n:ℂ)+1) z)=
    x*(x^n*generalICore (n:ℂ) z + x^(n+2)*generalICore ((n:ℂ)+2) z)
  rw [show (n:ℂ)+2=(n:ℂ)+1+1 by ring,H,pow_succ,pow_succ,pow_succ]
  dsimp only [z]
  ring

end
end ImbalancedChen.Part3.ActualPositiveHolomorphicWeights20261112

