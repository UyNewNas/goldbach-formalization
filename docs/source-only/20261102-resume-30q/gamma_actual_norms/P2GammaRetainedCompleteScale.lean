import ImbalancedChen.P2GammaRetainedActualNorms
import ImbalancedChen.P2GammaOriginalScaleTransport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual complete scales and original norm data for P's already implemented
conductor consumers. In particular x is lower(head)*lower(COMPLETE beta),
not the residual quotient and not a possibly short prime interval length.
The existing generic primitive-scale and threshold transport are imported,
not rewritten. Every new estimate below starts with literal retained rows.
-/

namespace ImbalancedChen.P2GammaRetainedCompleteScale
noncomputable section
open scoped Classical BigOperators
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2GammaOriginalCartesianMask
open P2GammaSmoothLogGrid P2GammaRetainedInteriorGeometry
open P2GammaRetainedActualNorms P2GammaOriginalScaleTransport
open P2GammaSmallConductorIntervalBridge P2GammaConvolutionLargeConductor
open P2GammaPrimeCharacterSW
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Wu2008DoubleSieve
open P5OriginalU5CausalFinite (pairSupport)

def Occupied (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l : ℕ) : Prop :=
  ∃ p ∈ headCarrier N t c, ∃ y ∈ rootComplementLabels N t (c::cs),
    complexWeight δ j p * betaLabel N t H δ j l y ≠ 0

/-- Nonoccupied rows are exactly zero for EVERY arithmetic test. Thus the
power-scale argument is used only where there is a physical witness. -/
theorem original_retained_row_zero_of_not_occupied {N c : ℕ} {t : ℕ × ℕ}
    {cs : List ℕ} (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    (j l : ℕ) (hn : ¬ Occupied N t c cs H δ j l) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (complexWeight δ j (labelHead x) *
        betaLabel N t H δ j l (labelComplement x)) *
          F (product (t.1*t.2) x))=0 := by
  rw [original_retained_row_eq_cartesian ht c cs hδ j l F]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro y hy
  have hz : complexWeight δ j p * betaLabel N t H δ j l y=0 := by
    by_contra hw
    exact hn ⟨p,hp,y,hy,hw⟩
  rw [hz,zero_mul]

/-- Actual complete-product bounds and both original factor floors. The
old marked pair remains inside the second factor. Each factor loses at
most the fixed dyadic factor two when passing to its lower endpoint. -/
theorem occupied_scale_geometry {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hN : 2 ≤ N) (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ Real.log 2) {j l : ℕ}
    (ho : Occupied N t c cs H δ j l) :
    H ≤ lower δ j * lower δ l ∧
    lower δ j * lower δ l ≤ (N : ℝ) ∧
    (N : ℝ)^(68/1135 : ℝ) ≤ 2*lower δ j ∧
    (N : ℝ)^(417/2500 : ℝ) ≤ 2*lower δ l := by
  obtain ⟨p,hp,y,hy,hw⟩ := ho
  have hlegal := retained_row_legal ht hδ hp hy hw
  have hfloors := original_two_factor_floors hN ht hlegal
  simp only [head_rebuild,complement_rebuild] at hfloors
  have hr : Retain N H δ j l y := by
    by_contra hn
    exact hw (by simp [betaLabel,hn])
  have hwp : weight δ j p ≠ 0 := by
    intro hz
    exact hw (by simp [complexWeight,hz])
  have hwm : weight δ l (product (t.1*t.2) y) ≠ 0 := by
    intro hz
    exact hw (by simp [betaLabel,hr,complexWeight,hz])
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (headCarrier_prime_and_target_deleted hp).1.pos
  have hm0 : (0 : ℝ) < product (t.1*t.2) y := by
    exact_mod_cast complement_product_pos ht hy
  have hpu := (weight_nonzero_support hδ hp0 j hwp).2
  have hmu := (weight_nonzero_support hδ hm0 l hwm).2
  have hendpoint (s : ℕ) : lower δ s ≤ upper δ s := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact ⟨hr.1,(mul_le_mul (hendpoint j) (hendpoint l)
      (lower_pos δ l).le (upper_pos δ j).le).trans hr.2.1,
    hfloors.1.trans (hpu.le.trans (upper_le_two_lower hwidth j)),
    hfloors.2.trans (hmu.le.trans (upper_le_two_lower hwidth l))⟩

/-- A fixed exponent, chosen before N and every moving marked pair or
grid index. This is the actual instance of the positive-factor hypothesis
of the existing conductor theorem. -/
theorem exists_occupied_power_threshold :
    ∃ T0 : ℝ, 2 ≤ T0 ∧ ∀ N : ℕ, T0 ≤ (N : ℝ) →
      ∀ t ∈ pairSupport N, ∀ c : ℕ, ∀ cs : List ℕ,
      ∀ H δ : ℝ, 0 < δ → 2*δ ≤ Real.log 2 → ∀ j l : ℕ,
      Occupied N t c cs H δ j l →
      (lower δ j*lower δ l)^(34/1135 : ℝ) ≤ lower δ j ∧
      (lower δ j*lower δ l)^(34/1135 : ℝ) ≤ lower δ l := by
  obtain ⟨T1,hT1⟩ := eventually_atTop.mp
    (eventually_power_le_fixed_multiple_power (34/1135) (68/1135) (1/2)
      (by norm_num) (by norm_num))
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp
    (eventually_power_le_fixed_multiple_power (34/1135) (417/2500) (1/2)
      (by norm_num) (by norm_num))
  refine ⟨max 2 (max T1 T2),le_max_left _ _,?_⟩
  intro N hNT t ht c cs H δ hδ hwidth j l ho
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := (le_max_left _ _).trans hNT
    exact_mod_cast this
  obtain ⟨_,hx,hM,hB⟩ := occupied_scale_geometry hN2 ht hδ hwidth ho
  have h1 := (hT1 (N : ℝ)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hNT))).2
  have h2 := (hT2 (N : ℝ)
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNT))).2
  have hxpow : (lower δ j*lower δ l)^(34/1135 : ℝ) ≤
      (N : ℝ)^(34/1135 : ℝ) :=
    Real.rpow_le_rpow (mul_pos (lower_pos δ j) (lower_pos δ l)).le hx (by norm_num)
  constructor
  · exact hxpow.trans (h1.trans (by nlinarith))
  · exact hxpow.trans (h2.trans (by nlinarith))

/-- The actual plateau-compatible lower cutoff H=2*N^(1-kappa) gives
the complete near-target scale and the target exponent needed by the
target-deleted prime supplier. No quotient-scale comparison is assumed. -/
theorem occupied_trim_complete_scale {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hN : 2 ≤ N) (ht : t ∈ pairSupport N) {kappa δ : ℝ} (hk : kappa < 1)
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) {j l : ℕ}
    (ho : Occupied N t c cs (2*(N : ℝ)^(1-kappa)) δ j l) :
    (N : ℝ)^(1-kappa) ≤ lower δ j*lower δ l ∧
    lower δ j*lower δ l ≤ (N : ℝ) ∧
    (N : ℝ) ≤ (lower δ j*lower δ l)^(1/(1-kappa)) := by
  obtain ⟨hh,hupper,_,_⟩ := occupied_scale_geometry hN ht hδ hwidth ho
  have hlower : (N : ℝ)^(1-kappa) ≤ lower δ j*lower δ l :=
    (by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (1-kappa)] :
      (N : ℝ)^(1-kappa) ≤ 2*(N : ℝ)^(1-kappa)).trans hh
  refine ⟨hlower,hupper,?_⟩
  have hk0 : 0 < 1-kappa := by linarith
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) (1-kappa))
    hlower (by positivity : 0 ≤ 1/(1-kappa))
  have hid : ((N : ℝ)^(1-kappa))^(1/(1-kappa))=(N : ℝ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    have he : (1-kappa)*(1/(1-kappa))=1 := by field_simp [hk0.ne']
    rw [he,Real.rpow_one]
  simpa only [hid] using hraise

/-- One original-N threshold supplies all complete-scale hypotheses for
the concrete retained trim. It precedes the marked pair, original word,
grid width and indices. The only input is a nonzero retained physical term. -/
theorem exists_trim_occupied_scale_threshold (kappa : ℝ) (hk : kappa < 1) :
    ∃ T0 : ℝ, 2 ≤ T0 ∧ ∀ N : ℕ, T0 ≤ (N : ℝ) →
      ∀ t ∈ pairSupport N, ∀ c : ℕ, ∀ cs : List ℕ,
      ∀ δ : ℝ, 0 < δ → 2*δ ≤ Real.log 2 → ∀ j l : ℕ,
      Occupied N t c cs (2*(N : ℝ)^(1-kappa)) δ j l →
      1 ≤ Real.log (lower δ j*lower δ l) ∧
      1 ≤ lower δ j ∧ 1 ≤ lower δ l ∧
      (lower δ j*lower δ l)^(34/1135 : ℝ) ≤ lower δ j ∧
      (lower δ j*lower δ l)^(34/1135 : ℝ) ≤ lower δ l ∧
      (N : ℝ)^(1-kappa) ≤ lower δ j*lower δ l ∧
      lower δ j*lower δ l ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (lower δ j*lower δ l)^(1/(1-kappa)) := by
  obtain ⟨Tp,hTp,hpower⟩ := exists_occupied_power_threshold
  obtain ⟨Tl,hTl,hlarge⟩ := exists_original_scale_common_threshold
    (Real.exp 1) (1-kappa) (by linarith)
  refine ⟨max Tp Tl,hTp.trans (le_max_left _ _),?_⟩
  intro N hNT t ht c cs δ hδ hwidth j l ho
  have hp := (le_max_left _ _).trans hNT
  have hl := (le_max_right _ _).trans hNT
  have hN2 : 2 ≤ N := by exact_mod_cast hTp.trans hp
  obtain ⟨hMpow,hBpow⟩ := hpower N hp t ht c cs _ δ hδ hwidth j l ho
  obtain ⟨hlower,hupper,htarget⟩ := occupied_trim_complete_scale hN2 ht hk hδ hwidth ho
  have hexp : Real.exp 1 ≤ lower δ j*lower δ l :=
    hlarge (N : ℝ) hl _ hlower
  have hlog : 1 ≤ Real.log (lower δ j*lower δ l) := by
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    simpa only [Real.log_exp] using h
  have hx1 : 1 ≤ lower δ j*lower δ l := by
    have h := Real.exp_le_exp.mpr (by linarith : 0 ≤ Real.log (lower δ j*lower δ l))
    simpa only [Real.exp_zero,Real.exp_log (mul_pos (lower_pos δ j) (lower_pos δ l))] using h
  have hp1 := Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 34/1135)
  exact ⟨hlog,hp1.trans hMpow,hp1.trans hBpow,hMpow,hBpow,hlower,hupper,htarget⟩

private theorem one_add_log_double_le {M B : ℝ} (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hlog : 1 ≤ Real.log (M*B)) :
    1+Real.log (2*B) ≤ 3*Real.log (M*B) := by
  have hB0 : 0 < B := by linarith
  have hBx : B ≤ M*B := by nlinarith
  have hlogs := Real.log_le_log hB0 hBx
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB0.ne']
  linarith

/-- All raw physical norm/cap premises of P's local conductor theorem,
with actual rows and complete scale x=M*B. Here D=(word.length+1)^2-1 and
E=word.length; one may take ea=2, eb=2*3^D, c=2, em=2*3^E. These constants
are fixed before the requested accuracy and the auxiliary quotient k. -/
theorem actual_retained_norm_data {N c i : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) (hi : i ∈ secondFunctionalMotherPrefixIndices)
    (hcs : (c::cs) ∈ secondFunctionalMotherGammaWords i)
    {H δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2)
    (j l : ℕ) (hM : 1 ≤ lower δ j) (hB : 1 ≤ lower δ l)
    (hlog : 1 ≤ Real.log (lower δ j*lower δ l))
    {u v : ℝ} (hv : v ≤ 2*lower δ j) :
    let D := ((c::cs).length+1)^2-1
    let E := (c::cs).length
    let a := paddedRow (primeSWInterval u v) (primeHeadCoefficient N δ j)
    let b := paddedRow (retainedComplementSupport N t c cs H δ j l)
      (retainedBeta N t c cs H δ j l)
    rowEnergy a 0 (Nat.floor (2*lower δ j)) ≤
      (2 : ℝ)^2*lower δ j*(Real.log (lower δ j*lower δ l))^D ∧
    rowEnergy b 0 (Nat.floor (2*lower δ l)) ≤
      (2*(3 : ℝ)^D)^2*lower δ l*(Real.log (lower δ j*lower δ l))^D ∧
    rowMass (retainedComplementSupport N t c cs H δ j l)
      (retainedBeta N t c cs H δ j l) ≤
      (2*(3 : ℝ)^E)*lower δ l*(Real.log (lower δ j*lower δ l))^E ∧
    (Nat.floor (2*lower δ j) : ℝ) ≤ (2 : ℝ)^2*lower δ j ∧
    (Nat.floor (2*lower δ l) : ℝ) ≤ (2 : ℝ)^2*lower δ l := by
  dsimp only
  let D := ((c::cs).length+1)^2-1
  let E := (c::cs).length
  have hp := prime_head_raw_norms N δ j (lower_pos δ j).le hv
  have hb := mother_retained_beta_raw_norms ht hi hcs hδ hwidth j l hB
  have hlogB := one_add_log_double_le hM hB hlog
  have hlogB0 : 0 ≤ 1+Real.log (2*lower δ l) := by
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2*lower δ l)
    linarith
  have hpowD : 1 ≤ (Real.log (lower δ j*lower δ l))^D := one_le_pow₀ hlog
  have h3D : 1 ≤ (3 : ℝ)^D := one_le_pow₀ (by norm_num)
  have hcoefficient : 2*(3 : ℝ)^D ≤ (2*(3 : ℝ)^D)^2 := by nlinarith
  refine ⟨hp.2.trans ?_,hb.2.trans ?_,hb.1.trans ?_,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hpowD (lower_pos δ j).le]
  · calc
      _ ≤ (2*lower δ l)*(3*Real.log (lower δ j*lower δ l))^D := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlogB0 hlogB D) (by positivity)
      _ = (2*(3 : ℝ)^D)*lower δ l*(Real.log (lower δ j*lower δ l))^D := by
        rw [mul_pow]
        ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefficient (lower_pos δ l).le)
          (pow_nonneg (by linarith : 0 ≤ Real.log (lower δ j*lower δ l)) D)
  · calc
      _ ≤ (2*lower δ l)*(3*Real.log (lower δ j*lower δ l))^E :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogB0 hlogB E) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · exact (Nat.floor_le (by positivity : 0 ≤ 2*lower δ j)).trans (by nlinarith [lower_pos δ j])
  · exact (Nat.floor_le (by positivity : 0 ≤ 2*lower δ l)).trans (by nlinarith [lower_pos δ l])

end
end ImbalancedChen.P2GammaRetainedCompleteScale
