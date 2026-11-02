import ImbalancedChen.Part3OriginalZeroDifferenceSourcePayment
import ImbalancedChen.Part3ActualFixedFeatureCountGeometry
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import Mathlib.Tactic

/-! Source only / uncompiled / zero formal credit.
Uniform selectable divisor, preliminary-d and logarithmic costs for the
actual y=0 completed square at its original occupied owner. The retained
phase debit x^(5*kappa) is kept, squared only in the squared normalization.
No spectral or whole-medium estimate is an input.
-/

namespace ImbalancedChen.Part3.OriginalZeroDifferenceLogPayment20261102
noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open CommonSmoothCutoff ActualCompletedZeroPaymentSourceOnly
open ActualOriginalSpectralScales20261028 ActualSpectralDoubleCauchyNormalization20261028
open ActualOccupiedCountingScale20261102 ActualMediumVarianceAtomBindingSourceOnly
open ActualSpectralUniformGeometry20261028 ActualSpectralMonomialMargins20261028
open MediumGlobalDyadicOwnership20261028 OriginalLambdaTrimPoissonFamily20261028
open OriginalSourcePoissonFamilyDictionary20261028 MediumReceiverCutoffArithmetic20261028
open OriginalZeroDifferenceSourcePayment20261102
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem frequency_abs_bound {H : ℕ} {h : ℤ}
    (hh : h ∈ poissonNonzeroFrequencyWindow H) : h.natAbs ≤ H := by
  rcases mem_union.mp hh with hh | hh
  · obtain ⟨n,hn,rfl⟩ := mem_image.mp hh
    simpa only [Int.natAbs_natCast] using (mem_Icc.mp hn).2
  · obtain ⟨n,hn,rfl⟩ := mem_image.mp hh
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using (mem_Icc.mp hn).2

/-- The divisor argument is the genuine nonzero |h|s' from zeroCross.
The constant precedes every atom, receiver, owner and coefficient choice.
The original short-H geometry implies |h|s'<=8*x^2. -/
theorem keyZeroTau_free_epsilon {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → 0 ≤ sigma →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z,
        keyRealH atom k ≤ roughS k →
        (keyZeroTau atom k : ℝ) ≤ C * atom.scale^eta := by
  obtain ⟨K,hK,htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show 0 < eta/2 by positivity)
  refine ⟨K * (8 : ℝ)^(eta/2),by positivity,?_⟩
  intro B sigma kappa c0 atom hA hsigma z k hk hshort
  have hx := ActualFixedFeatureCountGeometrySourceOnly.actual_admissible_geometry hA hsigma
  have hx0 : 0 < atom.scale := zero_lt_one.trans_le hx.1
  have hS : 0 < roughS k := zero_lt_one.trans_le (rough_scales_one_le k).2
  have hSx : roughS k ≤ 2 * atom.scale :=
    (actual_rough_owner_geometry hA (strictReceiverCutoff z)
      (originalSmoothTrim atom) k hk).2.1.trans
        (mul_le_mul_of_nonneg_left hx.2.2.2.1 (by norm_num))
  let T := factorCarrier (roughS k)
  let W := poissonNonzeroFrequencyWindow (sourceKeyH atom k)
  have hpoint (ht : ℤ × ℕ) (hht : ht ∈ W ×ˢ T) :
      ((ht.1.natAbs * ht.2).divisors.card : ℝ) ≤
        (K * (8 : ℝ)^(eta/2)) * atom.scale^eta := by
    obtain ⟨hh,htmem⟩ := mem_product.mp hht
    have hhpos : 0 < ht.1.natAbs :=
      Int.natAbs_pos.mpr (zero_frequency_nonzero (sourceKeyH atom k) hh)
    have htpos : 0 < ht.2 := zero_factor_pos_small hS htmem
    have hhcap : (ht.1.natAbs : ℝ) ≤ 2 * atom.scale := by
      calc
        _ ≤ (sourceKeyH atom k : ℝ) := by exact_mod_cast frequency_abs_bound hh
        _ ≤ keyRealH atom k := Nat.floor_le (poisson_nonneg hA k).1
        _ ≤ roughS k := hshort
        _ ≤ _ := hSx
    have htcap : (ht.2 : ℝ) ≤ 4 * atom.scale := by
      have hn : (ht.2 : ℝ) ≤ Nat.floor (2 * roughS k) := by
        exact_mod_cast (mem_Icc.mp htmem).2
      exact (hn.trans (Nat.floor_le (by positivity))).trans (by linarith)
    have hn : 0 < ht.1.natAbs * ht.2 := mul_pos hhpos htpos
    have hncap : ((ht.1.natAbs * ht.2 : ℕ) : ℝ) ≤ 8 * atom.scale^2 := by
      rw [Nat.cast_mul]
      have hm := mul_le_mul hhcap htcap (Nat.cast_nonneg _) (by positivity)
      nlinarith only [hm]
    have hp : (atom.scale^2)^(eta/2) = atom.scale^eta := by
      rw [← Real.rpow_natCast_mul hx0.le]
      congr 1
      ring
    calc
      _ ≤ K * ((ht.1.natAbs * ht.2 : ℕ) : ℝ)^(eta/2) := by
        simpa only [fouvryTau_two] using htau _ hn
      _ ≤ K * (8 * atom.scale^2)^(eta/2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hncap (by positivity)) hK.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _),hp]
        ring
  change (((W ×ˢ T).sup (fun ht : ℤ × ℕ =>
    (ht.1.natAbs * ht.2).divisors.card) : ℕ) : ℝ) ≤ _
  by_cases hn : (W ×ˢ T).Nonempty
  · obtain ⟨ht,hht,heq⟩ := exists_mem_eq_sup _ hn
      (fun ht : ℤ × ℕ => (ht.1.natAbs * ht.2).divisors.card)
    rw [heq]
    exact hpoint ht hht
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hempty,sup_empty,Nat.bot_eq_zero,Nat.cast_zero]
    positivity

/-- Pay the actual preliminary d and log^5, at a threshold chosen before
all source parameters. This does not assume poissonLoss is a subpower. -/
theorem exists_poissonLoss_threshold (eta : ℝ) (heta : 0 < eta) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z,
        poissonLoss atom k ≤ atom.scale^eta := by
  obtain ⟨x1,hx1,hmargin⟩ := exists_actual_margin_threshold heta
  obtain ⟨x2,hlog⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow 16 5
      (by norm_num) (show 0 < eta/2 by positivity))
  refine ⟨max x1 x2,hx1.trans_le (le_max_left _ _),?_⟩
  intro B sigma kappa c0 atom hA hx z k hk
  obtain ⟨hX,hll,h8⟩ := hmargin atom.scale ((le_max_left _ _).trans hx)
  have hx0 : 0 < atom.scale := zero_lt_one.trans_le hX
  have hD : keyD k ≤ atom.scale^(eta/2) :=
    (occupied_keyD_le_trim_square (Real.rpow_nonneg hx0.le _) hk).trans
      (originalTrim_square_le hX heta hll)
  have hlog' : 16 * (Real.log atom.scale)^5 ≤ atom.scale^(eta/2) := by
    simpa only [Real.rpow_natCast] using hlog atom.scale ((le_max_right _ _).trans hx)
  calc
    poissonLoss atom k = keyD k * (16 * (Real.log atom.scale)^5) := by
      unfold poissonLoss; ring
    _ ≤ atom.scale^(eta/2) * atom.scale^(eta/2) :=
      mul_le_mul hD hlog' (by positivity) (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- Original y=0 squared source payment, including the ONCE-charged
retained-phase cost. The strict original D0 gap pays tau and d/log losses.
No zero-difference bound or source equality is among the premises. -/
theorem exists_normalizedZero_power_payment (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B sigma kappa c0 atom → kappa ≤ sigma/100 → x0 ≤ atom.scale →
        ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z, ∀ (A : ℕ)
          (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
          (∀ s ∈ factorCarrier (roughS k), ‖lambda s‖ ≤ 1) →
          (∀ h ∈ poissonNonzeroFrequencyWindow (sourceKeyH atom k), ‖omega h‖ ≤ 1) →
          atom.scale^(10*kappa) * normalizedZero A atom k lambda omega ≤
            C * atom.scale^(-5*sigma) := by
  obtain ⟨K,hK,htau⟩ := keyZeroTau_free_epsilon hsigma
  obtain ⟨xg,hxg,hgeom⟩ := exists_actual_spectral_geometry_threshold sigma hsigma
  obtain ⟨xl,hxl,hloss⟩ := exists_poissonLoss_threshold sigma hsigma
  refine ⟨576*K,by positivity,max xg xl,hxg.trans_le (le_max_left _ _),?_⟩
  intro B kappa c0 atom hA hkappa hx z k hk A lambda omega hlambda homega
  obtain ⟨hU,hV,hQ,hx1⟩ := scale_facts hA
  have hx0 : 0 < atom.scale := zero_lt_one.trans hx1
  obtain ⟨hD0,hB,hH,hshort⟩ := hgeom B kappa c0 atom hA ((le_max_left _ _).trans hx) z k hk
  have hS : 0 < roughS k := zero_lt_one.trans_le (rough_scales_one_le k).2
  have hsmall : keyRealH atom k ≤ roughS k := by
    have hratio : keyRealH atom k / roughS k ≤ 1 := by linarith
    simpa only [one_mul] using (div_le_iff₀ hS).mp hratio
  have ht := htau B sigma kappa c0 atom hA hsigma.le z k hk hsmall
  have hl := hloss B sigma kappa c0 atom hA ((le_max_right _ _).trans hx) z k hk
  have hd := (actual_D0_D1_D2_margins hA (strictReceiverCutoff z)
    (originalSmoothTrim atom) k hk).1.le
  have hd0 : 0 ≤ D0 atom k := by dsimp [D0]; positivity
  have hn := normalizedZero_le_D0 hA z k hk A lambda omega hlambda homega
  have hbound : normalizedZero A atom k lambda omega ≤
      72 * (K * atom.scale^sigma) * atom.scale^sigma * (8 * atom.scale^(-8*sigma)) := by
    exact hn.trans (mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) hl
        (poisson_nonneg hA k).2 (by positivity)) hd hd0 (by positivity))
  calc
    _ ≤ atom.scale^(10*kappa) *
        (72 * (K * atom.scale^sigma) * atom.scale^sigma * (8 * atom.scale^(-8*sigma))) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hx0.le _)
    _ = (576*K) * atom.scale^(10*kappa + sigma + sigma - 8*sigma) := by
      rw [show 10*kappa + sigma + sigma - 8*sigma =
        10*kappa + sigma + sigma + (-8*sigma) by ring]
      simp only [Real.rpow_add hx0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) (by positivity)

/-- Arbitrary log saving for the actual original normalized y=0 source.
The threshold is selected before B, atom, receiver, key and coefficients. -/
theorem exists_normalizedZero_log_payment (sigma L : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → kappa ≤ sigma/100 → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z, ∀ (A : ℕ)
        (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        (∀ s ∈ factorCarrier (roughS k), ‖lambda s‖ ≤ 1) →
        (∀ h ∈ poissonNonzeroFrequencyWindow (sourceKeyH atom k), ‖omega h‖ ≤ 1) →
        atom.scale^(10*kappa) * normalizedZero A atom k lambda omega ≤
          1 / Real.log atom.scale^L := by
  obtain ⟨C,hC,xp,hxp,hpower⟩ := exists_normalizedZero_power_payment sigma hsigma
  obtain ⟨xl,hlog⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow C L hC.le
      (show 0 < 5*sigma by positivity))
  refine ⟨max xp xl,hxp.trans_le (le_max_left _ _),?_⟩
  intro B kappa c0 atom hA hkappa hx z k hk A lambda omega hlambda homega
  have hx1 := (scale_facts hA).2.2.2
  have hx0 : 0 < atom.scale := zero_lt_one.trans hx1
  have hlogpos : 0 < Real.log atom.scale := Real.log_pos hx1
  have hp := hpower B kappa c0 atom hA hkappa ((le_max_left _ _).trans hx)
    z k hk A lambda omega hlambda homega
  apply hp.trans
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogpos L)).mpr
  calc
    (C * atom.scale^(-5*sigma)) * Real.log atom.scale^L =
        (C * Real.log atom.scale^L) * atom.scale^(-5*sigma) := by ring
    _ ≤ atom.scale^(5*sigma) * atom.scale^(-5*sigma) :=
      mul_le_mul_of_nonneg_right (hlog atom.scale ((le_max_right _ _).trans hx))
        (Real.rpow_nonneg hx0.le _)
    _ = 1 := by rw [← Real.rpow_add hx0,show 5*sigma + -5*sigma = 0 by ring,Real.rpow_zero]

end
end ImbalancedChen.Part3.OriginalZeroDifferenceLogPayment20261102
