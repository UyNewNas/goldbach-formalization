import ImbalancedChen.Part3OriginalS2OtherRoughConsumer
import ImbalancedChen.Part3MediumPrimitiveShiuTwoSigns
import ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual I product carrier is translated to the original signed Shiu
progression. The fixed order is twelve; every location, width, modulus
and threshold gate is derived here. Only the original primitive Shiu
boundary, with its Euler exponential intact, is an analytic input.
-/

namespace ImbalancedChen.Part3OriginalS2ShiftedTwelve

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2OtherRoughSource
open ImbalancedChen.Part3OriginalS2OtherRoughCounting
open ImbalancedChen.Part3OriginalS2OtherRoughMean
open ImbalancedChen.Part3OriginalS2OtherRoughConsumer
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3.MediumSignedShiftGCD20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuSigned20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuTwoSigns20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b

/-- Both displayed parameters equal 1/400. Keeping their original
arithmetic form makes the Shiu record projections definitionally stable. -/
abbrev S2PrimitiveShiu := PrimitiveShiuTauBoundary 12
  (((1 : ℝ) / 5) / (16 * ((3 + 1) + 1)))
  (((1 : ℝ) / 5) / (16 * ((3 + 1) + 1)))

def shiftedLow (d : MediumAtom) : ℤ := 1 - d.residue
def shiftedHigh (d : MediumAtom) : ℤ := (Nat.floor (5 * d.scale) : ℤ) - d.residue

/-- No absolute-value map is used for reindexing: opposite signed shifts
are distinct. Absolute value enters only the divisor weight. -/
theorem product_shift_image_subset (d : MediumAtom) (p : ℕ) (hp : 0 < p) :
    (productMultiples d p).image (fun v : ℕ => (v : ℤ) - d.residue) ⊆
      signedShiftProgression (shiftedLow d) (shiftedHigh d) p
        (naturalResidue (-d.residue) p) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hvI, hpv, hvne⟩ := Finset.mem_filter.mp hv
  obtain ⟨hvlo, hvhi⟩ := Finset.mem_Icc.mp hvI
  have hvloZ : (1 : ℤ) ≤ v := by exact_mod_cast hvlo
  have hvhiZ : (v : ℤ) ≤ (Nat.floor (5 * d.scale) : ℤ) := by exact_mod_cast hvhi
  have hv0 : Int.ModEq (p : ℤ) (v : ℤ) 0 := by
    change (v : ℤ) % (p : ℤ) = 0 % (p : ℤ)
    rw [Int.emod_eq_zero_of_dvd (by exact_mod_cast hpv), Int.zero_emod]
  have hshift : Int.ModEq (p : ℤ) ((v : ℤ) - d.residue) (-d.residue) := by
    simpa only [zero_sub] using hv0.sub (Int.ModEq.refl d.residue)
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_, ?_, ?_⟩
  · dsimp [shiftedLow, shiftedHigh]
    omega
  · exact sub_ne_zero.mpr hvne
  · exact hshift.trans (naturalResidue_modEq (-d.residue) p hp).symm

theorem actual_shifted_moment_le_signed (d : MediumAtom) (p C : ℕ) (hp : 0 < p) :
    (∑ v ∈ productMultiples d p, tau (shiftAbs d.residue v) ^ C) ≤
      ∑ w ∈ signedShiftProgression (shiftedLow d) (shiftedHigh d) p
        (naturalResidue (-d.residue) p), (w.natAbs.divisors.card : ℝ) ^ C := by
  have hinj : Set.InjOn (fun v : ℕ => (v : ℤ) - d.residue) (productMultiples d p) := by
    intro v hv w hw he
    have hcast : (v : ℤ) = (w : ℤ) := by omega
    exact_mod_cast hcast
  calc
    _ = ∑ w ∈ (productMultiples d p).image (fun v : ℕ => (v : ℤ) - d.residue),
        (w.natAbs.divisors.card : ℝ) ^ C := by
      rw [Finset.sum_image hinj]
      rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (product_shift_image_subset d p hp) (fun _ _ _ => by positivity)

/-- This threshold precedes B, sigma, kappa, c0, the residue, key and p.
The large exponent is deliberately harmless; no numerical evaluation of
this expression is needed to apply the theorem. -/
def shiuThreshold (hShiu : S2PrimitiveShiu) : ℝ :=
  max ((10 : ℝ) ^ (10 : ℕ)) ((2 * hShiu.X0 + 32) ^ (80 : ℕ))

theorem shiuThreshold_large (hShiu : S2PrimitiveShiu) {x : ℝ}
    (hx : shiuThreshold hShiu ≤ x) : (10 : ℝ) ^ (10 : ℕ) ≤ x :=
  (le_max_left _ _).trans hx

theorem shiuThreshold_root (hShiu : S2PrimitiveShiu) {x : ℝ}
    (hx : shiuThreshold hShiu ≤ x) :
    2 * hShiu.X0 + 32 ≤ x ^ ((1 : ℝ) / 80) := by
  have hbase : 0 ≤ 2 * hShiu.X0 + 32 := by linarith [hShiu.X0_lower]
  calc
    _ = ((2 * hShiu.X0 + 32) ^ (80 : ℕ)) ^ ((1 : ℝ) / 80) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity)
      ((le_max_right _ _).trans hx) (by norm_num)

theorem shifted_original_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hkappa : kappa ≤ 1)
    (hx : 8 ≤ d.scale) :
    shiftedLow d ≤ shiftedHigh d ∧
      ((shiftedHigh d : ℝ) - (shiftedLow d : ℝ)) ≤ 5 * d.scale ∧
      5 * d.scale ≤ d.scale ^ (3 : ℝ) ∧
      (shiftedHigh d : ℝ) ≤ d.scale ^ (3 : ℝ) ∧
      -(shiftedLow d : ℝ) ≤ d.scale ^ (3 : ℝ) := by
  have hxone : 1 ≤ d.scale := by linarith
  have hfloor : (Nat.floor (5 * d.scale) : ℝ) ≤ 5 * d.scale :=
    Nat.floor_le (by linarith)
  have hfloor1 : 1 ≤ Nat.floor (5 * d.scale) := Nat.le_floor (by linarith)
  have ha0 := hd.2.2.2.2.2.2.2.1
  have ha : (d.residue.natAbs : ℝ) ≤ d.scale ^ (2 : ℕ) := by
    calc
      _ ≤ d.scale ^ (1 + kappa) := ha0
      _ ≤ d.scale ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
      _ = _ := by norm_num
  have habs : |(d.residue : ℝ)| ≤ d.scale ^ (2 : ℕ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using ha
  have hloA := (abs_le.mp habs).1
  have hhiA := (abs_le.mp habs).2
  have hx23 : 5 * d.scale + d.scale ^ 2 ≤ d.scale ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ d.scale by linarith)
      (mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ d.scale + 2 by linarith))]
  have hcastL : (shiftedLow d : ℝ) = 1 - (d.residue : ℝ) := by
    simp [shiftedLow]
  have hcastU : (shiftedHigh d : ℝ) =
      (Nat.floor (5 * d.scale) : ℝ) - (d.residue : ℝ) := by
    simp [shiftedHigh]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [shiftedLow, shiftedHigh]
    have hfZ : (1 : ℤ) ≤ Nat.floor (5 * d.scale) := by exact_mod_cast hfloor1
    omega
  · rw [hcastL, hcastU]
    linarith
  · norm_num only [Real.rpow_natCast]
    nlinarith [sq_nonneg d.scale]
  · rw [hcastU]
    norm_num only [Real.rpow_natCast]
    linarith
  · rw [hcastL]
    norm_num only [Real.rpow_natCast]
    nlinarith

def shiftedLogBudget (hShiu : S2PrimitiveShiu) (x : ℝ) : ℝ :=
  uniformTwoSmallConstant 12 (by norm_num : (0 : ℝ) < 1 / 5)
      (by norm_num : (0 : ℝ) < 3 + 1) +
    2 * largeLogFactor 12 x (1 / 5) 3 hShiu.A

theorem shiftedLogBudget_nonneg (hShiu : S2PrimitiveShiu) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ shiftedLogBudget hShiu x := by
  have hs := (uniformTwoSmallConstant_pos 12 (by norm_num : (0 : ℝ) < 1 / 5)
    (by norm_num : (0 : ℝ) < 3 + 1)).le
  have hE := uniformEulerConstant_pos 12
  have hA := hShiu.A_pos
  have hlx := Real.log_nonneg hx
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold shiftedLogBudget largeLogFactor
  positivity

/-- The actual translated order-12 sum has the second x/p factor.
Every premise below is original source geometry or the classical Shiu
boundary. No shifted-moment or correction estimate is a hypothesis. -/
theorem actual_shifted_twelve_le
    (hShiu : S2PrimitiveShiu)
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (hc0 : 0 < c0) (hkappa : kappa ≤ 1) (z : ℝ) (k : Key)
    (hk : k ∈ keyBank d (strictReceiverCutoff z) (roughY d.scale))
    (hx : shiuThreshold hShiu ≤ d.scale)
    (p : ℕ) (hp : p ∈ commonPrimes d z k) :
    (∑ v ∈ productMultiples d p, tau (shiftAbs d.residue v) ^ 12) ≤
      (5 * d.scale / p) * (2 : ℝ) ^ (13 : ℕ) * shiftedLogBudget hShiu d.scale := by
  have hprime := (Finset.mem_filter.mp hp).2.1
  have hlarge := shiuThreshold_large hShiu hx
  have hx8 : 8 ≤ d.scale :=
    (by norm_num : (8 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ)).trans hlarge
  have hxone : 1 ≤ d.scale := by linarith
  have hxpos : 0 < d.scale := by linarith
  have hroot := shiuThreshold_root hShiu hx
  have hroot32 : 32 ≤ d.scale ^ ((1 : ℝ) / 80) := by linarith [hShiu.X0_lower]
  have hpow (t : ℝ) (ht : (1 : ℝ) / 80 ≤ t) :
      d.scale ^ ((1 : ℝ) / 80) ≤ d.scale ^ t :=
    Real.rpow_le_rpow_of_exponent_le hxone ht
  have h3 : 3 ≤ d.scale ^ ((1 : ℝ) / 5) :=
    (by linarith : (3 : ℝ) ≤ d.scale ^ ((1 : ℝ) / 80)).trans (hpow _ (by norm_num))
  have h16 : 16 < d.scale ^ (7 * ((1 : ℝ) / 5) / 16) :=
    (by linarith : (16 : ℝ) < d.scale ^ ((1 : ℝ) / 80)).trans_le (hpow _ (by norm_num))
  have h2 : 2 ≤ d.scale ^ (((1 : ℝ) / 5) / 4) :=
    (by linarith : (2 : ℝ) ≤ d.scale ^ ((1 : ℝ) / 80)).trans (hpow _ (by norm_num))
  have hcap := occupied_common_prime_le_four_fifths hd hsigma hc0 z k hk hlarge p hp
  have hf : (p : ℝ) ≤ (5 * d.scale) * d.scale ^ (-((1 : ℝ) / 5)) := by
    calc
      _ ≤ d.scale ^ ((4 : ℝ) / 5) := hcap
      _ ≤ 5 * d.scale ^ ((4 : ℝ) / 5) := by
        nlinarith [Real.rpow_nonneg hxpos.le ((4 : ℝ) / 5)]
      _ = _ := by
        conv_rhs => rw [← Real.rpow_one d.scale]
        rw [mul_assoc, ← Real.rpow_add hxpos]
        norm_num
  have hg := shifted_original_geometry hd hkappa hx8
  have hq1 : (1 : ℝ) ≤ reducedModulus p (naturalResidue (-d.residue) p) := by
    exact_mod_cast (show 1 ≤ reducedModulus p (naturalResidue (-d.residue) p) from
      reducedModulus_pos (r := naturalResidue (-d.residue) p) hprime.pos)
  have hX0 : hShiu.X0 ≤
      (reducedModulus p (naturalResidue (-d.residue) p) : ℝ) *
        d.scale ^ (((1 : ℝ) / 5) / 2) / 2 := by
    have hroot' := hpow (((1 : ℝ) / 5) / 2) (by norm_num)
    have hnonneg := Real.rpow_nonneg hxpos.le (((1 : ℝ) / 5) / 2)
    nlinarith [mul_le_mul_of_nonneg_right hq1 hnonneg]
  have hraw := original_signed_shifted_sum_compact_budget 12
    (L := shiftedLow d) (U := shiftedHigh d)
    (f := p) (r := naturalResidue (-d.residue) p)
    (x := d.scale) (δ := 1 / 5) (K := 3) (M := 5 * d.scale) hShiu
    hprime.pos hg.1 hx8 (by norm_num) (by norm_num) (by norm_num)
    hf hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 h3 h16 h2 hX0
  have hτ : (p.divisors.card : ℝ) = 2 := tau_prime hprime
  exact (actual_shifted_moment_le_signed d p 12 hprime.pos).trans
    (by simpa only [hτ, shiftedLogBudget] using hraw)

end
end ImbalancedChen.Part3OriginalS2ShiftedTwelve
