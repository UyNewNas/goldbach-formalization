import ImbalancedChen.Part3ElementaryE1RealEndpoint
import Mathlib.Data.Int.Lemmas

/-!
SHIFTED FINITE TAU INTERVAL PAYMENT -- SOURCE ONLY -- UNCOMPILED -- HOLD

The first import is the exact future module root is preparing from the
real-endpoint E1 proposal, SHA3313e74df9d2e2c1ae36f320d1291bcf38d573f8046f1940e71f53017deb14b0.
Its actual sum_fouvryTau_E1_real_support is reused, not an assumed shifted
bound. No kernel acceptance or current import resolution is asserted here.

Native HighOmega itself has no shift-fiber theorem. Its actual successor
HighOmegaConvolution proves highOmega_shift_fiber_card_le and
highOmega_shift_sum_le. Their two-preimage argument is compatible with the
geometry here. Applying the global factor two separately on two intervals
would lose another factor two. Instead the two signs are injected separately,
using the existing Int.natAbs_inj_of_nonneg_of_nonneg and nonpos counterpart.
No absolute-shift fiber theorem is reproved or assumed.

The precise original source carrier is positive v<=floor(6*x), with the
integer equality v=a deleted BEFORE taking tau of the absolute difference.
For T=x^(1+kappa), x>=1,kappa>=0 gives 1<=x<=T. The positive-shift image lies
in [max 1 (-a), max 1 (-a+6*x)], and the negative image lies in
[max 1 (a-6*x), max 1 a]. Both lengths are <=6*x and both upper endpoints
are <=7*T. Clamping by 1 is legitimate because the nonzero integer shift
has natAbs>=1; it also treats an empty sign branch without extra hypotheses.

The final Ioc theorem matches the literal finite common-p fold carrier.
No replacement |a|<=x^2 is used, and there is no upper restriction on kappa.
The exact bound is 2*K*(6*x*L^(K-1)+Z^(1-1/K)*L^(K-2)), Z=7*T,L=1+log Z.
No Big-O/capped-kappa exponent, M2, spectrum, 7/32 or main theorem is proved.
All proof bodies are written below; actual Lean/runtime/pins remain frozen.
-/

namespace ImbalancedChen.Part3.ElementaryShiftedTau
noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment

def shiftedAbs (a : ℤ) (v : ℕ) : ℕ := ((v : ℤ) - a).natAbs

def shiftedSource (x : ℝ) (a : ℤ) : Finset ℕ :=
  (Icc 1 ⌊6 * x⌋₊).filter (fun v => (v : ℤ) ≠ a)

theorem shiftedSource_info {x : ℝ} (hx : 1 ≤ x) {a : ℤ} {v : ℕ}
    (hv : v ∈ shiftedSource x a) :
    1 ≤ (v : ℝ) ∧ (v : ℝ) ≤ 6 * x ∧ (v : ℤ) ≠ a ∧
      1 ≤ (shiftedAbs a v : ℝ) := by
  obtain ⟨hvI, hvne⟩ := Finset.mem_filter.mp hv
  obtain ⟨hv1, hvH⟩ := Finset.mem_Icc.mp hvI
  have hvR : (v : ℝ) ≤ (⌊6 * x⌋₊ : ℝ) := by exact_mod_cast hvH
  have hn0 : shiftedAbs a v ≠ 0 := Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hvne)
  have hn1 : 1 ≤ shiftedAbs a v := by omega
  exact ⟨by exact_mod_cast hv1, hvR.trans (Nat.floor_le (by linarith)), hvne,
    by exact_mod_cast hn1⟩

theorem shiftedAbs_real_of_le {a : ℤ} {v : ℕ} (h : a ≤ (v : ℤ)) :
    (shiftedAbs a v : ℝ) = (v : ℝ) - (a : ℝ) := by
  have hz : (shiftedAbs a v : ℤ) = (v : ℤ) - a :=
    Int.natAbs_of_nonneg (sub_nonneg.mpr h)
  exact_mod_cast hz

theorem shiftedAbs_real_of_ge {a : ℤ} {v : ℕ} (h : (v : ℤ) ≤ a) :
    (shiftedAbs a v : ℝ) = (a : ℝ) - (v : ℝ) := by
  have hz : (shiftedAbs a v : ℤ) = -((v : ℤ) - a) :=
    Int.ofNat_natAbs_of_nonpos (sub_nonpos.mpr h)
  have hR : (shiftedAbs a v : ℝ) = -((v : ℝ) - (a : ℝ)) := by exact_mod_cast hz
  linarith

theorem shiftedAbs_injOn_nonneg (S : Finset ℕ) (a : ℤ)
    (hS : ∀ v ∈ S, a ≤ (v : ℤ)) : Set.InjOn (shiftedAbs a) S := by
  intro v hv w hw heq
  have hdiff : (v : ℤ) - a = (w : ℤ) - a :=
    (Int.natAbs_inj_of_nonneg_of_nonneg
      (sub_nonneg.mpr (hS v hv)) (sub_nonneg.mpr (hS w hw))).mp heq
  exact_mod_cast ((Int.sub_left_inj a).mp hdiff)

theorem shiftedAbs_injOn_nonpos (S : Finset ℕ) (a : ℤ)
    (hS : ∀ v ∈ S, (v : ℤ) ≤ a) : Set.InjOn (shiftedAbs a) S := by
  intro v hv w hw heq
  have hdiff : (v : ℤ) - a = (w : ℤ) - a :=
    (Int.natAbs_inj_of_nonpos_of_nonpos
      (sub_nonpos.mpr (hS v hv)) (sub_nonpos.mpr (hS w hw))).mp heq
  exact_mod_cast ((Int.sub_left_inj a).mp hdiff)

/-- Clamping an interval at one preserves its width upper bound. -/
theorem clamped_interval_geometry {c H Z : ℝ} (hH : 0 ≤ H) (hZ : 1 ≤ Z)
    (hcZ : c + H ≤ Z) :
    1 ≤ max 1 c ∧ max 1 c ≤ max 1 (c + H) ∧
      max 1 (c + H) ≤ Z ∧ max 1 (c + H) - max 1 c ≤ H := by
  have hlo : 1 ≤ max 1 c := le_max_left _ _
  have hc : c ≤ max 1 c := le_max_right _ _
  have horder : max 1 c ≤ max 1 (c + H) := by
    apply max_le
    · exact le_max_left _ _
    · exact (by linarith : c ≤ c + H).trans (le_max_right _ _)
  have hupper : max 1 (c + H) ≤ max 1 c + H := by
    apply max_le <;> linarith
  exact ⟨hlo, horder, max_le hZ hcZ, by linarith⟩

/-- A true injection into a real-supported image pays one E1 interval. -/
theorem sum_image_in_clamped_interval_le (S : Finset ℕ) (f : ℕ → ℕ)
    {K : ℕ} (hK : 2 ≤ K) {c H Z : ℝ} (hH : 0 ≤ H) (hZ : 2 ≤ Z)
    (hcZ : c + H ≤ Z) (hinj : Set.InjOn f S)
    (hS : ∀ v ∈ S, max 1 c ≤ (f v : ℝ) ∧ (f v : ℝ) ≤ max 1 (c + H)) :
    (∑ v ∈ S, (fouvryTau K (f v) : ℝ)) ≤
      (K : ℝ) * (H * (1 + Real.log Z) ^ (K - 1) +
        Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)) := by
  have hg := clamped_interval_geometry hH (by linarith : 1 ≤ Z) hcZ
  have himage : ∀ n ∈ S.image f,
      max 1 c ≤ (n : ℝ) ∧ (n : ℝ) ≤ max 1 (c + H) := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    exact hS v hv
  have he1 := sum_fouvryTau_E1_real_support (S.image f) hK hg.1 hg.2.1 hZ hg.2.2.1 himage
  have hL : 0 ≤ 1 + Real.log Z := by
    have := Real.log_nonneg (by linarith : 1 ≤ Z)
    linarith
  calc
    (∑ v ∈ S, (fouvryTau K (f v) : ℝ)) =
        ∑ n ∈ S.image f, (fouvryTau K n : ℝ) := (Finset.sum_image hinj).symm
    _ ≤ (K : ℝ) * ((max 1 (c + H) - max 1 c) * (1 + Real.log Z) ^ (K - 1) +
        Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)) := he1
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_right hg.2.2.2 (pow_nonneg hL (K - 1)))
        (le_refl (Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2))))
      (Nat.cast_nonneg K)

/-- Finite shifted tau payment in the original near-linear moving-shift range. -/
theorem shifted_tau_Icc_sum_le {K : ℕ} (hK : 2 ≤ K) {x κ : ℝ}
    (hx : 1 ≤ x) (hκ : 0 ≤ κ) (a : ℤ) (ha : |(a : ℝ)| ≤ x ^ (1 + κ)) :
    (∑ v ∈ (Icc 1 ⌊6 * x⌋₊).filter (fun (v : ℕ) => (v : ℤ) ≠ a),
      (fouvryTau K ((v : ℤ) - a).natAbs : ℝ)) ≤
      2 * (K : ℝ) * (6 * x * (1 + Real.log (7 * x ^ (1 + κ))) ^ (K - 1) +
        (7 * x ^ (1 + κ)) ^ (1 - 1 / (K : ℝ)) *
          (1 + Real.log (7 * x ^ (1 + κ))) ^ (K - 2)) := by
  let T : ℝ := x ^ (1 + κ)
  let Z : ℝ := 7 * T
  let M : ℝ := 6 * x * (1 + Real.log Z) ^ (K - 1) +
    Z ^ (1 - 1 / (K : ℝ)) * (1 + Real.log Z) ^ (K - 2)
  let S := shiftedSource x a
  let P := S.filter (fun (v : ℕ) => a < (v : ℤ))
  let N := S.filter (fun (v : ℕ) => ¬a < (v : ℤ))
  change (∑ v ∈ S, (fouvryTau K (shiftedAbs a v) : ℝ)) ≤ 2 * (K : ℝ) * M
  have hxT : x ≤ T := by
    calc
      x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hT1 : 1 ≤ T := hx.trans hxT
  have hZ : 2 ≤ Z := by dsimp [Z]; linarith
  have haT : -T ≤ (a : ℝ) ∧ (a : ℝ) ≤ T := abs_le.mp ha
  have hPsign : ∀ v ∈ P, a ≤ (v : ℤ) := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2.le
  have hNsign : ∀ v ∈ N, (v : ℤ) ≤ a := by
    intro v hv
    exact le_of_not_gt (Finset.mem_filter.mp hv).2
  have hp : (∑ v ∈ P, (fouvryTau K (shiftedAbs a v) : ℝ)) ≤ (K : ℝ) * M := by
    apply sum_image_in_clamped_interval_le P (shiftedAbs a) hK
      (c := -(a : ℝ)) (H := 6 * x) (Z := Z) (by linarith) hZ
      (by dsimp [Z]; linarith [haT.1]) (shiftedAbs_injOn_nonneg P a hPsign)
    intro v hv
    have hi := shiftedSource_info hx (Finset.mem_filter.mp hv).1
    have he := shiftedAbs_real_of_le (hPsign v hv)
    constructor
    · exact max_le hi.2.2.2 (by linarith [hi.1])
    · exact (by linarith [hi.2.1] : (shiftedAbs a v : ℝ) ≤ -(a : ℝ) + 6 * x).trans
        (le_max_right _ _)
  have hn : (∑ v ∈ N, (fouvryTau K (shiftedAbs a v) : ℝ)) ≤ (K : ℝ) * M := by
    apply sum_image_in_clamped_interval_le N (shiftedAbs a) hK
      (c := (a : ℝ) - 6 * x) (H := 6 * x) (Z := Z) (by linarith) hZ
      (by dsimp [Z]; linarith [haT.2]) (shiftedAbs_injOn_nonpos N a hNsign)
    intro v hv
    have hi := shiftedSource_info hx (Finset.mem_filter.mp hv).1
    have he := shiftedAbs_real_of_ge (hNsign v hv)
    constructor
    · exact max_le hi.2.2.2 (by linarith [hi.2.1])
    · have hu : (shiftedAbs a v : ℝ) ≤ (a : ℝ) := by linarith [hi.1]
      exact hu.trans (by simpa only [sub_add_cancel] using
        (le_max_right (1 : ℝ) (a : ℝ)))
  have hsplit :
      (∑ v ∈ P, (fouvryTau K (shiftedAbs a v) : ℝ)) +
        (∑ v ∈ N, (fouvryTau K (shiftedAbs a v) : ℝ)) =
      ∑ v ∈ S, (fouvryTau K (shiftedAbs a v) : ℝ) :=
    Finset.sum_filter_add_sum_filter_not S (fun v => a < (v : ℤ))
      (fun v => (fouvryTau K (shiftedAbs a v) : ℝ))
  calc
    (∑ v ∈ S, (fouvryTau K (shiftedAbs a v) : ℝ)) =
        (∑ v ∈ P, (fouvryTau K (shiftedAbs a v) : ℝ)) +
          (∑ v ∈ N, (fouvryTau K (shiftedAbs a v) : ℝ)) := hsplit.symm
    _ ≤ (K : ℝ) * M + (K : ℝ) * M := add_le_add hp hn
    _ = 2 * (K : ℝ) * M := by ring

/-- The identical Ioc carrier used by the literal finite common-p folded sum. -/
theorem shifted_tau_Ioc_sum_le {K : ℕ} (hK : 2 ≤ K) {x κ : ℝ}
    (hx : 1 ≤ x) (hκ : 0 ≤ κ) (a : ℤ) (ha : |(a : ℝ)| ≤ x ^ (1 + κ)) :
    (∑ v ∈ (Ioc 0 ⌊6 * x⌋₊).filter (fun (v : ℕ) => (v : ℤ) ≠ a),
      (fouvryTau K ((v : ℤ) - a).natAbs : ℝ)) ≤
      2 * (K : ℝ) * (6 * x * (1 + Real.log (7 * x ^ (1 + κ))) ^ (K - 1) +
        (7 * x ^ (1 + κ)) ^ (1 - 1 / (K : ℝ)) *
          (1 + Real.log (7 * x ^ (1 + κ))) ^ (K - 2)) := by
  have hI : Ioc 0 ⌊6 * x⌋₊ = Icc 1 ⌊6 * x⌋₊ := by
    ext v
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hI]
  exact shifted_tau_Icc_sum_le hK hx hκ a ha

end
end ImbalancedChen.Part3.ElementaryShiftedTau
