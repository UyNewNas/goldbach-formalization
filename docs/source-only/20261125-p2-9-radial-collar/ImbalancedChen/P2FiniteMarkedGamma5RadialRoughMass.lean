import ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformFixedCompat

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The existing radial endpoint argument at the actual frozen-history
cutoff exponent divided by two. The unrestricted finite-band theorem is
imported from the already supplied FixedCompat module. No Buchstab or PNT
estimate is re-proved here. The band index is a fixed symbolic natural
number, chosen before N, with no cap of 100.

The absolute physical shell is measured in M/N. Its width is fixed while
N tends to infinity, as required by the 1106 positive outer-approximation
argument. An exponent-coordinate measure-zero statement is not used.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass
noncomputable section
open Filter Finset Real LiLiuPrereqBuchstab
open Part5OriginalH430FrozenRootRefinement
open scoped Classical Topology BigOperators

def cutExponent : ℝ := frozenLeafCutoffFloor / 2
def cut (N : ℕ) : ℝ := (N : ℝ) ^ cutExponent
def norm (N : ℕ) : ℝ := log (N : ℝ) / (N : ℝ)
def shell (N : ℕ) (b c : ℝ) : Finset ℕ :=
  roughNumbers (c * (N : ℝ)) (cut N) \ roughNumbers (b * (N : ℝ)) (cut N)

theorem cutExponent_pos : 0 < cutExponent :=
  half_pos frozenLeafCutoffFloor_pos

theorem cutExponent_lt_one : cutExponent < 1 := by
  have hpow : (1 : ℝ) ≤ (101 : ℝ) ^ 440 := one_le_pow₀ (by norm_num)
  have hres : frozenResidualFloor ≤ 11 / 384 := by
    unfold frozenResidualFloor
    exact div_le_self (by norm_num) hpow
  unfold cutExponent frozenLeafCutoffFloor
  linarith only [hres]

theorem one_le_inv_cutExponent : 1 ≤ cutExponent⁻¹ := by
  simpa only [one_div] using (one_le_div cutExponent_pos).mpr cutExponent_lt_one.le

theorem cut_tendsto : Tendsto cut atTop atTop :=
  (tendsto_rpow_atTop cutExponent_pos).comp tendsto_natCast_atTop_atTop

private def bandRank : ℕ := Nat.ceil cutExponent⁻¹ + 1

private theorem one_lt_cutExponent_mul_bandRank :
    1 < cutExponent * (bandRank : ℝ) := by
  have hr : cutExponent⁻¹ < (bandRank : ℝ) := by
    dsimp only [bandRank]
    rw [Nat.cast_add, Nat.cast_one]
    linarith only [Nat.le_ceil cutExponent⁻¹]
  have hh := mul_lt_mul_of_pos_left hr cutExponent_pos
  simpa only [mul_inv_cancel₀ cutExponent_pos.ne'] using hh

private theorem cut_div_N :
    Tendsto (fun N : ℕ => cut N / (N : ℝ)) atTop (𝓝 0) := by
  apply ((tendsto_rpow_neg_atTop (sub_pos.mpr cutExponent_lt_one)).comp
    tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have h0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  change (N : ℝ) ^ (-(1 - cutExponent)) = (N : ℝ) ^ cutExponent / (N : ℝ)
  rw [show -(1 - cutExponent) = cutExponent - 1 by ring, rpow_sub h0, rpow_one]

private theorem parameters {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => log (c * (N : ℝ)) / log (cut N))
      atTop (𝓝 cutExponent⁻¹) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => (cutExponent⁻¹ * log c) / log (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hh := hsmall.const_add cutExponent⁻¹
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  simp only [cut, log_mul hc.ne' h0.ne', log_rpow h0]
  field_simp [cutExponent_pos.ne', (log_pos hNr).ne'] <;> ring

/-- Actual rough-integer endpoint, including its full absolute error.
The fixed band may be as large as the original cutoff requires. -/
theorem endpoint {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => norm N * (roughCount (c * (N : ℝ)) (cut N) : ℝ))
      atTop (𝓝 (cutExponent⁻¹ * c * buchstab cutExponent⁻¹)) := by
  let C := buchstabBandConstant bandRank
  let main := fun N : ℕ =>
    cutExponent⁻¹ * c * buchstab (log (c * (N : ℝ)) / log (cut N))
  let error := fun N : ℕ =>
    (cutExponent⁻¹ * C) * (c * buchstabRemainder (cut N) + cut N / (N : ℝ))
  let X := fun N : ℕ => norm N * (roughCount (c * (N : ℝ)) (cut N) : ℝ)
  have hmain : Tendsto main atTop (𝓝 (cutExponent⁻¹ * c * buchstab cutExponent⁻¹)) :=
    ((continuous_buchstab.tendsto cutExponent⁻¹).comp (parameters hc)).const_mul _
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [error, Function.comp_apply, mul_zero, zero_add] using
      ((((tendsto_buchstabRemainder.comp cut_tendsto).const_mul c).add cut_div_N).const_mul
        (cutExponent⁻¹ * C))
  have hpow := (tendsto_rpow_atTop
    (sub_pos.mpr one_lt_cutExponent_mul_bandRank)).comp tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ N : ℕ in atTop, |X N - main N| ≤ error N := by
    filter_upwards [eventually_gt_atTop (1 : ℕ),
      cut_tendsto.eventually_ge_atTop primeErrorStart,
      cut_div_N.eventually (gt_mem_nhds hc), hpow.eventually_ge_atTop c]
      with N hN hstart hlo hhi
    have hNr : (1 : ℝ) < N := by exact_mod_cast hN
    have h0 := zero_lt_one.trans hNr
    have hL := log_pos hNr
    have hlogcut : log (cut N) = cutExponent * log (N : ℝ) := log_rpow h0 _
    have hhigh : c * (N : ℝ) ≤ cut N ^ bandRank := by
      have hh := mul_le_mul_of_nonneg_right hhi h0.le
      calc
        _ ≤ (N : ℝ) ^ (cutExponent * (bandRank : ℝ) - 1) * (N : ℝ) := hh
        _ = (N : ℝ) ^ ((cutExponent * (bandRank : ℝ) - 1) + 1) := by
          rw [rpow_add h0, rpow_one]
        _ = cut N ^ bandRank := by
          rw [show (cutExponent * (bandRank : ℝ) - 1) + 1 =
            cutExponent * (bandRank : ℝ) by ring, rpow_mul h0.le, rpow_natCast] <;> rfl
    have hlow : cut N < c * (N : ℝ) := (div_lt_iff₀ h0).mp hlo
    have hm := roughCount_buchstab_band_error_unrestricted bandRank hstart hlow.le hhigh
    have hnorm : 0 ≤ norm N := div_nonneg hL.le h0.le
    have heq : X N - main N = norm N *
        ((roughCount (c * (N : ℝ)) (cut N) : ℝ) -
          (c * (N : ℝ)) * buchstab (log (c * (N : ℝ)) / log (cut N)) / log (cut N)) := by
      dsimp only [X, main, norm]
      rw [hlogcut]
      field_simp [cutExponent_pos.ne', h0.ne', hL.ne'] <;> ring
    rw [heq, abs_mul, abs_of_nonneg hnorm]
    apply (mul_le_mul_of_nonneg_left hm hnorm).trans_eq
    dsimp only [norm, error, C]
    rw [hlogcut]
    field_simp [cutExponent_pos.ne', h0.ne', hL.ne'] <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hmain.sub herror)
    (by simpa only [add_zero] using hmain.add herror)
  · filter_upwards [hb] with N hN
    linarith only [(abs_le.mp hN).1]
  · filter_upwards [hb] with N hN
    linarith only [(abs_le.mp hN).2]

theorem mem_shell {N M : ℕ} {b c : ℝ} :
    M ∈ shell N b c ↔ 0 < M ∧ b * (N : ℝ) < (M : ℝ) ∧
      (M : ℝ) ≤ c * (N : ℝ) ∧ Rough (cut N) M := by
  change M ∈ (roughNumbers (c * (N : ℝ)) (cut N) \
    roughNumbers (b * (N : ℝ)) (cut N) : Finset ℕ) ↔ _
  rw [Finset.mem_sdiff, LiLiuPrereqBuchstab.mem_roughNumbers,
    LiLiuPrereqBuchstab.mem_roughNumbers]
  constructor
  · rintro ⟨⟨hM, hhi, hr⟩, he⟩
    exact ⟨hM, lt_of_not_ge (fun h => he ⟨hM, h, hr⟩), hhi, hr⟩
  · rintro ⟨hM, hlo, hhi, hr⟩
    exact ⟨⟨hM, hhi, hr⟩, fun h => (not_le_of_gt hlo) h.2.1⟩

theorem shell_limit {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c) :
    Tendsto (fun N : ℕ => norm N * ((shell N b c).card : ℝ)) atTop
      (𝓝 (cutExponent⁻¹ * (c - b) * buchstab cutExponent⁻¹)) := by
  have h := (endpoint (hb.trans_le hbc)).sub (endpoint hb)
  have he : cutExponent⁻¹ * c * buchstab cutExponent⁻¹ -
      cutExponent⁻¹ * b * buchstab cutExponent⁻¹ =
      cutExponent⁻¹ * (c - b) * buchstab cutExponent⁻¹ := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [] with N
  have hs : roughNumbers (b * (N : ℝ)) (cut N) ⊆
      roughNumbers (c * (N : ℝ)) (cut N) := by
    intro m hm
    obtain ⟨hm0, hmle, hr⟩ := mem_roughNumbers.mp hm
    exact mem_roughNumbers.mpr ⟨hm0,
      hmle.trans (mul_le_mul_of_nonneg_right hbc (Nat.cast_nonneg N)), hr⟩
  have hh := card_sdiff_add_card_eq_card hs
  have hcast : ((shell N b c).card : ℝ) + (roughCount (b * (N : ℝ)) (cut N) : ℝ) =
      (roughCount (c * (N : ℝ)) (cut N) : ℝ) := by exact_mod_cast hh
  rw [← hcast]
  ring

/-- Nonzero original profile coordinates are > N^a/2. Eventually that
same floor is above N^(a/2); no extra positive-exponent assumption is
introduced for an actual source. -/
theorem eventually_cut_le_half_floor :
    ∀ᶠ N : ℕ in atTop, cut N ≤ (N : ℝ) ^ frozenLeafCutoffFloor / 2 := by
  filter_upwards [cut_tendsto.eventually_ge_atTop 2,
    eventually_gt_atTop (0 : ℕ)] with N hlarge hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsq : (N : ℝ) ^ frozenLeafCutoffFloor = cut N ^ 2 := by
    rw [show frozenLeafCutoffFloor = cutExponent * (2 : ℝ) by
      unfold cutExponent; ring, rpow_mul hN0.le] <;> rfl
  have hprod := mul_le_mul_of_nonneg_right hlarge
    (show 0 ≤ cut N by linarith only [hlarge])
  rw [← pow_two, ← hsq] at hprod
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    (by simpa only [mul_comm] using hprod)

end
end ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass
