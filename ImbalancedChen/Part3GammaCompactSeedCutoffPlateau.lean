import ImbalancedChen.Part3GammaSmoothMultiplierLegalTests
import ImbalancedChen.Part3Gamma0CompactCarrierBump
import ImbalancedChen.Part3ActualParabolicHighSeedLocalFinite

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A quantitative plateau of the ACTUAL global modular cutoff on a compact
seed and its entire integral modular orbit. The real height floor a and
ceiling b are derived from the original compact H set. On the OPEN band
(a/2,b+1), the pinned actual integer Mobius bound pays every image height
by max(b+1,2/a). The threshold has a strict margin and is fixed before the
point or the group element. Genuine constant-one germs are transported to
the full orbit, not inferred from a cutoff value at an isolated point.
-/

namespace ImbalancedChen.Part3.GammaCompactSeedCutoffPlateau20261026a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open Gamma0CompactCarrierBump20261025a
open ActualParabolicHighSeedLocalFinite20261025a
open ActualModularSmoothCuspCutoff20261025a
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a

/-- One fixed OPEN neighborhood of the original compact seed carrier. -/
def plateauBand (a b : ℝ) : Set UpperHalfPlane :=
  {z | a/2 < z.im ∧ z.im < b+1}

/-- Explicit strict margin over ALL integral-matrix image-height ceilings. -/
def plateauThreshold (a b : ℝ) : ℝ := max 2 (max (b+1) (2/a)) + 1

theorem plateauBand_isOpen (a b : ℝ) : IsOpen (plateauBand a b) :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const)

theorem plateauThreshold_pos (a b : ℝ) : 0 < plateauThreshold a b := by
  unfold plateauThreshold
  linarith [le_max_left (2:ℝ) (max (b+1) (2/a))]

theorem integral_height_le_band_ceiling (a b : ℝ) (ha : 0 < a)
    (z : UpperHalfPlane) (hz : z ∈ plateauBand a b) (g : SL(2,ℤ)) :
    (g • z).im ≤ max (b+1) (2/a) := by
  have hrecip : 1/z.im ≤ 2/a := by
    apply (div_le_div_iff₀ z.im_pos ha).mpr
    dsimp [plateauBand] at hz
    nlinarith [hz.1]
  exact (integral_smul_im_le g z).trans (max_le_max hz.2.le hrecip)

/-- Every genuine parabolic term vanishes on the whole open band; no
numerical high-cusp or eventual-tail estimate is being assumed. -/
theorem globalCutoff_eq_one_on_band (a b : ℝ) (ha : 0 < a)
    (Y : ℝ) (hY : plateauThreshold a b ≤ Y)
    (z : UpperHalfPlane) (hz : z ∈ plateauBand a b) : globalCutoff Y z = 1 := by
  have hYpos : 0 < Y := (plateauThreshold_pos a b).trans_le hY
  have hcap : max (b+1) (2/a) ≤ Y :=
    (le_max_right (2:ℝ) (max (b+1) (2/a))).trans
      ((le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans hY)
  have hzero : highTrace 1 Y z = 0 := by
    apply tsum_eq_zero.mpr
    intro q
    exact highProfile_eq_zero Y hYpos _ (parabolicRepresentative 1 q • z).im_pos.le
      ((integral_height_le_band_ceiling a b ha z hz
        (parabolicRepresentative 1 q : SL(2,ℤ))).trans hcap)
  simp only [globalCutoff, hzero, sub_zero]

theorem globalCutoff_germ_one_on_band (a b : ℝ) (ha : 0 < a)
    (Y : ℝ) (hY : plateauThreshold a b ≤ Y)
    (z : UpperHalfPlane) (hz : z ∈ plateauBand a b) :
    globalCutoff Y =ᶠ[𝓝 z] (fun _ => 1) := by
  filter_upwards [(plateauBand_isOpen a b).mem_nhds hz] with w hw
  exact globalCutoff_eq_one_on_band a b ha Y hY w hw

private theorem integralAction_continuous (g : SL(2,ℤ)) :
    Continuous (fun z : UpperHalfPlane => g • z) := by
  change Continuous (fun z : UpperHalfPlane => (SpecialLinearGroup.mapGL ℝ g) • z)
  exact continuous_const_smul _

/-- The ACTUAL full modular invariance transports the constant germ to
every group image. No support-invariance premise is required. -/
theorem globalCutoff_germ_one_on_integer_orbit (a b : ℝ) (ha : 0 < a)
    (Y : ℝ) (hY : plateauThreshold a b ≤ Y)
    (z : UpperHalfPlane) (hz : z ∈ plateauBand a b) (g : SL(2,ℤ)) :
    globalCutoff Y =ᶠ[𝓝 (g • z)] (fun _ => 1) := by
  have hpre : ∀ᶠ w in 𝓝 (g • z), g⁻¹ • w ∈ plateauBand a b :=
    (integralAction_continuous g⁻¹).continuousAt.eventually
      (by simpa only [inv_smul_smul] using (plateauBand_isOpen a b).mem_nhds hz)
  filter_upwards [hpre] with w hw
  have hone := globalCutoff_eq_one_on_band a b ha Y hY (g⁻¹ • w) hw
  rw [globalCutoff_sl2_invariant Y g⁻¹ w] at hone
  exact hone

/-- Compactness supplies the floor and ceiling BEFORE any point, matrix,
or cutoff scale is chosen. The threshold is the displayed explicit formula. -/
theorem exists_compact_seed_plateau_parameters {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ K ⊆ plateauBand a b ∧
      ∀ Y : ℝ, plateauThreshold a b ≤ Y → ∀ z ∈ K, ∀ g : SL(2,ℤ),
        globalCutoff Y =ᶠ[𝓝 (g • z)] (fun _ => 1) := by
  obtain ⟨A,a,b,_hA,ha,hab,hrect⟩ := compact_height_rectangle hK
  have hband : K ⊆ plateauBand a b := by
    intro z hz
    have hh := (hrect z hz).2
    constructor <;> linarith [hh.1, hh.2]
  exact ⟨a,b,ha,hab,hband,fun Y hY z hz g =>
    globalCutoff_germ_one_on_integer_orbit a b ha Y hY z (hband hz) g⟩

/-- Uniform full-orbit plateau endpoint, including empty compact carriers. -/
theorem exists_uniform_compact_orbit_plateau {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ Y0 : ℝ, 0 < Y0 ∧ ∀ Y : ℝ, Y0 ≤ Y → ∀ z ∈ K, ∀ g : SL(2,ℤ),
      globalCutoff Y =ᶠ[𝓝 (g • z)] (fun _ => 1) := by
  obtain ⟨a,b,ha,hab,hband,hgerm⟩ := exists_compact_seed_plateau_parameters hK
  exact ⟨plateauThreshold a b,plateauThreshold_pos a b,hgerm⟩

end
end ImbalancedChen.Part3.GammaCompactSeedCutoffPlateau20261026a
