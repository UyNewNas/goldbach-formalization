import ImbalancedChen.Part3GammaCompactSeedCutoffPlateau
import ImbalancedChen.Part3ActualPoincareDirichletTrace

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The predecessor's quantitative compact-seed plateau is already complete.
This is the next primitive: its genuine constant-one neighborhood germ
forces the actual native first derivatives and Maass differential to
vanish on every integral modular image of the compact carrier. The same
statement holds for the square multiplier used in the original tests.
No derivative conclusion is drawn from a value at one point.
-/

namespace ImbalancedChen.Part3.GammaCompactOrbitCutoffJets20261026b

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0CompactGreenProductL120261025a
open ActualGamma0MaassDescent20261025a ActualPoincareDirichletTrace20261025a
open ActualPoincareMaassLocalFinite20261025a ActualModularSmoothCuspCutoff20261025a
open ActualModularCutoffMaassBudget20261025a GammaNativeMaassLeibniz20261026a
open GammaCompactSeedCutoffPlateau20261026a

/-- Transport an actual H-neighborhood germ to the positive coordinate
chart. The zero extension outside H plays no role near this point. -/
theorem extendUpper_germ_const (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (c : ℂ)
    (h : F =ᶠ[𝓝 z] (fun _ => c)) :
    extendUpper F =ᶠ[𝓝 (z.re,z.im)] (fun _ => c) := by
  have hc := (chartLift_continuousAt_positive z.im_pos).eventually
    (by simpa only [chartLift_pair] using h)
  have hp : ∀ᶠ p : ℝ × ℝ in 𝓝 (z.re,z.im), 0 < p.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos
  filter_upwards [hc,hp] with p hpc hpp
  rw [extendUpper_chartLift F p hpp]
  exact hpc

/-- Locality of the ACTUAL derivatives, including both true second
coordinate derivatives. Smoothness is unnecessary for this germ lemma. -/
theorem native_jet_zero_of_germ_const (F : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) (c : ℂ) (h : F =ᶠ[𝓝 z] (fun _ => c)) :
    nativeDx F z = 0 ∧ nativeDy F z = 0 ∧
      deriv (deriv (fun x : ℝ => extendUpper F (x,z.im))) z.re = 0 ∧
      deriv (deriv (fun y : ℝ => extendUpper F (z.re,y))) z.im = 0 ∧
      upperMaass F z = 0 := by
  have hg := extendUpper_germ_const F z c h
  have hx : (fun x : ℝ => extendUpper F (x,z.im)) =ᶠ[𝓝 z.re] (fun _ => c) :=
    (continuousAt_id.prodMk continuousAt_const).eventually hg
  have hy : (fun y : ℝ => extendUpper F (z.re,y)) =ᶠ[𝓝 z.im] (fun _ => c) :=
    (continuousAt_const.prodMk continuousAt_id).eventually hg
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [nativeDx,sliceDx,deriv_const] using hx.deriv_eq
  · simpa only [nativeDy,sliceDy,deriv_const] using hy.deriv_eq
  · simpa only [deriv_const] using hx.deriv.deriv_eq
  · simpa only [deriv_const] using hy.deriv.deriv_eq
  · change chartMaass (extendUpper F) (z.re,z.im) = 0
    rw [chartMaass_eq_of_eventuallyEq hg]
    simp only [chartMaass,deriv_const,add_zero,mul_zero,neg_zero]

theorem complexGlobalH_germ_one_of_real_germ (Y : ℝ) (z : UpperHalfPlane)
    (h : globalCutoff Y =ᶠ[𝓝 z] (fun _ => 1)) :
    complexGlobalH Y =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
  filter_upwards [h] with w hw
  simp only [complexGlobalH,hw,Complex.ofReal_one]

theorem complexGlobalH_square_germ_one (Y : ℝ) (z : UpperHalfPlane)
    (h : globalCutoff Y =ᶠ[𝓝 z] (fun _ => 1)) :
    complexGlobalH Y * complexGlobalH Y =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
  filter_upwards [complexGlobalH_germ_one_of_real_germ Y z h] with w hw
  simp only [Pi.mul_apply,hw,one_mul]

/-- Explicit predecessor threshold, uniform before the carrier point and
matrix, now with the genuinely derived native differential information. -/
theorem compact_orbit_cutoff_jets
    (a b : ℝ) (ha : 0 < a) (Y : ℝ) (hY : plateauThreshold a b ≤ Y)
    (z : UpperHalfPlane) (hz : z ∈ plateauBand a b) (g : SL(2,ℤ)) :
    let w := g • z
    complexGlobalH Y w = 1 ∧
      nativeDx (complexGlobalH Y) w = 0 ∧ nativeDy (complexGlobalH Y) w = 0 ∧
      upperMaass (complexGlobalH Y) w = 0 ∧
      nativeDx (complexGlobalH Y * complexGlobalH Y) w = 0 ∧
      nativeDy (complexGlobalH Y * complexGlobalH Y) w = 0 ∧
      upperMaass (complexGlobalH Y * complexGlobalH Y) w = 0 := by
  have h := globalCutoff_germ_one_on_integer_orbit a b ha Y hY z hz g
  have hc := complexGlobalH_germ_one_of_real_germ Y (g • z) h
  have hj := native_jet_zero_of_germ_const _ (g • z) 1 hc
  have hsq := native_jet_zero_of_germ_const _ (g • z) 1
    (complexGlobalH_square_germ_one Y (g • z) h)
  exact ⟨hc.eq_of_nhds,hj.1,hj.2.1,hj.2.2.2.2,hsq.1,hsq.2.1,hsq.2.2.2.2⟩

/-- The compact height floor and ceiling are obtained before Y, z and g.
The conclusion is a germ, so it remains suitable for further derivatives. -/
theorem exists_compact_orbit_cutoff_square_germs
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ K ⊆ plateauBand a b ∧
      ∀ Y : ℝ, plateauThreshold a b ≤ Y → ∀ z ∈ K, ∀ g : SL(2,ℤ),
        complexGlobalH Y * complexGlobalH Y =ᶠ[𝓝 (g • z)] (fun _ => (1 : ℂ)) := by
  obtain ⟨a,b,ha,hab,hband,hgerm⟩ := exists_compact_seed_plateau_parameters hK
  exact ⟨a,b,ha,hab,hband,fun Y hY z hz g =>
    complexGlobalH_square_germ_one Y (g • z) (hgerm Y hY z hz g)⟩

end
end ImbalancedChen.Part3.GammaCompactOrbitCutoffJets20261026b
