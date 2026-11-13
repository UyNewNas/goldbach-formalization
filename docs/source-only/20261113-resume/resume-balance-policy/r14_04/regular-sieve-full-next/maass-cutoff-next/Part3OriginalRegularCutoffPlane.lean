import ImbalancedChen.Part3OriginalRegularCutoffAngularMass
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The genuine compact frequency-one seed as a bounded multiplier of
the physical Bruhat plane. All r have the same absolute angular price. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCutoffPlane20261113
open Real Set Filter Complex MeasureTheory
open scoped Topology
open OriginalPositiveScalarGeometry20261112 (plane induced)
open OriginalRegularPreKuznetsovPolar20261113 (physical compact_profile)
open OriginalRegularPreKuznetsovSeed20261113 (seed)
open OriginalRegularCutoffAngularMass20261113
open ActualUnitBandHeightSeeds20261112 (window window_bounds window_eventually)
open ActualInfinityCuspAnnihilator20261026b (HeightSeed)
open OriginalAbelOrbit (heights)
open private raw half from ImbalancedChen.Part3OriginalRegularPreKuznetsovInduced

def compact (r : ℝ) (j : ℕ) : HeightSeed := (seed (2*Real.pi) r j).toHeightSeed
def fullPair (r a b : ℝ) : ℂ := physical 0 r a*star (physical 0 r b)
def cutoffPair (j : ℕ) (r a b : ℝ) : ℂ := (compact r j).toFun a*star ((compact r j).toFun b)
def cutoffValue (j : ℕ) (r u : ℝ) := induced (cutoffPair j r) u
def fullValue (r u : ℝ) := induced (fullPair r) u

private def clipping (j : ℕ) (p : ℝ) (z : ℝ×ℝ) : ℝ :=
  window j (Real.log (2*Real.pi*z.2))*
  window j (Real.log (2*Real.pi*(p^2*z.2/(z.1^2+z.2^2))))

private def clipped (j : ℕ) (p r : ℝ) (z : ℝ×ℝ) : ℂ :=
  (clipping j p z:ℂ)*raw 0 p r z

private theorem clipping_le (j : ℕ) (p : ℝ) (z : ℝ×ℝ) : 0≤clipping j p z ∧ clipping j p z≤1 :=
  ⟨mul_nonneg (window_bounds _ _).1 (window_bounds _ _).1,
    mul_le_one₀ (window_bounds _ _).2 (window_bounds _ _).1 (window_bounds _ _).2⟩

private theorem clipped_eq {p : ℝ} (hp : 0<p) (j : ℕ) (r : ℝ) (z : ℝ×ℝ) :
    clipped j p r z=half.indicator (fun w => plane (cutoffPair j r) (p^2) w.1 w.2) z := by
  by_cases h : z∈half
  · have h0 : 0<z.2 := h
    have d0 : 0<z.1^2+z.2^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos h0)
    have b0 := div_pos (mul_pos (sq_pos_of_pos hp) h0) d0
    rw [clipped,raw,indicator_of_mem h,indicator_of_mem h]
    change (clipping j p z:ℂ)*plane (fullPair r) (p^2) z.1 z.2=plane (cutoffPair j r) (p^2) z.1 z.2
    dsimp only [clipping,plane,cutoffPair,compact,fullPair]
    rw [compact_profile r j h0,compact_profile r j b0,star_mul']
    simp only [Complex.star_def,Complex.conj_ofReal,Complex.real_smul,Complex.ofReal_mul]
    ring
  · simp only [clipped,raw,indicator_of_notMem h,mul_zero]

private theorem clip_bound (j : ℕ) (p r : ℝ) (z : ℝ×ℝ) :
    ‖clipped j p r z‖≤‖raw 0 p r z‖ := by
  rw [clipped,norm_mul,Complex.norm_real,Real.norm_of_nonneg (clipping_le j p z).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (clipping_le j p z).2

private theorem clipped_integrable {p : ℝ} (hp : 0<p) (j : ℕ) (r : ℝ) : Integrable (clipped j p r) := by
  apply (raw_integrable hp r).norm.mono' _ (ae_of_all _ (clip_bound j p r))
  have W : Measurable (fun z : ℝ×ℝ => (clipping j p z:ℂ)) := by
    unfold clipping window;fun_prop
  exact W.aestronglyMeasurable.mul (raw_integrable hp r).aestronglyMeasurable

private theorem plane_value {p : ℝ} (hp : 0<p) (r : ℝ) (j : Option ℕ) :
    (match j with | none => fullValue r (4*Real.pi*p) | some k => cutoffValue k r (4*Real.pi*p))=
    (p⁻¹:ℝ) • ∫ z : ℝ×ℝ,(match j with | none => raw 0 p r z | some k => clipped k p r z) := by
  let H : ℝ→ℝ→ℂ := match j with | none => fullPair r | some k => cutoffPair k r
  let F : ℝ×ℝ→ℂ := match j with | none => raw 0 p r | some k => clipped k p r
  have G : (match j with | none => fullValue r (4*Real.pi*p) | some k => cutoffValue k r (4*Real.pi*p))=
      induced H (4*Real.pi*p) := by cases j <;> rfl
  have id (z : ℝ×ℝ) : F z=half.indicator (fun w => plane H (p^2) w.1 w.2) z := by
    cases j with
    | none => rfl
    | some k => exact clipped_eq hp k r z
  have reg : Integrable F := by cases j with
    | none => exact raw_integrable hp r
    | some k => exact clipped_integrable hp k r
  have reg' : Integrable F ((volume:Measure ℝ).prod volume) := by rwa [←Measure.volume_eq_prod]
  have row (x : ℝ) : (∫ y : ℝ,F (x,y))=∫ y,plane H (p^2) x y ∂heights := by
    simp_rw [id]
    change (∫ y,(Ioi 0).indicator (plane H (p^2) x) y)=_
    exact integral_indicator measurableSet_Ioi _
  have c : 4*Real.pi/(4*Real.pi*p)=p⁻¹ := by field_simp [Real.pi_ne_zero,hp.ne']
  have arg : (4*Real.pi*p/(4*Real.pi))^2=p^2 := by field_simp [Real.pi_ne_zero]
  rw [G,induced,c,arg]
  have E : (∫ x : ℝ,∫ y,plane H (p^2) x y ∂heights)=∫ z : ℝ×ℝ,F z := by
    simp_rw [←row]
    rw [←integral_prod F reg',←Measure.volume_eq_prod]
  rw [E] <;> cases j <;> rfl

def constant := Real.pi/4*angleConstant

theorem constant_nonnegative : 0≤constant := mul_nonneg (by positivity) angleConstant_nonnegative

/-- The SAME q^(7/8) majorant for all r, all compact cutoffs and their
physical limit. This fixed-mark estimate is used only for exchanges. -/
theorem price {u : ℝ} (hu : 0<u) (r : ℝ) (j : Option ℕ) :
    ‖match j with | none => fullValue r u | some k => cutoffValue k r u‖≤constant*u^(1-tilt) := by
  let p := u/(4*Real.pi)
  have hp : 0<p := div_pos hu (by positivity)
  have scale : 4*Real.pi*p=u := by dsimp only [p];field_simp [Real.pi_ne_zero]
  have pi : π*p=u/4 := by dsimp only [p];field_simp [Real.pi_ne_zero]
  let F : ℝ×ℝ→ℂ := fun z => match j with | none => raw 0 p r z | some k => clipped k p r z
  have reg : Integrable F := by cases j with
    | none => exact raw_integrable hp r
    | some k => exact clipped_integrable hp k r
  have dom (z : ℝ×ℝ) : ‖F z‖≤‖raw 0 p r z‖ := by cases j with
    | none => exact le_rfl
    | some k => exact clip_bound k p r z
  have h := (norm_integral_le_integral_norm F).trans (integral_mono reg.norm (raw_integrable hp r).norm dom)
  rw [raw_mass hp r,scale] at h
  have w := mul_le_mul_of_nonneg_left (angular_price hu) (mul_nonneg (sq_nonneg π) (sq_nonneg p))
  have g := mul_le_mul_of_nonneg_left (h.trans w) (inv_nonneg.mpr hp.le)
  have E := plane_value hp r j
  rw [scale] at E
  rw [E,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  change p⁻¹*‖∫ z : ℝ×ℝ,F z‖≤_
  apply g.trans_eq
  rw [constant,show 1-tilt=1+(-tilt) by ring,rpow_add hu,rpow_one]
  have red : p⁻¹*(π^2*p^2)=π*(u/4) := by rw [←pi];field_simp [hp.ne'] <;> ring
  calc
    _=(p⁻¹*(π^2*p^2))*(angleConstant*u^(-tilt)) := by ring
    _=_ := by rw [red];ring

theorem cutoff_limit {u : ℝ} (hu : 0<u) (r : ℝ) :
    Tendsto (fun j => cutoffValue j r u) atTop (𝓝 (fullValue r u)) := by
  let p := u/(4*Real.pi)
  have hp : 0<p := div_pos hu (by positivity)
  have scale : 4*Real.pi*p=u := by dsimp only [p];field_simp [Real.pi_ne_zero]
  have W (z : ℝ×ℝ) : ∀ᶠ j : ℕ in atTop,clipped j p r z=raw 0 p r z := by
    filter_upwards [window_eventually (Real.log (2*Real.pi*z.2)),
      window_eventually (Real.log (2*Real.pi*(p^2*z.2/(z.1^2+z.2^2))))] with j h1 h2
    simp only [clipped,clipping,h1,h2,mul_one,Complex.ofReal_one,one_mul]
  have T : Tendsto (fun j => ∫ z : ℝ×ℝ,clipped j p r z) atTop (𝓝 (∫ z : ℝ×ℝ,raw 0 p r z)) :=
    tendsto_integral_of_dominated_convergence (fun z => ‖raw 0 p r z‖)
      (fun j => (clipped_integrable hp j r).aestronglyMeasurable) (raw_integrable hp r).norm
      (fun j => ae_of_all _ (clip_bound j p r))
      (ae_of_all _ (fun z => tendsto_const_nhds.congr' ((W z).mono (fun _ h => h.symm))))
  have C (j : ℕ) : cutoffValue j r u=(p⁻¹:ℝ) • ∫ z : ℝ×ℝ,clipped j p r z := by
    rw [←scale];exact plane_value hp r (some j)
  have B : fullValue r u=(p⁻¹:ℝ) • ∫ z : ℝ×ℝ,raw 0 p r z := by
    rw [←scale];exact plane_value hp r none
  simp_rw [C,B]
  exact T.const_smul _

def value (j : Option ℕ) (r u : ℝ) := match j with
  | none => fullValue r u
  | some k => cutoffValue k r u

theorem measurable_value {u : ℝ} (hu : 0<u) (j : Option ℕ) :
    Measurable (fun r : ℝ => value j r u) := by
  let p := u/(4*Real.pi)
  have hp : 0<p := div_pos hu (by positivity)
  have scale : 4*Real.pi*p=u := by dsimp only [p];field_simp [Real.pi_ne_zero]
  let F := fun w : ℝ×(ℝ×ℝ) => match j with
    | none => raw 0 p w.1 w.2
    | some k => clipped k p w.1 w.2
  have rawM : Measurable (fun w : ℝ×(ℝ×ℝ) => raw 0 p w.1 w.2) := by
    let base := fun w : ℝ×(ℝ×ℝ) => plane (fullPair w.1) (p^2) w.2.1 w.2.2
    have M : Measurable base := by
      unfold base plane fullPair physical ActualUnitBandHeightSeeds20261112.modulation
        P3Period64NativeReconstructionSourceOnly.e
      fun_prop
    exact M.indicator ((measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ))).preimage (measurable_snd.comp measurable_snd))
  have fm : Measurable F := by
    cases j with
    | none => exact rawM
    | some k =>
      exact (show Measurable (fun w : ℝ×(ℝ×ℝ) => (clipping k p w.2:ℂ)) by
        unfold clipping window;fun_prop).mul rawM
  have H := (fm.stronglyMeasurable.integral_prod_right' (ν:=(volume:Measure (ℝ×ℝ)))).measurable
  have E (r : ℝ) : value j r u=(p⁻¹:ℝ) • ∫ z : ℝ×ℝ,F (r,z) := by
    rw [←scale];exact plane_value hp r j
  simp_rw [E]
  exact measurable_const.smul H

theorem value_price {u : ℝ} (hu : 0<u) (j : Option ℕ) (r : ℝ) :
    ‖value j r u‖≤constant*u^(1-tilt) := price hu r j

end ImbalancedChen.Part3.OriginalRegularCutoffPlane20261113
end

