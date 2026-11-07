import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Set
import ImbalancedChen.Part3CommonSmoothCutoff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
SOURCEONLY 2026-10-23. Complete by-source candidate, UNCOMPILED.
Actual alpha=psi=dyadicCutoff; actual Phi=Fourier dyadicCutoffSchwartz.
Zero extension is PROVED smooth via a closed support box in the positive
orthant. No smoothness, compactness, or Fourier decay is assumed.
Coordinates and norm are the native EuclideanSpace Real (Fin 4).
-/

namespace ImbalancedChen.Part3.ActualNormalizedSmoothF
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter CommonSmoothCutoff
open scoped Topology ContDiff FourierTransform SchwartzMap

abbrev E4 := EuclideanSpace ℝ (Fin 4)

def positive (x : E4) : Prop :=
  0 < x 0 ∧ 0 < x 1 ∧ 0 < x 2 ∧ 0 < x 3

def rawF (rho sigma : ℝ) (x : E4) : ℂ :=
  ((dyadicCutoff (x 1) * dyadicCutoff (x 2) * dyadicCutoff (x 3) *
      Real.sqrt (x 3) *
      dyadicCutoff (Real.sqrt (x 1 * x 2 / x 3) / x 0) : ℝ) : ℂ) *
    ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * x 0 * Real.sqrt (x 1 * x 3 / x 2))

def normalizedF (rho sigma : ℝ) (x : E4) : ℂ :=
  if positive x then rawF rho sigma x else 0

def boxLo (i : Fin 4) : ℝ := if i = 0 then Real.sqrt 10 / 25 else 1 / 2
def boxHi (i : Fin 4) : ℝ := if i = 0 then 5 * Real.sqrt 2 else 5 / 2

def fixedBox : Set E4 := {x | ∀ i, x i ∈ Icc (boxLo i) (boxHi i)}

/-- Same tight bump fact as the independently supplied physical-c draft;
reproved locally so this draft has only actual imports. -/
theorem cutoff_nonzero_bounds {u : ℝ} (hu : dyadicCutoff u ≠ 0) :
    u ∈ Icc (1 / 2 : ℝ) (5 / 2) := by
  have hm : u ∈ tsupport (dyadicBump : ℝ → ℝ) := subset_closure hu
  rw [dyadicBump.tsupport_eq] at hm
  change |u - 3 / 2| ≤ 1 at hm
  obtain ⟨hl, hh⟩ := abs_le.mp hm
  constructor <;> linarith

/-- The actual support calculation; no rough endpoint replacement. -/
theorem t_bounds {t v w z : ℝ} (ht : 0 < t)
    (hv : v ∈ Icc (1 / 2 : ℝ) (5 / 2))
    (hw : w ∈ Icc (1 / 2 : ℝ) (5 / 2))
    (hz : z ∈ Icc (1 / 2 : ℝ) (5 / 2))
    (hu : Real.sqrt (v * w / z) / t ∈ Icc (1 / 2 : ℝ) (5 / 2)) :
    t ∈ Icc (Real.sqrt 10 / 25) (5 * Real.sqrt 2) := by
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hw0 : 0 ≤ w := by linarith [hw.1]
  have hz0 : 0 < z := by linarith [hz.1]
  have hpLo : (1 : ℝ) / 4 ≤ v * w := by
    have h := mul_le_mul hv.1 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0
    nlinarith
  have hpHi : v * w ≤ (25 : ℝ) / 4 := by
    have h := mul_le_mul hv.2 hw.2 hw0 (by norm_num : (0 : ℝ) ≤ 5 / 2)
    nlinarith
  have hrLo : (1 : ℝ) / 10 ≤ v * w / z := by
    apply (le_div_iff₀ hz0).2
    nlinarith [hz.2]
  have hrHi : v * w / z ≤ (25 : ℝ) / 2 := by
    apply (div_le_iff₀ hz0).2
    nlinarith [hz.1]
  have hr0 : 0 ≤ v * w / z := le_trans (by norm_num) hrLo
  have hyLo : Real.sqrt 10 / 10 ≤ Real.sqrt (v * w / z) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt hr0]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  have hyHi : Real.sqrt (v * w / z) ≤ 5 * Real.sqrt 2 / 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt hr0]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have huLo := (le_div_iff₀ ht).1 hu.1
  have huHi := (div_le_iff₀ ht).1 hu.2
  constructor <;> linarith

/-- Nonzero support implies all four explicit closed coordinate bounds. -/
theorem support_subset_fixedBox (rho sigma : ℝ) :
    Function.support (normalizedF rho sigma) ⊆ fixedBox := by
  intro x hx
  have hn : normalizedF rho sigma x ≠ 0 := hx
  by_cases hp : positive x
  · have hraw : rawF rho sigma x ≠ 0 := by
      simpa only [normalizedF, if_pos hp] using hn
    have hv : dyadicCutoff (x 1) ≠ 0 := by
      intro h; apply hraw; simp [rawF, h]
    have hw : dyadicCutoff (x 2) ≠ 0 := by
      intro h; apply hraw; simp [rawF, h]
    have hz : dyadicCutoff (x 3) ≠ 0 := by
      intro h; apply hraw; simp [rawF, h]
    have hu : dyadicCutoff (Real.sqrt (x 1 * x 2 / x 3) / x 0) ≠ 0 := by
      intro h; apply hraw; simp [rawF, h]
    have hvb := cutoff_nonzero_bounds hv
    have hwb := cutoff_nonzero_bounds hw
    have hzb := cutoff_nonzero_bounds hz
    have htb := t_bounds hp.1 hvb hwb hzb (cutoff_nonzero_bounds hu)
    intro i
    fin_cases i
    · simpa [boxLo, boxHi] using htb
    · simpa [boxLo, boxHi] using hvb
    · simpa [boxLo, boxHi] using hwb
    · simpa [boxLo, boxHi] using hzb
  · exact (hn (by simp only [normalizedF, if_neg hp])).elim

theorem fixedBox_isClosed : IsClosed fixedBox := by
  have h : IsClosed (⋂ i : Fin 4,
      (fun x : E4 => x i) ⁻¹' Icc (boxLo i) (boxHi i)) :=
    isClosed_iInter (fun i => isClosed_Icc.preimage (EuclideanSpace.proj i).continuous)
  convert h using 1
  ext x
  simp only [fixedBox, mem_ofPred_eq, mem_iInter, mem_preimage]

theorem fixedBox_isCompact : IsCompact fixedBox := by
  let K : Set (Fin 4 → ℝ) := Set.pi Set.univ (fun i => Icc (boxLo i) (boxHi i))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hcont : Continuous (fun x : Fin 4 → ℝ => (WithLp.toLp 2 x : E4)) := by fun_prop
  have he : (fun x : Fin 4 → ℝ => (WithLp.toLp 2 x : E4)) '' K = fixedBox := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      intro i
      exact hy i (mem_univ i)
    · intro hx
      refine ⟨fun i => x i, ?_, ?_⟩
      · intro i hi
        exact hx i
      · ext i
        rfl
  rw [← he]
  exact hK.image hcont

theorem tsupport_subset_fixedBox (rho sigma : ℝ) :
    tsupport (normalizedF rho sigma) ⊆ fixedBox := by
  exact closure_minimal (support_subset_fixedBox rho sigma) fixedBox_isClosed

theorem normalizedF_hasCompactSupport (rho sigma : ℝ) :
    HasCompactSupport (normalizedF rho sigma) := by
  exact fixedBox_isCompact.of_isClosed_subset isClosed_closure
    (tsupport_subset_fixedBox rho sigma)

theorem fixedBox_positive {x : E4} (hx : x ∈ fixedBox) : positive x := by
  have h0 : Real.sqrt 10 / 25 ≤ x 0 := by
    simpa [boxLo] using (hx 0).1
  have h1 : (1 : ℝ) / 2 ≤ x 1 := by simpa [boxLo] using (hx 1).1
  have h2 : (1 : ℝ) / 2 ≤ x 2 := by simpa [boxLo] using (hx 2).1
  have h3 : (1 : ℝ) / 2 ≤ x 3 := by simpa [boxLo] using (hx 3).1
  have hroot : 0 < Real.sqrt (10 : ℝ) / 25 := by positivity
  exact ⟨lt_of_lt_of_le hroot h0, by linarith, by linarith, by linarith⟩

theorem positive_isOpen : IsOpen {x : E4 | positive x} := by
  have hi (i : Fin 4) : IsOpen {x : E4 | 0 < x i} :=
    isOpen_lt continuous_const (EuclideanSpace.proj i).continuous
  exact (hi 0).inter ((hi 1).inter ((hi 2).inter (hi 3)))

/-- Smoothness of the LITERAL formula on the positive orthant. -/
theorem rawF_contDiffAt (rho sigma : ℝ) {x : E4} (hx : positive x) :
    ContDiffAt ℝ ∞ (rawF rho sigma) x := by
  obtain ⟨ht, hv, hw, hz⟩ := hx
  have hi (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : E4 => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : E4 →L[ℝ] ℝ).contDiff.contDiffAt
  have hroot1 : ContDiffAt ℝ ∞
      (fun y : E4 => Real.sqrt (y 1 * y 2 / y 3)) x :=
    (((hi 1).mul (hi 2)).div (hi 3) hz.ne').sqrt
      (div_pos (mul_pos hv hw) hz).ne'
  have hroot2 : ContDiffAt ℝ ∞
      (fun y : E4 => Real.sqrt (y 1 * y 3 / y 2)) x :=
    (((hi 1).mul (hi 3)).div (hi 2) hw.ne').sqrt
      (div_pos (mul_pos hv hz) hw).ne'
  have ha (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : E4 => dyadicCutoff (y i)) x :=
    dyadicCutoff_contDiff.contDiffAt.comp x (hi i)
  have hpsi : ContDiffAt ℝ ∞
      (fun y : E4 => dyadicCutoff (Real.sqrt (y 1 * y 2 / y 3) / y 0)) x :=
    dyadicCutoff_contDiff.contDiffAt.comp x (hroot1.div (hi 0) ht.ne')
  have hreal := ((((ha 1).mul (ha 2)).mul (ha 3)).mul ((hi 3).sqrt hz.ne')).mul hpsi
  have hcomplex := Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  have harg : ContDiffAt ℝ ∞
      (fun y : E4 => sigma * rho * y 0 * Real.sqrt (y 1 * y 3 / y 2)) x :=
    (contDiffAt_const.mul (hi 0)).mul hroot2
  have hphi := ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)).smooth ⊤).contDiffAt.comp x harg
  exact hcomplex.mul hphi

/-- On an open positive neighborhood the zero extension agrees with rawF. -/
theorem normalizedF_contDiffAt_positive (rho sigma : ℝ) {x : E4}
    (hx : positive x) : ContDiffAt ℝ ∞ (normalizedF rho sigma) x := by
  apply (rawF_contDiffAt rho sigma hx).congr_of_eventuallyEq
  filter_upwards [positive_isOpen.mem_nhds hx] with y hy
  exact if_pos hy

/-- Actual zero extension: support lies strictly inside the smooth domain;
outside topological support it is locally the constant zero function. -/
theorem normalizedF_contDiff (rho sigma : ℝ) :
    ContDiff ℝ ∞ (normalizedF rho sigma) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ tsupport (normalizedF rho sigma)
  · exact normalizedF_contDiffAt_positive rho sigma
      (fixedBox_positive (tsupport_subset_fixedBox rho sigma hx))
  · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E4 => (0 : ℂ)) x).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hx)

/-- Actual Schwartz object ready for the native E4 Fourier sampling API. -/
def normalizedFSchwartz (rho sigma : ℝ) : 𝓢(E4, ℂ) :=
  (normalizedF_hasCompactSupport rho sigma).toSchwartzMap
    (normalizedF_contDiff rho sigma)

@[simp] theorem normalizedFSchwartz_apply (rho sigma : ℝ) (x : E4) :
    normalizedFSchwartz rho sigma x = normalizedF rho sigma x := rfl

/-- The fixed box is well inside the common worker's period64 cell. -/
theorem fixedBox_subset_inside64 :
    fixedBox ⊆ {x : E4 | ∀ i, x i ∈ Ioo (-32 : ℝ) 32} := by
  intro x hx i
  have hp := fixedBox_positive hx
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).1
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hi := hx i
  fin_cases i <;> simp only [boxLo, boxHi] at hi
  · change x 0 ∈ Ioo (-32 : ℝ) 32
    norm_num at hi
    exact ⟨by linarith [hp.1], by nlinarith [hi.2]⟩
  · change x 1 ∈ Ioo (-32 : ℝ) 32
    norm_num at hi
    exact ⟨by linarith [hp.2.1], by linarith [hi.2]⟩
  · change x 2 ∈ Ioo (-32 : ℝ) 32
    norm_num at hi
    change (1 / 2 : ℝ) ≤ x 2 ∧ x 2 ≤ 5 / 2 at hi
    exact ⟨by linarith [hp.2.2.1], by linarith [hi.2]⟩
  · change x 3 ∈ Ioo (-32 : ℝ) 32
    norm_num at hi
    change (1 / 2 : ℝ) ≤ x 3 ∧ x 3 ≤ 5 / 2 at hi
    exact ⟨by linarith [hp.2.2.2], by linarith [hi.2]⟩

theorem normalizedF_tsupport_inside64 (rho sigma : ℝ) :
    tsupport (normalizedF rho sigma) ⊆
      {x : E4 | ∀ i, x i ∈ Ioo (-32 : ℝ) 32} := by
  exact (tsupport_subset_fixedBox rho sigma).trans fixedBox_subset_inside64

theorem normalizedF_support_inside64 (rho sigma : ℝ) :
    Function.support (normalizedF rho sigma) ⊆
      {x : E4 | ∀ i, x i ∈ Ioo (-32 : ℝ) 32} := by
  intro x hx
  exact normalizedF_tsupport_inside64 rho sigma (subset_closure hx)

end
end ImbalancedChen.Part3.ActualNormalizedSmoothF



/-!
UNIFORM-RHO SUPPLIER, 2026-10-23, SOURCEONLY / UNCOMPILED.
This standalone text contains the exact fc9e3c smooth/compact V2 parent above.
The following new section derives every derivative constant from the actual
fixed geometry on its proved compact box and from actual Schwartz seminorms.
No derivative-mass or Fourier-decay estimate is a premise of the final theorem.
-/

namespace ImbalancedChen.Part3.ActualNormalizedSmoothF
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory CommonSmoothCutoff
open scoped BigOperators Topology ContDiff FourierTransform SchwartzMap

/-- The fixed actual amplitude without its varying Schwartz argument. -/
def fixedAmplitude (x : E4) : ℂ :=
  ((dyadicCutoff (x 1) * dyadicCutoff (x 2) * dyadicCutoff (x 3) *
    Real.sqrt (x 3) *
    dyadicCutoff (Real.sqrt (x 1 * x 2 / x 3) / x 0) : ℝ) : ℂ)

/-- The fixed actual geometric argument, on the positive neighborhood of B. -/
def fixedGeometry (x : E4) : ℝ := x 0 * Real.sqrt (x 1 * x 3 / x 2)

theorem fixedAmplitude_contDiffAt {x : E4} (hx : positive x) :
    ContDiffAt ℝ ∞ fixedAmplitude x := by
  obtain ⟨ht, hv, hw, hz⟩ := hx
  have hi (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : E4 => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : E4 →L[ℝ] ℝ).contDiff.contDiffAt
  have hroot : ContDiffAt ℝ ∞
      (fun y : E4 => Real.sqrt (y 1 * y 2 / y 3)) x :=
    (((hi 1).mul (hi 2)).div (hi 3) hz.ne').sqrt
      (div_pos (mul_pos hv hw) hz).ne'
  have ha (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : E4 => dyadicCutoff (y i)) x :=
    dyadicCutoff_contDiff.contDiffAt.comp x (hi i)
  have hpsi := dyadicCutoff_contDiff.contDiffAt.comp x
    (hroot.div (hi 0) ht.ne')
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (((((ha 1).mul (ha 2)).mul (ha 3)).mul ((hi 3).sqrt hz.ne')).mul hpsi)

theorem fixedGeometry_contDiffAt {x : E4} (hx : positive x) :
    ContDiffAt ℝ ∞ fixedGeometry x := by
  obtain ⟨ht, hv, hw, hz⟩ := hx
  have hi (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : E4 => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : E4 →L[ℝ] ℝ).contDiff.contDiffAt
  exact (hi 0).mul ((((hi 1).mul (hi 3)).div (hi 2) hw.ne').sqrt
    (div_pos (mul_pos hv hz) hw).ne')

/-- A compactness-derived finite derivative bound, not an assumed envelope. -/
theorem fixedBox_finite_derivative_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E4 → V) (hf : ∀ x ∈ fixedBox, ContDiffAt ℝ ∞ f x) (r : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ r, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb (i : ℕ) : ∃ C : ℝ, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
    apply fixedBox_isCompact.exists_bound_of_continuousOn
    intro x hx
    exact ((hf x hx).continuousAt_iteratedFDeriv
      (show (i : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  choose C hC using hb
  let D : ℝ := 1 + ∑ i ∈ Finset.range (r + 1), |C i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (r + 1), |C i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro i hi x hx
  calc
    ‖iteratedFDeriv ℝ i f x‖ ≤ C i := hC i x hx
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ k ∈ Finset.range (r + 1), |C k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (C k))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    _ ≤ D := by dsimp [D]; linarith

/-- The actual Phi has a uniform finite set of derivative bounds on all R. -/
theorem actualPhi_finite_derivative_bound (r : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ r, ∀ y : ℝ,
      ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ ≤ C := by
  let P (i : ℕ) : ℝ := SchwartzMap.seminorm ℝ 0 i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)))
  let C : ℝ := 1 + ∑ i ∈ Finset.range (r + 1), |P i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (r + 1), |P i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro i hi y
  calc
    ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ ≤ P i := by
      simpa only [pow_zero, one_mul] using
        (SchwartzMap.le_seminorm ℝ 0 i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) y)
    _ ≤ |P i| := le_abs_self _
    _ ≤ ∑ k ∈ Finset.range (r + 1), |P k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (P k))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    _ ≤ C := by dsimp [C]; linarith

/-- Native finite-order composition bound with all rho dependence exposed.
The geometry/Phi constants in this local helper are derived above and are
fully discharged in the final actual theorem. -/
theorem actual_composition_derivative_bound
    (r : ℕ) (C D : ℝ) (hC1 : 1 ≤ C) (hD1 : 1 ≤ D)
    (hPhi : ∀ i ≤ r, ∀ y : ℝ,
      ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ ≤ C)
    (hGeom : ∀ i ≤ r, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i fixedGeometry x‖ ≤ D)
    {rho sigma : ℝ} (hrho : 0 ≤ rho) (hsigma : |sigma| ≤ 1)
    {j : ℕ} (hj : j ≤ r) {x : E4} (hx : x ∈ fixedBox) :
    ‖iteratedFDerivWithin ℝ j
        (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y))
        {y : E4 | positive y} x‖ ≤
      ((j.factorial : ℝ) * C * D ^ j) * (1 + rho) ^ r := by
  let O : Set E4 := {y | positive y}
  have hxO : x ∈ O := fixedBox_positive hx
  have hO : IsOpen O := positive_isOpen
  have hG : ContDiffOn ℝ ∞ fixedGeometry O :=
    fun y hy => (fixedGeometry_contDiffAt hy).contDiffWithinAt
  have hf : ContDiffOn ℝ ∞ (fun y => sigma * rho * fixedGeometry y) O :=
    contDiffOn_const.mul hG
  have hP1 : 1 ≤ 1 + rho := by linarith
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hPD1 : 1 ≤ (1 + rho) * D := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (1 + rho) * D := mul_le_mul hP1 hD1 zero_le_one (by linarith)
  have hnorm (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (fun y => sigma * rho * fixedGeometry y) O x‖ ≤
        ((1 + rho) * D) ^ i := by
    have hscale :
        iteratedFDerivWithin ℝ i (fun y => sigma * rho * fixedGeometry y) O x =
          (sigma * rho) • iteratedFDerivWithin ℝ i fixedGeometry O x := by
      have hfun : (fun y : E4 => sigma * rho * fixedGeometry y) =
          (sigma * rho) • fixedGeometry := by
        funext y
        rfl
      rw [hfun]
      exact (iteratedFDerivWithin_const_smul_apply (a := sigma * rho)
          ((fixedGeometry_contDiffAt hxO).of_le
            (show (i : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
          hO.uniqueDiffOn hxO)
    have hGb : ‖iteratedFDerivWithin ℝ i fixedGeometry O x‖ ≤ D := by
      rw [iteratedFDerivWithin_of_isOpen i hO hxO]
      exact hGeom i (le_trans hij hj) x hx
    have hs : |sigma| * rho ≤ rho := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsigma hrho
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hrho]
    calc
      |sigma| * rho * ‖iteratedFDerivWithin ℝ i fixedGeometry O x‖ ≤ rho * D :=
        mul_le_mul hs hGb (norm_nonneg _) hrho
      _ ≤ (1 + rho) * D := mul_le_mul_of_nonneg_right (by linarith) hD0
      _ = ((1 + rho) * D) ^ 1 := by rw [pow_one]
      _ ≤ ((1 + rho) * D) ^ i := pow_le_pow_right₀ hPD1 hi
  have hbound := norm_iteratedFDerivWithin_comp_le
    (g := ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
    (f := fun y : E4 => sigma * rho * fixedGeometry y)
    (s := O) (t := Set.univ) (n := j)
    ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)).smooth ⊤).contDiffOn hf
    (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    uniqueDiffOn_univ hO.uniqueDiffOn (fun _ _ => mem_univ _) hxO
    (C := C) (D := (1 + rho) * D)
    (fun i hi => by
      rw [iteratedFDerivWithin_univ]
      exact hPhi i (le_trans hi hj) _) hnorm
  calc
    ‖iteratedFDerivWithin ℝ j
        (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O x‖
      ≤ (j.factorial : ℝ) * C * ((1 + rho) * D) ^ j := by
        simpa only [Function.comp_def] using hbound
    _ = ((j.factorial : ℝ) * C * D ^ j) * (1 + rho) ^ j := by
      rw [mul_pow]
      ring
    _ ≤ ((j.factorial : ℝ) * C * D ^ j) * (1 + rho) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP1 hj) (by positivity)

/-- Explicit finite cost from the native product derivative bound. -/
def derivativeCost (A C D : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * A * ((j - i).factorial : ℝ) * C * D ^ (j - i)

theorem derivativeCost_nonneg {A C D : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (j : ℕ) :
    0 ≤ derivativeCost A C D j := by
  unfold derivativeCost
  exact Finset.sum_nonneg (fun i hi => by positivity)

/-- Actual normalizedF, retaining its exact zero extension and coefficient. -/
theorem actual_normalizedF_derivative_bound
    (r : ℕ) (A C D : ℝ) (hA1 : 1 ≤ A) (hC1 : 1 ≤ C) (hD1 : 1 ≤ D)
    (hAmp : ∀ i ≤ r, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i fixedAmplitude x‖ ≤ A)
    (hPhi : ∀ i ≤ r, ∀ y : ℝ,
      ‖iteratedFDeriv ℝ i ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y‖ ≤ C)
    (hGeom : ∀ i ≤ r, ∀ x ∈ fixedBox,
      ‖iteratedFDeriv ℝ i fixedGeometry x‖ ≤ D)
    {rho sigma : ℝ} (hrho : 0 ≤ rho) (hsigma : |sigma| ≤ 1)
    {j : ℕ} (hj : j ≤ r) {x : E4} (hx : x ∈ fixedBox) :
    ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖ ≤
      derivativeCost A C D j * (1 + rho) ^ r := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  let O : Set E4 := {y | positive y}
  have hxO : x ∈ O := fixedBox_positive hx
  have hO : IsOpen O := positive_isOpen
  have hA : ContDiffOn ℝ ∞ fixedAmplitude O :=
    fun y hy => (fixedAmplitude_contDiffAt hy).contDiffWithinAt
  have hG : ContDiffOn ℝ ∞ fixedGeometry O :=
    fun y hy => (fixedGeometry_contDiffAt hy).contDiffWithinAt
  have hcomp : ContDiffOn ℝ ∞
      (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O :=
    ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ)).smooth ⊤).comp_contDiffOn (contDiffOn_const.mul hG)
  have heq : EqOn (normalizedF rho sigma)
      (fun y => fixedAmplitude y *
        ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O := by
    intro y hy
    change positive y at hy
    simp only [normalizedF, if_pos hy, rawF, fixedAmplitude, fixedGeometry, mul_assoc]
  rw [← iteratedFDerivWithin_of_isOpen j hO hxO,
    iteratedFDerivWithin_congr heq hxO j]
  calc
    ‖iteratedFDerivWithin ℝ j
        (fun y => fixedAmplitude y *
          ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i fixedAmplitude O x‖ *
          ‖iteratedFDerivWithin ℝ (j - i)
            (fun y => ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ, ℂ))) (sigma * rho * fixedGeometry y)) O x‖ :=
      norm_iteratedFDerivWithin_mul_le hA hcomp hO.uniqueDiffOn hxO
        (show (j : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℝ) * A * ((j - i).factorial : ℝ) * C * D ^ (j - i)) *
          (1 + rho) ^ r := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hj
      have hAb : ‖iteratedFDerivWithin ℝ i fixedAmplitude O x‖ ≤ A := by
        rw [iteratedFDerivWithin_of_isOpen i hO hxO]
        exact hAmp i hir x hx
      have hCb := actual_composition_derivative_bound r C D hC1 hD1 hPhi hGeom
        hrho hsigma (le_trans (Nat.sub_le j i) hj) hx
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left hAb (Nat.cast_nonneg (j.choose i))) hCb
        (norm_nonneg _) (by positivity : 0 ≤ (j.choose i : ℝ) * A)
      exact hmul.trans_eq (by ring)
    _ = derivativeCost A C D j * (1 + rho) ^ r := by
      rw [derivativeCost, Finset.sum_mul]

/-- Derivatives vanish off the TRUE fixed box; no integration-domain shortcut. -/
theorem actual_derivative_zero_off_box (rho sigma : ℝ) (j : ℕ)
    {x : E4} (hx : x ∉ fixedBox) :
    iteratedFDeriv ℝ j (normalizedF rho sigma) x = 0 := by
  by_contra hn
  exact hx (tsupport_subset_fixedBox rho sigma
    (support_iteratedFDeriv_subset (𝕜 := ℝ) j hn))

/-- Integral consequence of a proved pointwise bound on the true box. -/
theorem actual_derivative_integral_bound (rho sigma : ℝ) (j : ℕ) (K : ℝ)
    (hK : ∀ x ∈ fixedBox, ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖ ≤ K) :
    (∫ x : E4, ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖) ≤
      K * volume.real fixedBox := by
  have hzero (x : E4) (hx : x ∉ fixedBox) :
      ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖ = 0 := by
    rw [actual_derivative_zero_off_box rho sigma j hx, norm_zero]
  have hset := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzero
  rw [← hset]
  calc
    (∫ x in fixedBox, ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖)
      ≤ ‖∫ x in fixedBox, ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖‖ :=
      le_abs_self _
    _ ≤ K * volume.real fixedBox :=
      norm_setIntegral_le_of_norm_le_const fixedBox_isCompact.measure_lt_top
        (fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hK x hx)

/-- The actual uniform-rho derivative-mass supplier for EVERY finite r.
All constants precede rho and sigma; the only variable assumptions are
rho>=0 and |sigma|<=1, stronger than the requested two-sign conclusion. -/
theorem actual_uniform_derivative_mass (r : ℕ) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
      (∑ j ∈ Finset.range (r + 1),
        ∫ x : E4, ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖) ≤
          Cr * (1 + rho) ^ r := by
  obtain ⟨A, hA1, hAmp⟩ := fixedBox_finite_derivative_bound fixedAmplitude
    (fun x hx => fixedAmplitude_contDiffAt (fixedBox_positive hx)) r
  obtain ⟨D, hD1, hGeom⟩ := fixedBox_finite_derivative_bound fixedGeometry
    (fun x hx => fixedGeometry_contDiffAt (fixedBox_positive hx)) r
  obtain ⟨C, hC1, hPhi⟩ := actualPhi_finite_derivative_bound r
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  let S : ℝ := ∑ j ∈ Finset.range (r + 1), derivativeCost A C D j
  have hS : 0 ≤ S := Finset.sum_nonneg
    (fun j hj => derivativeCost_nonneg hA0 hC0 hD0 j)
  have hvol : 0 ≤ volume.real fixedBox := ENNReal.toReal_nonneg
  let Cr : ℝ := 1 + S * volume.real fixedBox
  refine ⟨Cr, by dsimp [Cr]; positivity, ?_⟩
  intro rho hrho sigma hsigma
  have hP : 0 ≤ (1 + rho) ^ r := by positivity
  calc
    (∑ j ∈ Finset.range (r + 1),
        ∫ x : E4, ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖)
      ≤ ∑ j ∈ Finset.range (r + 1),
          (derivativeCost A C D j * (1 + rho) ^ r) * volume.real fixedBox := by
        apply Finset.sum_le_sum
        intro j hj
        apply actual_derivative_integral_bound
        intro x hx
        exact actual_normalizedF_derivative_bound r A C D hA1 hC1 hD1 hAmp hPhi hGeom
          hrho hsigma (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hx
    _ = (S * volume.real fixedBox) * (1 + rho) ^ r := by
      dsimp [S]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ Cr * (1 + rho) ^ r :=
      mul_le_mul_of_nonneg_right (by dsimp [Cr]; linarith) hP

/-- The requested positive/negative phase signs, including rho=0. -/
theorem actual_uniform_derivative_mass_signs (r : ℕ) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ,
      (sigma = 1 ∨ sigma = -1) →
      (∑ j ∈ Finset.range (r + 1),
        ∫ x : E4, ‖iteratedFDeriv ℝ j (normalizedF rho sigma) x‖) ≤
          Cr * (1 + rho) ^ r := by
  obtain ⟨C, hC, hb⟩ := actual_uniform_derivative_mass r
  refine ⟨C, hC, fun rho hrho sigma hsigma => hb rho hrho sigma ?_⟩
  rcases hsigma with rfl | rfl <;> norm_num

end
end ImbalancedChen.Part3.ActualNormalizedSmoothF
