import ImbalancedChen.P3LogProductTransitionJets
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Compact scalar extensions for one log numerator and one ORIGINAL GROUP
inverse log per HB group. No inverse log is assigned to an individual unit.
The extensions agree with the physical factors on their explicitly proved
core domains. The pole at zero is removed by an actual zero neighbourhood,
not by relying on totalized division or assuming a derivative estimate.
-/
namespace ImbalancedChen.P3HBLogScalarProfiles
noncomputable section
open scoped Classical Topology
open Filter Set

/-- Equals y on [0,2], with fixed compact support [-1,3]. -/
def logProfile (y : ℝ) : ℝ :=
  Real.smoothTransition (y+1)*(1-Real.smoothTransition (y-2))*y

/-- Equals 1/y on [a,2]. For a>0 it is zero near the apparent pole. -/
def inverseLogProfile (a y : ℝ) : ℝ :=
  (Real.smoothTransition (2*y/a-1)*(1-Real.smoothTransition (y-2)))/y

theorem logProfile_core {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 2) : logProfile y=y := by
  rw [logProfile,Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem logProfile_zero : logProfile 0=0 := by simp [logProfile]

theorem inverseLogProfile_core {a y : ℝ} (ha : 0 < a)
    (hay : a ≤ y) (hy2 : y ≤ 2) : inverseLogProfile a y=1/y := by
  have h : 1 ≤ 2*y/a-1 := by
    have hh : 2 ≤ 2*y/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  rw [inverseLogProfile,Real.smoothTransition.one_of_one_le h,
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

theorem inverseLogProfile_zero_left {a y : ℝ} (ha : 0 < a)
    (hy : y ≤ a/2) : inverseLogProfile a y=0 := by
  have h : 2*y/a-1 ≤ 0 := by
    have hh : 2*y/a ≤ 1 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  rw [inverseLogProfile,Real.smoothTransition.zero_of_nonpos h,zero_mul,zero_div]

theorem logProfile_zero_outside {y : ℝ} (hy : y < -1 ∨ 3 < y) : logProfile y=0 := by
  rcases hy with hy | hy
  · rw [logProfile,Real.smoothTransition.zero_of_nonpos (by linarith),zero_mul,zero_mul]
  · rw [logProfile,Real.smoothTransition.one_of_one_le (by linarith),sub_self,mul_zero,zero_mul]

theorem inverseLogProfile_zero_outside {a y : ℝ} (ha : 0 < a)
    (hy : y < -1 ∨ 3 < y) : inverseLogProfile a y=0 := by
  rcases hy with hy | hy
  · exact inverseLogProfile_zero_left ha (by linarith)
  · rw [inverseLogProfile,Real.smoothTransition.one_of_one_le (by linarith),
      sub_self,mul_zero,zero_div]

theorem logProfile_contDiff : ContDiff ℝ ∞ logProfile := by
  exact ((Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (contDiff_id.sub contDiff_const)))).mul contDiff_id

/-- The sole apparent singularity is treated by a genuine zero germ. -/
theorem inverseLogProfile_contDiff {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (inverseLogProfile a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y=0
  · subst y
    have he : inverseLogProfile a =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (half_pos ha)] with z hz
      exact inverseLogProfile_zero_left ha hz.le
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) 0).
      congr_of_eventuallyEq he
  · have hf : ContDiff ℝ ∞ (fun y : ℝ =>
        Real.smoothTransition (2*y/a-1)*(1-Real.smoothTransition (y-2))) := by
      apply (Real.smoothTransition.contDiff.comp _).mul
        (contDiff_const.sub (Real.smoothTransition.contDiff.comp
          (contDiff_id.sub contDiff_const)))
      exact ((contDiff_const.mul contDiff_id).div_const a).sub contDiff_const
    exact hf.contDiffAt.div contDiffAt_id hy

/-- Basic compactness and zero-germ calculus supply ALL fixed orders.
The global bound is not taken as a premise for the target HB factor. -/
theorem exists_compact_scalar_derivative_bound (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hz : ∀ y, y < -1 ∨ 3 < y → f y=0) (n : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ y,|iteratedDeriv n f y| ≤ C := by
  have hc : Continuous (iteratedDeriv n f) :=
    ContDiff.continuous_iteratedDeriv' n (hf.of_le (by simp))
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 3)).
    exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 1,le_max_right _ _,?_⟩
  intro y
  by_cases hlo : y < -1
  · have he : f =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds hlo] with z hz'
      exact hz z (Or.inl hz')
    have hd : iteratedDeriv n f y=0 := by
      simpa only [iteratedDeriv_fun_const_zero] using he.iteratedDeriv_eq n
    rw [hd,abs_zero]
    exact zero_le_one.trans (le_max_right _ _)
  by_cases hhi : 3 < y
  · have he : f =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [Ioi_mem_nhds hhi] with z hz'
      exact hz z (Or.inr hz')
    have hd : iteratedDeriv n f y=0 := by
      simpa only [iteratedDeriv_fun_const_zero] using he.iteratedDeriv_eq n
    rw [hd,abs_zero]
    exact zero_le_one.trans (le_max_right _ _)
  exact (by simpa only [Real.norm_eq_abs] using
    hB y ⟨le_of_not_gt hlo,le_of_not_gt hhi⟩).trans (le_max_left _ _)

inductive Kind where
  | transition | product | logSlot | inverseGroup
  deriving DecidableEq, Fintype

def scalar (a : ℝ) : Kind → ℝ → ℝ
  | .transition => Real.smoothTransition
  | .product => P3LogProductTransitionJets.logStep
  | .logSlot => logProfile
  | .inverseGroup => inverseLogProfile a

theorem scalar_contDiff {a : ℝ} (ha : 0 < a) (k : Kind) :
    ContDiff ℝ ∞ (scalar a k) := by
  cases k
  · exact Real.smoothTransition.contDiff
  · exact P3LogProductTransitionJets.logStep_contDiff
  · exact logProfile_contDiff
  · exact inverseLogProfile_contDiff ha

/-- a is a fixed exponent floor. The bound precedes every later argument,
physical scale, numerator choice, group assignment and smoothing stage. -/
theorem exists_scalar_derivative_bound (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ k : Kind,∀ y,|iteratedDeriv n (scalar a k) y| ≤ C := by
  have h : ∀ k : Kind,∃ C : ℝ,1 ≤ C ∧ ∀ y,|iteratedDeriv n (scalar a k) y| ≤ C := by
    intro k
    cases k
    · exact P4B.exists_smoothTransition_global_derivative_bound n
    · exact P3LogProductTransitionJets.exists_logStep_derivative_bound n
    · exact exists_compact_scalar_derivative_bound _ logProfile_contDiff
        (fun y hy => logProfile_zero_outside hy) n
    · exact exists_compact_scalar_derivative_bound _ (inverseLogProfile_contDiff ha)
        (fun y hy => inverseLogProfile_zero_outside ha hy) n
  choose c hc hb using h
  let C := 1+∑ k : Kind,c k
  have hc0 (k : Kind) : 0 ≤ c k := zero_le_one.trans (hc k)
  refine ⟨C,?_,?_⟩
  · have hh := Finset.sum_nonneg (s:=Finset.univ) (fun k _ => hc0 k)
    dsimp [C]
    linarith
  intro k y
  exact (hb k y).trans ((Finset.single_le_sum (fun k _ => hc0 k)
    (Finset.mem_univ k)).trans (by dsimp [C]; linarith))

end
end ImbalancedChen.P3HBLogScalarProfiles
