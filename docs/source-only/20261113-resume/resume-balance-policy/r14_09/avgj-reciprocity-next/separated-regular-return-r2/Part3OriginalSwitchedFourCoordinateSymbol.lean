import ImbalancedChen.Part3OriginalSwitchedPhysicalWindows
import ImbalancedChen.Part3NativePeriod64Reconstruction

/-! A single compact symbol for the second application of Kuznetsov.
Scaling the return level by 4C places it on the original χ plateau. -/
namespace ImbalancedChen.Part3.OriginalSwitchedFourCoordinateSymbol20261113
noncomputable section
open Set Filter Complex
open scoped Topology ContDiff BigOperators
open P3NativePeriod64SamplingSourceOnly (E4 D4 inside64)
open P3Period64NativeReconstructionSourceOnly (chi chi_contDiff chi_tsupport_subset)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_contDiff)
open ActualNormalizedSmoothF (cutoff_nonzero_bounds)
open P3ActualSampledLatticeSourceOnly (coeff testWeight weightedL1 native_weighted_l1)

/-- The coordinate ordering is (Yx,m/M,n/M,d/(4C)). -/
def symbol (x : E4) : ℂ :=
  ((dyadicCutoff (x 0)*dyadicCutoff (x 1)*dyadicCutoff (x 2)*chi (x 3)*
    dyadicCutoff (Real.sqrt (x 1*x 2)/(x 3*x 0)):ℝ):ℂ)

private def box : Set E4 := {x | ∀ i,x i∈Icc (1/16:ℝ) 16}

private theorem compact_box : IsCompact box := by
  let K := Set.pi (Set.univ:Set (Fin 4)) (fun _ => Icc (1/16:ℝ) 16)
  have h : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have e : (fun x : Fin 4→ℝ => (WithLp.toLp 2 x:E4)) '' K=box := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact fun i => hy i (mem_univ i)
    · intro hx
      refine ⟨fun i => x i,fun i _ => hx i,?_⟩
      ext i;rfl
  rw [←e]
  exact h.image (by fun_prop)

private theorem boxed : Function.support symbol⊆box := by
  intro x hx
  have a (i : Fin 4) (hi : i=0 ∨ i=1 ∨ i=2) : x i∈Icc (1/2:ℝ) (5/2) := by
    apply cutoff_nonzero_bounds
    intro z
    rcases hi with rfl|rfl|rfl <;> exact hx (by simp [symbol,z])
  have c : chi (x 3)≠0 := fun z => hx (by simp [symbol,z])
  have h := chi_tsupport_subset (subset_tsupport _ c)
  intro i
  fin_cases i
  · have p := a 0 (Or.inl rfl);exact ⟨by linarith [p.1],by linarith [p.2]⟩
  · have p := a 1 (Or.inr (Or.inl rfl));exact ⟨by linarith [p.1],by linarith [p.2]⟩
  · have p := a 2 (Or.inr (Or.inr rfl));exact ⟨by linarith [p.1],by linarith [p.2]⟩
  · exact ⟨h.1.le,h.2.le⟩

theorem smooth_symbol : ContDiff ℝ ∞ symbol := by
  have s := closure_minimal boxed compact_box.isClosed
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases h : x∈tsupport symbol
  · have p (i : Fin 4) : 0<x i := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/16) ((s h) i).1
    have coord (i : Fin 4) : ContDiffAt ℝ ∞ (fun y : E4 => y i) x :=
      (EuclideanSpace.proj (𝕜:=ℝ) i : E4→L[ℝ]ℝ).contDiff.contDiffAt
    have b (i : Fin 4) := dyadicCutoff_contDiff.contDiffAt.comp x (coord i)
    have root := ((coord 1).mul (coord 2)).sqrt (mul_pos (p 1) (p 2)).ne'
    have ratio := root.div ((coord 3).mul (coord 0)) (mul_pos (p 3) (p 0)).ne'
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (((((b 0).mul (b 1)).mul (b 2)).mul (chi_contDiff.contDiffAt.comp x (coord 3))).mul
        (dyadicCutoff_contDiff.contDiffAt.comp x ratio))
  · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E4 => (0:ℂ)) x).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp h)

theorem support_cell : Function.support symbol⊆inside64 := fun x hx i =>
  ⟨by linarith [(boxed hx i).1],by linarith [(boxed hx i).2]⟩

theorem compact_symbol : HasCompactSupport symbol :=
  HasCompactSupport.of_support_subset_isCompact compact_box boxed

def coefficient (k : D4→ℤ) := coeff symbol k

/-- Only this fixed function enters the constant. In particular the
level and the two Fourier marks have disappeared before coefficient pricing. -/
theorem lattice_budget (r : ℕ) :
    ∃ C : ℝ,0<C ∧ Summable (fun k : D4→ℤ => ‖coefficient k‖*(1+|((k 0:ℤ):ℝ)|)^r) ∧
      (∑' k : D4→ℤ,‖coefficient k‖*(1+|((k 0:ℤ):ℝ)|)^r)≤C := by
  have B := native_weighted_l1 symbol r (smooth_symbol.of_le (by simp)) compact_symbol support_cell
  have nn : 0≤weightedL1 symbol r := by
    unfold weightedL1
    exact tsum_nonneg (fun k => by dsimp [testWeight];positivity)
  exact ⟨1+weightedL1 symbol r,add_pos_of_pos_of_nonneg zero_lt_one nn,B.1,le_add_of_nonneg_left zero_le_one⟩

end
end ImbalancedChen.Part3.OriginalSwitchedFourCoordinateSymbol20261113
