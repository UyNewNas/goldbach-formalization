import ImbalancedChen.Part3OriginalSwitchedMellinRows
import ImbalancedChen.Part3ActualSeparatedRowLogModeSupplier

/-! Uniform derivatives of the actual one- and two-cutoff families on
the normalized period cell; all constants precede the switching parameters. -/
namespace ImbalancedChen.Part3.OriginalSwitchedCutoffFamily20261113
noncomputable section
open Set Complex Filter CommonSmoothCutoff
open scoped ContDiff Topology
open P3CompactCoordinateSourceOnly (coeff64)

/-- u=Yx, L=4πY√(mn)/(dQ). -/
def profile (second : Bool) (L u : ℝ) : ℂ :=
  (dyadicCutoff u:ℂ)*(if second then (dyadicCutoff (L/u):ℂ) else 1)

theorem support (s : Bool) (L : ℝ) :
    tsupport (profile s L) ⊆ Icc (1/2:ℝ) (5/2) := by
  rw [←dyadicCutoff_tsupport_eq_tight]
  apply closure_mono
  intro u hu
  by_contra h
  exact hu (by simp [profile,show dyadicCutoff u=0 from not_ne_iff.mp h])

theorem parameter_support {L u : ℝ} (h : profile true L u≠0) : L ∈ Icc (1/4:ℝ) (25/4) := by
  have U := support true L (subset_tsupport _ h)
  have nz : dyadicCutoff (L/u)≠0 := by intro eq; exact h (by simp [profile,eq])
  have V : L/u ∈ Icc (1/2:ℝ) (5/2) := by
    rw [←dyadicCutoff_tsupport_eq_tight]
    exact subset_tsupport _ nz
  have up : 0<u := by linarith [U.1]
  have lo := (le_div_iff₀ up).mp V.1
  have hi := (div_le_iff₀ up).mp V.2
  constructor <;> linarith [U.1,U.2]

theorem parameter_zero {L : ℝ} (h : L ∉ Icc (1/4:ℝ) (25/4)) :
    profile true L=0 := by
  funext u
  by_contra z
  exact h (parameter_support z)

private theorem joint_smooth (s : Bool) : ContDiff ℝ ∞ (fun p : ℝ×ℝ => profile s p.1 p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases z : p.2=0
  · have nb : ∀ᶠ w : ℝ×ℝ in 𝓝 p,w.2 < 1/2 :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds (by simp [z])
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ×ℝ => (0:ℂ)) p).congr_of_eventuallyEq
    filter_upwards [nb] with w hw
    by_contra h
    exact (not_le_of_gt hw) (support s w.1 (subset_tsupport _ h)).1
  · cases s with
    | false => simpa [profile] using
        (Complex.ofRealCLM.contDiff.comp (dyadicCutoff_contDiff.comp contDiff_snd)).contDiffAt (x:=p)
    | true =>
      have div : ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => w.1/w.2) p :=
        contDiff_fst.contDiffAt.div contDiff_snd.contDiffAt z
      exact ((Complex.ofRealCLM.contDiff.comp (dyadicCutoff_contDiff.comp contDiff_snd)).contDiffAt).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp p (dyadicCutoff_contDiff.contDiffAt.comp p div))

theorem profile_smooth (s : Bool) (L : ℝ) : ContDiff ℝ ∞ (profile s L) :=
  (joint_smooth s).comp (contDiff_prodMk_right L)

private def jet (s : Bool) : ℕ→(ℝ×ℝ)→ℂ
  | 0 => fun p => profile s p.1 p.2
  | r+1 => fun p => fderiv ℝ (jet s r) p (0,1)

private theorem jet_smooth (s : Bool) (r : ℕ) : ContDiff ℝ ∞ (jet s r) := by
  induction r with
  | zero => exact joint_smooth s
  | succ r ih => exact (contDiff_infty_iff_fderiv.mp ih).2.clm_apply contDiff_const

private theorem jet_slice (s : Bool) (r : ℕ) (L : ℝ) :
    iteratedDeriv r (profile s L)=fun u => jet s r (L,u) := by
  induction r with
  | zero => simp [jet]
  | succ r ih =>
    rw [iteratedDeriv_succ,ih]
    funext u
    have h := ((jet_smooth s r).differentiable (by simp) (L,u)).hasFDerivAt
    exact (h.comp_hasDerivAt u ((hasDerivAt_const u L).prodMk (hasDerivAt_id u))).deriv

/-- Uniform in every real L. The traces can therefore use the same
coefficient budget for every pair of marks on every level. -/
theorem uniform_jet (r : ℕ) : ∃ B : ℝ,0<B ∧ ∀ (s : Bool) (L u : ℝ),
    u ∈ Icc (-32:ℝ) 32 → ‖iteratedDeriv r (profile s L) u‖ ≤ B := by
  let K := Icc (1/4:ℝ) (25/4) ×ˢ Icc (-32:ℝ) 32
  have k : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨A,hA⟩ := k.exists_bound_of_continuousOn (jet_smooth false r).continuous.continuousOn
  obtain ⟨B,hB⟩ := k.exists_bound_of_continuousOn (jet_smooth true r).continuous.continuousOn
  let C := 1+|A|+|B|
  have cp : 0<C := by dsimp [C]; positivity
  refine ⟨C,cp,?_⟩
  intro s L u hu
  cases s with
  | false =>
    have eq : profile false L=profile false 1 := by funext x; simp [profile]
    rw [eq,jet_slice]
    exact (hA (1,u) ⟨by norm_num,hu⟩).trans (by dsimp [C]; linarith [le_abs_self A,abs_nonneg B])
  | true =>
    by_cases h : L∈Icc (1/4:ℝ) (25/4)
    · rw [jet_slice]
      exact (hB (L,u) ⟨h,hu⟩).trans (by dsimp [C]; linarith [le_abs_self B,abs_nonneg A])
    · have z (j : ℕ) : iteratedDeriv j (0 : ℝ→ℂ)=0 := by
        induction j with
        | zero => simp
        | succ j ih => simp [iteratedDeriv_succ,ih]
      rw [parameter_zero h,z]
      simpa using cp.le

end
end ImbalancedChen.Part3.OriginalSwitchedCutoffFamily20261113
