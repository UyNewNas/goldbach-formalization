import ImbalancedChen.Part3MaassFirstGradientWeakLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The coordinate gradients in the actual hyperbolic form are zero below and
on height zero. Their planar L² limits retain this property. The proof
constructs the actual supported closed subspace and uses the pinned theorem
that Lp convergence has an a.e. convergent subsequence. No support property
of the limit is assumed.

Together with the preceding first-gradient weak-limit module, this leaves
only actual upper-chart compact tensor test density for zero-gradient
uniqueness. That density and full form closability are still OPEN here.
-/

namespace ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a

noncomputable section
open MeasureTheory Filter
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a

/-- The actual planar L² subspace supported in the open positive-height chart.
The support condition is a.e.; no pointwise representative is selected. -/
def upperSupportedSubmodule : Submodule ℂ PlaneL2 where
  carrier := {G | ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ upperChart → G p = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ × ℝ))] with p hp
    intro _
    exact hp
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with p hpf hpg hsum
    intro hp
    rw [hsum]
    simp only [Pi.add_apply, hpf hp, hpg hp, add_zero]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with p hpf hsmul
    intro hp
    rw [hsmul]
    simp only [Pi.smul_apply, hpf hp, smul_zero]

/-- This is a proved closed subspace of the actual planar L² space.
The a.e. subsequence argument works for Lebesgue's infinite measure. -/
theorem isClosed_upperSupportedSubmodule :
    IsClosed (upperSupportedSubmodule : Set PlaneL2) := by
  apply IsSeqClosed.isClosed
  intro f G hf hlim
  have hmem : ∀ n, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      p ∉ upperChart → f n p = 0 := hf
  obtain ⟨ns, _, hns⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  change ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ upperChart → G p = 0
  filter_upwards [countable_iInter_mem.mpr hmem, hns] with p hp hpae
  intro hout
  have hzero : ∀ i : ℕ, f (ns i) p = 0 := by
    intro i
    exact (Set.mem_iInter.mp hp (ns i)) hout
  have htzero : Tendsto (fun i : ℕ => f (ns i) p) atTop (nhds (0 : ℂ)) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  exact tendsto_nhds_unique hpae htzero

/-- Both actual tensor derivatives vanish at every nonpositive height.
The vertical derivative uses the actual support-of-derivative theorem. -/
theorem tensorGradient_zero_outside_upperChart (vertical : Bool) (T : CompactTensor)
    (p : ℝ × ℝ) (hp : p ∉ upperChart) : tensorGradient vertical T p = 0 := by
  have hv : T.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (T.vertical_positive h))
  have hdv : deriv T.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (T.vertical_positive (tsupport_deriv_subset h)))
  cases vertical <;> simp [tensorGradient, tensorDx, tensorDy, hv, hdv]

theorem finiteGradient_zero_outside_upperChart {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) (p : ℝ × ℝ) (hp : p ∉ upperChart) :
    finiteGradient vertical s T p = 0 := by
  unfold finiteGradient
  apply Finset.sum_eq_zero
  intro i _
  exact tensorGradient_zero_outside_upperChart vertical (T i) p hp

/-- Membership follows from the actual gradient formula and its toLp a.e.
identity; no caller supplies an abstract support contract. -/
theorem gradientL2_mem_upperSupportedSubmodule {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) :
    gradientL2 vertical s T ∈ upperSupportedSubmodule := by
  change ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
    p ∉ upperChart → gradientL2 vertical s T p = 0
  filter_upwards [(finiteGradient_memLp vertical s T).coeFn_toLp] with p hp
  intro hout
  change gradientL2 vertical s T p = finiteGradient vertical s T p at hp
  rw [hp]
  exact finiteGradient_zero_outside_upperChart vertical s T p hout

/-- L² gradient limits retain zero on the whole lower complement, including
the height-zero face. No input-function convergence is needed for this fact. -/
theorem gradient_limit_mem_upperSupportedSubmodule (vertical : Bool)
    (k : ℕ → ℕ) (T : (n : ℕ) → Fin (k n) → CompactTensor) (G : PlaneL2)
    (hgradient : Tendsto (fun n => gradientL2 vertical Finset.univ (T n))
      atTop (nhds G)) :
    G ∈ upperSupportedSubmodule :=
  isClosed_upperSupportedSubmodule.mem_of_tendsto hgradient
    (Eventually.of_forall fun n =>
      gradientL2_mem_upperSupportedSubmodule vertical Finset.univ (T n))

theorem gradient_limit_zero_outside_upperChart (vertical : Bool)
    (k : ℕ → ℕ) (T : (n : ℕ) → Fin (k n) → CompactTensor) (G : PlaneL2)
    (hgradient : Tendsto (fun n => gradientL2 vertical Finset.univ (T n))
      atTop (nhds G)) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ upperChart → G p = 0 :=
  gradient_limit_mem_upperSupportedSubmodule vertical k T G hgradient

end
end ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a
