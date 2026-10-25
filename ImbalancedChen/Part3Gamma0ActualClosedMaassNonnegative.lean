import ImbalancedChen.Part3Gamma0ActualMaassClosedOperator
import ImbalancedChen.Part3ActualGamma0PoincareEnergy

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Nonnegative energy passes from the actual smooth Gamma0 quotient core to
the actual closed Gamma0 Maass graph. The nonnegative quadratic-pairing
set is closed in the genuine quotient-L2 product Hilbert space, so graph
closure preserves it. The input is the actual derived core energy theorem,
not an hNonnegative premise or a whole-plane operator substitution.

The actual closed operator then satisfies the shifted quadratic coercive
bound and the norm lower bound for I+A. Its shift is injective, with an
explicit difference norm bound. No surjectivity, resolvent existence or
self-adjointness is claimed.
-/

namespace ImbalancedChen.Part3.Gamma0ActualClosedMaassNonnegative20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.ActualGamma0PoincareEnergy20261025a

/-- Nonnegative energy is inherited by the closure of the ACTUAL input/
output graph, using continuity of the canonical Hilbert pairing. -/
theorem closedGammaGraph_nonneg (N : ℕ) [NeZero N] {u v : QuotientL2 N}
    (h : (u,v) ∈ closedGammaGraph N) : 0 ≤ (inner ℂ u v).re := by
  have hclosed : IsClosed {p : QuotientL2 N × QuotientL2 N |
      0 ≤ (inner ℂ p.1 p.2).re} :=
    isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_fst.inner continuous_snd))
  have hcore : (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) ⊆
      {p | 0 ≤ (inner ℂ p.1 p.2).re} := by
    intro p hp
    have hu : p.1 ∈ smoothCore N := (coreGraph_domain_iff N p.1).mp ⟨p.2,hp⟩
    have hv := (coreGraph_iff_operator N ⟨p.1,hu⟩ p.2).mp hp
    rw [hv]
    exact actualCoreLaplacian_nonneg N ⟨p.1,hu⟩
  exact (closure_minimal hcore hclosed) h

theorem actualClosedGammaMaass_nonneg (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    0 ≤ (inner ℂ (u : QuotientL2 N) (actualClosedGammaMaass N u)).re :=
  closedGammaGraph_nonneg N (actualClosedGammaMaass_mem_graph N u)

/-- The shift uses exactly the true closed operator on its actual domain. -/
def actualClosedGammaShift (N : ℕ) [NeZero N] :
    (actualClosedGammaMaass N).domain →ₗ[ℂ] QuotientL2 N :=
  (actualClosedGammaMaass N).domain.subtype + (actualClosedGammaMaass N).toFun

@[simp] theorem actualClosedGammaShift_apply (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    actualClosedGammaShift N u = (u : QuotientL2 N) + actualClosedGammaMaass N u := rfl

theorem actualClosedGammaMaass_shifted_coercive (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    ‖(u : QuotientL2 N)‖^2 ≤
      (inner ℂ (u : QuotientL2 N) ((u : QuotientL2 N)+actualClosedGammaMaass N u)).re := by
  rw [inner_add_right,Complex.add_re]
  have hself : (inner ℂ (u : QuotientL2 N) (u : QuotientL2 N)).re = ‖(u : QuotientL2 N)‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (u : QuotientL2 N)
  rw [hself]
  linarith [actualClosedGammaMaass_nonneg N u]

/-- Cauchy--Schwarz turns the quadratic bound into a norm lower bound. -/
theorem actualClosedGammaShift_norm_lower (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    ‖(u : QuotientL2 N)‖ ≤ ‖actualClosedGammaShift N u‖ := by
  have hquad := actualClosedGammaMaass_shifted_coercive N u
  have hCS := re_inner_le_norm (𝕜 := ℂ) (u : QuotientL2 N) (actualClosedGammaShift N u)
  change ‖(u : QuotientL2 N)‖^2 ≤
    (inner ℂ (u : QuotientL2 N) (actualClosedGammaShift N u)).re at hquad
  by_cases hu : (u : QuotientL2 N) = 0
  · simp only [hu,norm_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖(u : QuotientL2 N)‖ := norm_pos_iff.mpr hu
    apply (mul_le_mul_left hpos).1
    simpa only [pow_two] using hquad.trans hCS

theorem actualClosedGammaShift_difference_norm_lower (N : ℕ) [NeZero N]
    (u v : (actualClosedGammaMaass N).domain) :
    ‖(u : QuotientL2 N)-(v : QuotientL2 N)‖ ≤
      ‖actualClosedGammaShift N u-actualClosedGammaShift N v‖ := by
  simpa only [Submodule.coe_sub,map_sub] using actualClosedGammaShift_norm_lower N (u-v)

/-- Injectivity is proved on the actual closed domain. This asserts no
existence of solutions outside the shift's actual range. -/
theorem actualClosedGammaShift_injective (N : ℕ) [NeZero N] :
    Function.Injective (actualClosedGammaShift N) := by
  intro u v huv
  have hnorm := actualClosedGammaShift_difference_norm_lower N u v
  rw [huv,sub_self,norm_zero] at hnorm
  have hz : (u : QuotientL2 N)-(v : QuotientL2 N) = 0 :=
    norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  exact Subtype.ext (sub_eq_zero.mp hz)

end
end ImbalancedChen.Part3.Gamma0ActualClosedMaassNonnegative20261025a
