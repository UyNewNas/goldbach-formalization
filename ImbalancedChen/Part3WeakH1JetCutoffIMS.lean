import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Weak testing extends to the closure of actual value/gradient test jets.
The cutoff-square jet then gives IMS by completing the square. These are
real Hilbert statements, hence apply to the realification of complex L2.
No regularity, test-jet approximation, or form-domain membership of a Gamma
adjoint vector is asserted. In particular closure membership below is an
explicit H1 test-legality obligation, not an energy-smallness assumption.
-/

namespace ImbalancedChen.Part3.WeakH1JetCutoffIMS20261026a

noncomputable section
open Set Filter

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- A test jet consists of its L2 value and its L2 weak gradient. -/
abbrev TestJet := E × G

def weakPair (f : E) (g : G) (v : TestJet (E := E) (G := G)) : ℝ :=
  inner ℝ v.1 f + inner ℝ v.2 g

theorem weakPair_continuous (f : E) (g : G) : Continuous (weakPair f g) := by
  exact (continuous_fst.inner continuous_const).add
    (continuous_snd.inner continuous_const)

/-- Only value/gradient convergence is required; convergence of second
derivatives is unnecessary for legitimate negative-one weak testing. -/
theorem weakPair_zero_on_closure (f : E) (g : G)
    (T : Set (TestJet (E := E) (G := G)))
    (hT : ∀ v ∈ T, weakPair f g v = 0)
    {v : TestJet (E := E) (G := G)} (hv : v ∈ closure T) :
    weakPair f g v = 0 := by
  have hs : IsClosed {v : TestJet (E := E) (G := G) | weakPair f g v = 0} :=
    isClosed_eq (weakPair_continuous f g) continuous_const
  exact closure_minimal hT hs hv

theorem weakPair_zero_of_jet_limit (f : E) (g : G)
    (v : ℕ → TestJet (E := E) (G := G))
    (hv : ∀ n, weakPair f g (v n) = 0)
    (w : TestJet (E := E) (G := G)) (hw : Tendsto v atTop (𝓝 w)) :
    weakPair f g w = 0 := by
  have hs : IsClosed {v : TestJet (E := E) (G := G) | weakPair f g v = 0} :=
    isClosed_eq (weakPair_continuous f g) continuous_const
  exact hs.mem_of_tendsto hw (Eventually.of_forall hv)

/-- Multiplication by a real cutoff on scalar and gradient L2. Symmetry
is the literal multiplier adjoint identity; no derivative is assumed for
the vector f. The vector d denotes f times the cutoff's weak gradient. -/
def cutoffSquareJet (M : E →L[ℝ] E) (D : G →L[ℝ] G)
    (f : E) (g d : G) : TestJet (E := E) (G := G) :=
  (M (M f), D (D g) + (2 : ℝ) • D d)

theorem cutoffSquareJet_pair (M : E →L[ℝ] E) (D : G →L[ℝ] G)
    (hM : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (hD : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y))
    (f : E) (g d : G) :
    weakPair f g (cutoffSquareJet M D f g d) =
      ‖M f‖ ^ 2 + ‖D g‖ ^ 2 + 2 * inner ℝ (D g) d := by
  unfold weakPair cutoffSquareJet
  dsimp only
  rw [inner_add_left, real_inner_smul_left, hM (M f) f,
    hD (D g) g, hD d g,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm (D g) d]
  ring

/-- Exact weak IMS identity. The sole test-legality hypothesis is that
the displayed Leibniz jet is approximable by tests for which the PDE is
already known. Neither IMS nor its bound is among the hypotheses. -/
theorem weak_cutoff_IMS (M : E →L[ℝ] E) (D : G →L[ℝ] G)
    (hM : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (hD : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y))
    (f : E) (g d : G) (T : Set (TestJet (E := E) (G := G)))
    (hPDE : ∀ v ∈ T, weakPair f g v = 0)
    (hlegal : cutoffSquareJet M D f g d ∈ closure T) :
    ‖D g + d‖ ^ 2 + ‖M f‖ ^ 2 = ‖d‖ ^ 2 := by
  have ht := weakPair_zero_on_closure f g T hPDE hlegal
  rw [cutoffSquareJet_pair M D hM hD] at ht
  rw [norm_add_sq_real]
  linarith

theorem weak_cutoff_Caccioppoli (M : E →L[ℝ] E) (D : G →L[ℝ] G)
    (hM : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (hD : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y))
    (f : E) (g d : G) (T : Set (TestJet (E := E) (G := G)))
    (hPDE : ∀ v ∈ T, weakPair f g v = 0)
    (hlegal : cutoffSquareJet M D f g d ∈ closure T) :
    ‖M f‖ ^ 2 ≤ ‖d‖ ^ 2 := by
  have h := weak_cutoff_IMS M D hM hD f g d T hPDE hlegal
  linarith [sq_nonneg ‖D g + d‖]

/-- Exhausting legal weak tests kill a negative-one defect. The input
limits concern actual cutoff multiplication and its commutator vector;
they are not assumed small-energy estimates for the unknown gradient. -/
theorem eq_zero_of_exhausting_legal_tests
    (M : ℕ → E →L[ℝ] E) (D : ℕ → G →L[ℝ] G)
    (hM : ∀ n x y, inner ℝ (M n x) y = inner ℝ x (M n y))
    (hD : ∀ n x y, inner ℝ (D n x) y = inner ℝ x (D n y))
    (f : E) (g : ℕ → G) (d : ℕ → G)
    (T : Set (TestJet (E := E) (G := G)))
    (hPDE : ∀ n v, v ∈ T → weakPair f (g n) v = 0)
    (hlegal : ∀ n, cutoffSquareJet (M n) (D n) f (g n) (d n) ∈ closure T)
    (hMf : Tendsto (fun n => M n f) atTop (𝓝 f))
    (hd : Tendsto d atTop (𝓝 0)) : f = 0 := by
  have hi : ∀ n, ‖M n f‖ ^ 2 ≤ ‖d n‖ ^ 2 := fun n =>
    weak_cutoff_Caccioppoli (M n) (D n) (hM n) (hD n) f (g n) (d n)
      T (hPDE n) (hlegal n)
  have hz : ‖f‖ ^ 2 ≤ (0 : ℝ) := by
    have h := le_of_tendsto_of_tendsto (hMf.norm.pow 2) (hd.norm.pow 2)
      (Eventually.of_forall hi)
    simpa using h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hz (sq_nonneg _)))

end
end ImbalancedChen.Part3.WeakH1JetCutoffIMS20261026a
