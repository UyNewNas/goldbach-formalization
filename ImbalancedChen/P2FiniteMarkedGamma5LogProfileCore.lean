import ImbalancedChen.P2SeedOmegaCutoffConstants
import ImbalancedChen.P4BSmoothGateUpperStep
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FunProp

/-!
SOURCE ONLY / UNCOMPILED / ZERO ENDPOINT CREDIT.

Lossless extraction of the original logarithmic Gamma5 profile and its
scalar geometry and smoothness lemmas. Every declaration below is moved
verbatim from P2FiniteMarkedGamma5LogExtension, keeping the same namespace
and fully qualified name; the original arithmetic extension imports this
core and no longer redeclares this block.

Acceptance of this lightweight core or its derivative budget does not
validate the original arithmetic-source plateau. That separate heavy
closure still has to compile and pass its original source/owned audits.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5LogExtension

noncomputable section
open Finset Real
open P4B
open P2SeedOmegaLiteralFibre (a0 a2)
open scoped Classical BigOperators ContDiff

/-- Physical logarithms: old complete prefix, two fresh slots, rough tail.
The number of tail slots is arbitrary and may be zero. -/
abbrev Point (r : ℕ) := ℝ × (Fin 2 → ℝ) × (Fin r → ℝ)

inductive Gate (r : ℕ) where
  | lower (i : Fin 2)
  | upper (i : Fin 2)
  | pairOrder
  | badSquare
  | rough (i : Fin r)
  | tailOrder (i j : Fin r)
  | product
  deriving DecidableEq, Fintype

def active {r : ℕ} : Gate r → Prop
  | .tailOrder i j => i < j
  | _ => True

def program (r : ℕ) : Finset (Gate r) := univ.filter active

/-- The original upper endpoints and pair order are strict. The bad wall,
lower cutoff, rough tail, tail order, and ordinary product cap are closed. -/
def openFace {r : ℕ} : Gate r → Bool
  | .upper _ | .pairOrder => true
  | _ => false

def margin {r : ℕ} (logQ logN : ℝ) (v : Point r) : Gate r → ℝ
  | .lower i => v.2.1 i - a0 * (logQ - v.1)
  | .upper i => a2 * (logQ - v.1) - v.2.1 i
  | .pairOrder => v.2.1 1 - v.2.1 0
  | .badSquare => v.1 + 2 * v.2.1 0 + v.2.1 1 - logQ
  | .rough i => v.2.2 i - a0 * (logQ - v.1)
  | .tailOrder i j => v.2.2 j - v.2.2 i
  | .product => logN - (v.1 + v.2.1 0 + v.2.1 1 + ∑ i, v.2.2 i)

def passed {r : ℕ} (logQ logN : ℝ) (v : Point r) (g : Gate r) : Prop :=
  if openFace g then 0 < margin logQ logN v g else 0 ≤ margin logQ logN v g

def accepted {r : ℕ} (logQ logN : ℝ) (v : Point r) : Prop :=
  ∀ g ∈ program r, passed logQ logN v g

def profile {r : ℕ} (logQ logN width : ℝ) (v : Point r) : ℝ :=
  ∏ g ∈ program r, smoothGateUpperStep width (margin logQ logN v g)

theorem mem_program {r : ℕ} {g : Gate r} : g ∈ program r ↔ active g := by
  simp [program]

theorem profile_bounds {r : ℕ} (logQ logN width : ℝ) (v : Point r) :
    0 ≤ profile logQ logN width v ∧ profile logQ logN width v ≤ 1 :=
  ⟨prod_nonneg (fun _ _ => smoothGateUpperStep_nonneg _ _),
    prod_le_one (fun _ _ => smoothGateUpperStep_nonneg _ _)
      (fun _ _ => smoothGateUpperStep_le_one _ _)⟩

theorem profile_one {r : ℕ} {logQ logN width : ℝ} {v : Point r}
    (hw : 0 < width) (hv : accepted logQ logN v) :
    profile logQ logN width v = 1 := by
  unfold profile
  apply prod_eq_one
  intro g hg
  have h := hv g hg
  have hm : 0 ≤ margin logQ logN v g := by
    unfold passed at h
    split at h
    · exact h.le
    · exact h
  exact smoothGateUpperStep_eq_one hw hm

theorem profile_nonzero_margin {r : ℕ} {logQ logN width : ℝ} {v : Point r}
    (hw : 0 < width) (hv : profile logQ logN width v ≠ 0)
    (g : Gate r) (hg : g ∈ program r) :
    -width < margin logQ logN v g := by
  unfold profile at hv
  exact smoothGateUpperStep_nonzero_support hw ((prod_ne_zero_iff.mp hv) g hg)

theorem contDiff_margin {r : ℕ} (logQ logN : ℝ) (g : Gate r) {k : ℕ∞} :
    ContDiff ℝ k (fun v : Point r => margin logQ logN v g) := by
  cases g <;> simp only [margin] <;> fun_prop

theorem contDiff_profile {r : ℕ} (logQ logN width : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (profile (r := r) logQ logN width) := by
  unfold profile
  apply contDiff_prod
  intro g _
  exact (contDiff_smoothGateUpperStep width).comp (contDiff_margin logQ logN g)

end
end ImbalancedChen.P2FiniteMarkedGamma5LogExtension
