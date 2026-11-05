import ImbalancedChen.P3FourierFrechetIBP
import ImbalancedChen.P3FourierDPointwise
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

Relates the ACTUAL ordinary coordinateDeriv/mixed on Point d to ordered
Fréchet derivatives on EuclideanSpace R (Fin d).  The same genuine
EuclideanSpace Fourier domain, unit coordinate directions and old doubled S
are used. No Fourier estimate or arithmetic distribution hypothesis is added.

The derivative bridge requires genuine ContDiff of the Euclidean pullback.
Its verification for every physical W_T family and the real-to-complex Fourier
bridge remain separate manuscript-internal obligations.
-/

namespace ImbalancedChen.P3FourierPointCoordinateBridge
noncomputable section

open scoped Classical BigOperators RealInnerProductSpace
open P3AffineTransitionJets P3FourierDPointwise P3FourierFrechetIBP
open P3U5ChartMixedL1Budget

/-- The pinned canonical finite-dimensional continuous linear equivalence,
not an unproved identification of the two norms or their measures. -/
abbrev chartEquiv (d : ℕ) : FourierSpace d ≃L[ℝ] Point d :=
  EuclideanSpace.equiv (Fin d) ℝ

/-- The physical Fourier-domain lift of a real Point d chart. -/
def chartLift {d : ℕ} (w : Point d → ℝ) : FourierSpace d → ℝ :=
  fun x => w (chartEquiv d x)

/-- Literal real Point d unit vector, used only to check the old shift. -/
def pointDirection {d : ℕ} (i : Fin d) : Point d :=
  Pi.single i (1 : ℝ)

/-- This is the precise old coordinate shift; no reordering or rescaling. -/
theorem shift_eq_add_direction {d : ℕ} (p : Point d)
    (i : Fin d) (t : ℝ) :
    shift p i t = p + t • pointDirection i := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [shift, pointDirection, Pi.single_apply]
  · simp [shift, pointDirection, Pi.single_apply, h, Ne.symm h]

/-- The two unit coordinate vectors agree under the explicit linear map. -/
theorem chartEquiv_basisDirection {d : ℕ} (i : Fin d) :
    chartEquiv d (basisDirection i) = pointDirection i := by
  rfl

/-- Coordinate line in the original Point d equals the line in the
actual EuclideanSpace on which the Fourier transform is taken. -/
theorem chart_shift {d : ℕ} (x : FourierSpace d)
    (i : Fin d) (t : ℝ) :
    chartEquiv d (x + t • basisDirection i) =
      shift (chartEquiv d x) i t := by
  calc
    chartEquiv d (x + t • basisDirection i) =
        chartEquiv d x + t • chartEquiv d (basisDirection i) := by
          simp
    _ = chartEquiv d x + t • pointDirection i := by
      rw [chartEquiv_basisDirection]
    _ = shift (chartEquiv d x) i t :=
      (shift_eq_add_direction (chartEquiv d x) i t).symm

private theorem hasDerivAt_coordinateLine {d : ℕ}
    (x v : FourierSpace d) :
    HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x

/-- Genuine FIRST coordinate differentiation of the original pulled back
function, paid by the actual Fréchet derivative on FourierSpace. -/
theorem coordinateDeriv_pulled_eq_fderiv {d : ℕ}
    (f : FourierSpace d → ℝ) (x : FourierSpace d) (i : Fin d)
    (hf : DifferentiableAt ℝ f x) :
    coordinateDeriv i (fun p : Point d => f ((chartEquiv d).symm p))
        (chartEquiv d x) =
      (fderiv ℝ f x) (basisDirection i) := by
  have hline :
      (fun t : ℝ => f ((chartEquiv d).symm
        (shift (chartEquiv d x) i t))) =
      (fun t : ℝ => f (x + t • basisDirection i)) := by
    funext t
    rw [← chart_shift x i t]
    simp
  unfold coordinateDeriv
  rw [hline]
  exact (hf.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_coordinateLine x (basisDirection i))).deriv

/-- Ordered directions: a FIN index for each original list entry. In
particular repeated coordinates are NOT collapsed to a Finset. -/
def orderedDirections {d : ℕ} :
    (js : List (Fin d)) → Fin js.length → FourierSpace d
  | [], j => Fin.elim0 j
  | i :: is, j => Fin.cons (basisDirection i) (orderedDirections is) j

/-- The ordered direction family is exactly the one used previously for
Fourier integration by parts, including repeated HB coordinates. -/
theorem orderedDirections_apply {d : ℕ} (js : List (Fin d))
    (j : Fin js.length) :
    orderedDirections js j = basisDirection (js[j]) := by
  induction js generalizing j with
  | nil => exact Fin.elim0 j
  | cons i is ih =>
      cases j using Fin.cases with
      | zero => rfl
      | succ k => simpa [orderedDirections] using ih k

/-- The first existing Fourier Frechet module uses this SAME 2S direction
family; hence no permutation or missing factor occurs on the index side. -/
theorem orderedDirections_doubled {d : ℕ} (S : Finset (Fin d)) :
    orderedDirections (doubled S) = subsetDirections S := by
  funext j
  exact orderedDirections_apply (doubled S) j

/-- All orders of the original coordinate derivatives are the genuine
ordered Fréchet derivative of the Euclidean pullback. We require ContDiff
at this EXACT finite order, not any Fourier/PP identity or derivative bound.
The order i :: is is preserved through Fin.cons and Fin.tail. -/
theorem mixed_pullback_eq_frechet {d : ℕ} (js : List (Fin d)) :
    ∀ (f : FourierSpace d → ℝ),
      ContDiff ℝ (js.length : ℕ∞) f →
      ∀ x : FourierSpace d,
        mixed js (fun p : Point d => f ((chartEquiv d).symm p))
          (chartEquiv d x) =
          (iteratedFDeriv ℝ js.length f x) (orderedDirections js) := by
  induction js with
  | nil =>
      intro f hf x
      simpa [mixed] using
        (iteratedFDeriv_zero_apply
          (f := f) (x := x)
          (m := orderedDirections ([] : List (Fin d)))).symm
  | cons i is ih =>
      intro f hf x
      have hsmall : ContDiff ℝ (is.length : ℕ∞) f :=
        hf.of_le (by exact_mod_cast Nat.le_succ is.length)
      let H : FourierSpace d → ℝ :=
        fun y => (iteratedFDeriv ℝ is.length f y) (orderedDirections is)
      have hEq :
          mixed is (fun p : Point d => f ((chartEquiv d).symm p)) =
          (fun p : Point d => H ((chartEquiv d).symm p)) := by
        funext p
        simpa [H] using ih f hsmall ((chartEquiv d).symm p)
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ is.length f) x :=
        (hf.differentiable_iteratedFDeriv (by simp)) x
      have hH : DifferentiableAt ℝ H x :=
        hd.continuousMultilinear_apply_const (orderedDirections is)
      have hsucc :
          (fderiv ℝ H x) (basisDirection i) =
          (iteratedFDeriv ℝ (is.length + 1) f x)
            (Fin.cons (basisDirection i) (orderedDirections is)) := by
        simpa [H] using
          (hd.iteratedFDeriv_succ_apply_left'
            (m := Fin.cons (basisDirection i) (orderedDirections is))).symm
      calc
        mixed (i :: is) (fun p : Point d => f ((chartEquiv d).symm p))
            (chartEquiv d x) =
            coordinateDeriv i
              (mixed is (fun p : Point d => f ((chartEquiv d).symm p)))
              (chartEquiv d x) := rfl
        _ = coordinateDeriv i
              (fun p : Point d => H ((chartEquiv d).symm p))
              (chartEquiv d x) := by rw [hEq]
        _ = (fderiv ℝ H x) (basisDirection i) :=
              coordinateDeriv_pulled_eq_fderiv H x i hH
        _ = (iteratedFDeriv ℝ (i :: is).length f x)
              (orderedDirections (i :: is)) := by
              simpa only [List.length_cons, orderedDirections] using hsucc

/-- Specialization back to the ACTUAL real Point d mixed function of the
original manuscript, without substituting a newly defined derivative. -/
theorem mixed_actual_eq_frechet {d : ℕ} (js : List (Fin d))
    (w : Point d → ℝ) (hw : ContDiff ℝ (js.length : ℕ∞) (chartLift w))
    (x : FourierSpace d) :
    mixed js w (chartEquiv d x) =
      (iteratedFDeriv ℝ js.length (chartLift w) x)
        (orderedDirections js) := by
  simpa [chartLift] using mixed_pullback_eq_frechet js (chartLift w) hw x

/-- The exact earlier 2S 'actualMixedFamily' is the cast of the REAL
Fréchet derivative, not merely a symbolic proxy. The complex Fourier
formula still needs the complexification and integrability instances. -/
theorem actualMixedFamily_eq_realFrechet {d : ℕ}
    (w : Point d → ℝ)
    (S : Finset (Fin d))
    (hw : ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (x : FourierSpace d) :
    actualMixedFamily w S x =
      (((iteratedFDeriv ℝ (doubled S).length (chartLift w) x)
        (subsetDirections S) : ℝ) : ℂ) := by
  change ((mixed (doubled S) w (chartEquiv d x) : ℝ) : ℂ) = _
  exact congrArg (fun y : ℝ => (y : ℂ))
    (by simpa only [orderedDirections_doubled] using
      mixed_actual_eq_frechet (doubled S) w hw x)

end
end ImbalancedChen.P3FourierPointCoordinateBridge
