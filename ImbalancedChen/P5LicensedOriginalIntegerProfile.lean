import ImbalancedChen.P5OriginalPrimeChartHBWitnesses
import Mathlib

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- An ambient smooth geometric profile is a genuine primitive licence.
-- A native prime/sorted fibre is NOT automatically such a licence.
-- The actual W_N admissible-family instance remains separately held.
namespace ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
noncomputable section
open Classical
open scoped BigOperators
open ExactOriginalSmoothDyadicPartition

structure Licence (k : ℕ) (Wprime : (Fin k → ℕ) → ℝ) where
  ambient : (Fin k → ℝ) → ℝ
  smooth : ContDiff ℝ ∞ ambient
  agrees_on_primes : ∀ u : Fin k → ℕ, (∀ i, (u i).Prime) →
    ambient (fun i => (u i : ℝ)) = Wprime u

def integerExtension {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (u : Fin k → ℕ) : ℝ :=
  L.ambient (fun i => (u i : ℝ))

theorem integerExtension_eq_on_primes {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (u : Fin k → ℕ) (hu : ∀ i, (u i).Prime) :
    integerExtension L u = Wprime u := L.agrees_on_primes u hu

def chartAmbient {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (T kappa0 : ℝ)
    (Rs : Fin k → ℝ) (u : Fin k → ℝ) : ℝ :=
  L.ambient u * eta ((∏ i, u i)/T^(1-kappa0)) *
    ∏ i, (chi (u i/Rs i)-chi (2*(u i/Rs i)))

theorem chartAmbient_smooth {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ)
    (hchi : ContDiff ℝ ∞ chi) (heta : ContDiff ℝ ∞ eta)
    (T kappa0 : ℝ) (Rs : Fin k → ℝ) :
    ContDiff ℝ ∞ (chartAmbient L chi eta T kappa0 Rs) := by
  have hL := L.smooth
  unfold chartAmbient
  fun_prop

-- The original eta/product and every original psi are retained as
-- smooth functions of group products after HB. No group wall is added.
def groupedProducts {k m : ℕ} (slots : Fin k → Finset (Fin m))
    (v : Fin m → ℝ) : Fin k → ℝ := fun i => ∏ j ∈ slots i, v j

theorem groupedProducts_smooth {k m : ℕ} (slots : Fin k → Finset (Fin m)) :
    ContDiff ℝ ∞ (groupedProducts slots) := by
  unfold groupedProducts
  fun_prop

theorem HB_chart_pullback_smooth {k m : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ)
    (hchi : ContDiff ℝ ∞ chi) (heta : ContDiff ℝ ∞ eta)
    (T kappa0 : ℝ) (Rs : Fin k → ℝ) (slots : Fin k → Finset (Fin m)) :
    ContDiff ℝ ∞ (fun v => chartAmbient L chi eta T kappa0 Rs (groupedProducts slots v)) :=
  (chartAmbient_smooth L chi eta hchi heta T kappa0 Rs).comp (groupedProducts_smooth slots)

def listExtension {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (u : List ℕ) : ℝ :=
  if h : u.length = k then L.ambient (fun i => (u[i.val]'(by omega) : ℝ)) else 0

theorem listExtension_ofFn {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (u : Fin k → ℕ) :
    listExtension L (List.ofFn u) = integerExtension L u := by
  simp [listExtension,integerExtension]

theorem prime_chart_value {k : ℕ} {Wprime : (Fin k → ℕ) → ℝ}
    (L : Licence k Wprime) (chi eta : ℝ → ℝ) (T kappa0 : ℝ)
    (js : Fin k → ℕ) (u : Fin k → ℕ) (hu : ∀ i, (u i).Prime) :
    chartAmbient L chi eta T kappa0 (fun i => R (js i)) (fun i => (u i : ℝ)) =
      Wprime u * eta (((∏ i, u i : ℕ) : ℝ)/T^(1-kappa0)) *
        ∏ i, bump chi ((u i : ℝ)/R (js i)) := by
  unfold chartAmbient bump
  rw [L.agrees_on_primes u hu]
  simp only [Nat.cast_prod]

end
end ImbalancedChen.P5Z.LicensedOriginalIntegerProfile
