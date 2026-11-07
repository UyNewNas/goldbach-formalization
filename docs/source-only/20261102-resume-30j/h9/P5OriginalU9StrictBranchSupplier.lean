import ImbalancedChen.P5OriginalU9RepeatedPhysicalPP
import ImbalancedChen.P5zUpsilon9OriginalSlot

/-!
# Original h9: repeated-coordinate PP condition removed

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The fixed actual rho is never changed, and its active support is removed
only by an exact zero-coefficient identity. The actual one-bound and
positive modulus support are proved suppliers, not new hypotheses.

The strict-coordinate source PP estimates, same-rho density, original
independent integral endpoints and full policy licence remain OPEN.
-/

namespace ImbalancedChen.P5OriginalU9RepeatedPP

noncomputable section
open Classical Filter

theorem eventually_repeatedPP_of_real_scope (scopeNu : ℝ) (hscopeNu : 0 ≤ scopeNu)
    (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin 3, ∀ D : Finset ℕ, ∀ rho : ℕ → ℝ,
      (∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ scopeNu) →
      (∀ d ∈ D, |rho d| ≤ 1) →
      |Part3.primeProductSignedError 3 N N D rho (repeatedWeight j N)| ≤
        (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [eventually_repeatedPP_log_bound scopeNu hscopeNu A] with N hN
  intro j D rho hD hrho
  apply hN j D (Nat.floor ((N : ℝ) ^ scopeNu)) rho ?_
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hrho
  intro d hd
  exact Finset.mem_Icc.mpr ⟨(hD d hd).1, Nat.le_floor (hD d hd).2⟩

/-- This is the SAME attachedUpperCoefficient used by the original h9
supplier, with its raw one-bound proved from unique small/rough factoring.
Only the existing original active-support scope remains as an input. -/
theorem eventually_actual_repeatedPP (nu r e scopeNu : ℝ) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (∀ d : ℕ, d ∈ attachedUpperModuli nu r e retain cap N →
        attachedUpperCoefficient nu r e retain cap N d ≠ 0 →
          (d : ℝ) ≤ (N : ℝ) ^ scopeNu) → ∀ j : Fin 3,
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) (repeatedWeight j N)| ≤
          (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [eventually_repeatedPP_of_real_scope scopeNu hscopeNu A] with N hN
  intro hscope j
  let R := attachedUpperCoefficient nu r e retain cap N
  let D := p5z_activeModuli (attachedUpperModuli nu r e retain cap N) R
  have hD : ∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ scopeNu := by
    intro d hd
    obtain ⟨hdD, hdne⟩ := Finset.mem_filter.mp hd
    have hsq := actualSmallRoughModuli_squarefree (retain N) N (cap N) _ _ hdD
    exact ⟨Nat.one_le_iff_ne_zero.mpr hsq.ne_zero, hscope d hdD hdne⟩
  have hrho : ∀ d ∈ D, |R d| ≤ 1 := by
    intro d hd
    exact actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d
  have hbound := hN j D R hD hrho
  dsimp only [D] at hbound
  rw [p5z_active_primeProductSignedError] at hbound
  exact hbound

/-- Restores every repeated-coordinate contribution of all three ordered
branches at the original N/log^3 scale. Only STRICT source PP remains.
There is no new estimate assumed on the deleted repeated source. -/
theorem original_branch_PP_of_strict (nu r e scopeNu : ℝ) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 →
        (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hstrict : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Even N → Licensed N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (strictWeight j N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Even N → Licensed N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (p5z_u9_orderedPhysicalWeight j N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
  intro j
  obtain ⟨C, hC, hstrictJ⟩ := hstrict j
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  filter_upwards [hstrictJ, hscope,
    eventually_actual_repeatedPP nu r e scopeNu hscopeNu retain cap 3]
      with N hstrictN hscopeN hrepeatN
  intro hEven hL
  rw [physicalPP_split]
  calc
    _ ≤ |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (strictWeight j N)| +
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (repeatedWeight j N)| := abs_add _ _
    _ ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 3 +
        (N : ℝ) / Real.log (N : ℝ) ^ 3 :=
      add_le_add (hstrictN hEven hL) (hrepeatN (hscopeN hEven hL) j)
    _ = (C + 1) * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by ring

end
end ImbalancedChen.P5OriginalU9RepeatedPP

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section
open Filter
open P5OriginalU9RepeatedPP

/-- The exact original h9 consumer with its repeated-coordinate PP port
now discharged. This statement retains both original numerical endpoints;
it does NOT certify them, the strict PP source or the policy density. -/
theorem original_h9_of_strict_actual_rho
    (nu r e scopeNu : ℝ) (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1 / 8)
    (heR : e ^ 2 ≤ r) (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hUpper : currentChenUpsilon9HarmonicIntegral ≤ p5z_originalU9UpperIntegralEndpoint)
    (hLower : p5z_originalU9LowerIntegralEndpoint ≤ currentChenUpsilon9HarmonicIntegral)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 →
        (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤
          fixedProductDensityCoefficient * (singularSeries N / Real.log (N : ℝ)))
    (hstrict : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Even N → Licensed N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (strictWeight j N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (U9Envelope fixedProductDensityCoefficient + delta) * singularNormalization N := by
  exact p5z_original_h9_of_fixed_actual_rho nu r e scopeNu hnu he he8 heR hnur hscopeNu
    retain cap Licensed hUpper hLower hlicensed hcap hscope hdensity
      (original_branch_PP_of_strict nu r e scopeNu hscopeNu retain cap Licensed hscope hstrict)

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
