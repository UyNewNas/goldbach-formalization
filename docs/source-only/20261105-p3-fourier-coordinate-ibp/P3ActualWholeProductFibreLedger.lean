import ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger

/-!
P3.6 / frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§3–4 (T),(F), manuscript-body.tex eq:current-PP.

Regroup the GENUINE three independent ordered original prime boxes and
actual fixed-product rough-HB positional coefficients by the COMPLETE
physical integer B. The fibres retain all original order, repetitions,
and positional geometry W; only the arithmetic kernel is indexed by B.

The quantitative L1 result is deliberately finite and exact: merging
distinct source triples with the same product never enlarges the total
absolute coefficient mass. This is the coefficient-side entrance for the
one-variable mixed shifted-divisor moment, NOT its logarithmic saving.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualWholeProductFibreLedger
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
open ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox

/-- Exact finite source-fibre partition. This is a partition by the
FULL integer f x, with no assumption that f is injective. -/
theorem sum_by_full_product_fibre
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [AddCommMonoid γ]
    (S : Finset α) (f : α → β) (c : α → γ) :
    (∑ B ∈ S.image f, ∑ x ∈ S.filter (fun x => f x = B), c x) =
      ∑ x ∈ S, c x := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem : f x ∈ S.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  simp [hmem]

/-- Regrouping commutes with any physical response function of the
complete product. Repeated products are summed with their full
multiplicity; no signed cancellation or complex coefficient is dropped. -/
theorem weighted_sum_by_full_product_fibre
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (c : α → ℂ) (R : β → ℂ) :
    (∑ B ∈ S.image f,
      (∑ x ∈ S.filter (fun x => f x = B), c x) * R B) =
      ∑ x ∈ S, c x * R (f x) := by
  classical
  calc
    _ = ∑ B ∈ S.image f,
          ∑ x ∈ S.filter (fun x => f x = B), c x * R (f x) := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          have hfx : f x = B := (Finset.mem_filter.mp hx).2
          rw [hfx]
    _ = _ := sum_by_full_product_fibre S f (fun x => c x * R (f x))

/-- The exact L1 price of regrouping is at most the ORIGINAL positional
absolute coefficient mass, even when many ordered triples have the same
complete integer. This uses triangle inequality only, never a target PP
bound or a fake injectivity hypothesis. -/
theorem full_product_fibre_l1_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (c : α → ℂ) :
    (∑ B ∈ S.image f,
      ‖∑ x ∈ S.filter (fun x => f x = B), c x‖) ≤
      ∑ x ∈ S, ‖c x‖ := by
  classical
  calc
    _ ≤ ∑ B ∈ S.image f,
          ∑ x ∈ S.filter (fun x => f x = B), ‖c x‖ := by
            apply Finset.sum_le_sum
            intro B hB
            exact norm_sum_le _ _
    _ = _ := sum_by_full_product_fibre S f (fun x => ‖c x‖)

/-- The actual THREE independent fine-prime ordered boxes, not
three separately normalized, separately tested products. -/
def actualHBTriples (N : ℕ) (τ : ℝ)
    (u v w : List ℕ) :
    Finset ((List ℕ × List ℕ) × List ℕ) :=
  ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u).product
    (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v)).product
    (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w)

/-- The one and only complete physical product. -/
def tripleFullProduct (m : ℕ)
    (x : (List ℕ × List ℕ) × List ℕ) : ℕ :=
  x.1.1.prod * x.1.2.prod * x.2.prod * m

/-- A complete-product fibre coefficient, with exact three-box
multiplicity and literal ordered HB positional mass. W is arbitrary
in all original slots, so merging fibres does NOT assume W=f(B). -/
def actualHBFullProductCoeff
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (B : ℕ) : ℂ :=
  ∑ x ∈ (actualHBTriples N τ u v w).filter
      (fun x => tripleFullProduct m x = B),
    hbPositionalMass m j z y W x.1.1 x.1.2 x.2

/-- Genuine same-signed-rho complete physical response, now indexed by
the FULL integer B (not the residual m or one of its three prime words).
This creates the actual single-variable coefficient ledger needed by the
shifted-divisor moment, preserving noninjective product fibres exactly. -/
theorem actualThreeHB_sameRho_regroup_by_complete_product
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      threeWholeHBAtQ N m j q τ z y u v w W) =
    ∑ B ∈ (actualHBTriples N τ u v w).image (tripleFullProduct m),
      actualHBFullProductCoeff N m j τ z y u v w W B *
        (∑ q ∈ Q, (rho q : ℂ) *
          (((fineKernel N q B : ℝ) : ℂ))) := by
  rw [threeWholeHB_sameRho_fixed]
  simpa [actualHBFullProductCoeff, actualHBTriples, tripleFullProduct,
    sameRhoFixedProductResponse, Finset.sum_product] using
    (weighted_sum_by_full_product_fibre
      (actualHBTriples N τ u v w) (tripleFullProduct m)
      (fun x => hbPositionalMass m j z y W x.1.1 x.1.2 x.2)
      (fun B => ∑ q ∈ Q, (rho q : ℂ) *
        (((fineKernel N q B : ℝ) : ℂ)))).symm

/-- Uniformly for arbitrary physical positional geometry W, merging
repeated complete products costs no extra L1 factor. This is a genuine
finite bound, NOT the as-yet-unproved near-linear shifted moment. -/
theorem actualHBFullProductCoeff_l1_le
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) :
    (∑ B ∈ (actualHBTriples N τ u v w).image (tripleFullProduct m),
      ‖actualHBFullProductCoeff N m j τ z y u v w W B‖) ≤
    ∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
      ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
        ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
          ‖hbPositionalMass m j z y W a b d‖ := by
  simpa [actualHBFullProductCoeff, actualHBTriples, tripleFullProduct,
    Finset.sum_product] using
    (full_product_fibre_l1_le
      (actualHBTriples N τ u v w) (tripleFullProduct m)
      (fun x => hbPositionalMass m j z y W x.1.1 x.1.2 x.2))

end
end ImbalancedChen.P3ActualWholeProductFibreLedger
