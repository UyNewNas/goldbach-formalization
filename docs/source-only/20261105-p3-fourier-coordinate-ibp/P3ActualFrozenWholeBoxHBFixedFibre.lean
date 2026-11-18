import ImbalancedChen.P3ActualFrozenWholeBoxHBOffshift
import ImbalancedChen.P3HBRoughLiteralMoment

/-!
P3.6: literal fixed-HB-product fibre of the actual THREE frozen prime boxes.

The original factorTuples k m has h.prod=m at EVERY occurrence.  Thus the
complete physical shift is N-(a.prod*b.prod*d.prod)*m, independent of the
ordered HB factorisation.  W(a,b,d,h) is NOT assumed product-dependent;
its positional sum stays inside an exact complex coefficient.  This gives
a genuine same-signed-rho physical response and an elementary tau^k
bound for its HB coefficient.  Neither a small shifted-divisor moment
nor full original PP compiler admission follows from this identity.

Frozen manuscript: chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§2,4 (F), manuscript-body.tex eq:current-PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenWholeBoxHBOffshift
open ImbalancedChen.P3ActualFrozenThreeWholeBoxHBTarget
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P3HBRoughLiteralMoment
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- The TRUE original HB coefficient at fixed product m.  It retains
every ordered occurrence, the literal per-slot mu/log/one weights, strict
rough projector and the full four-word positional geometry W. -/
def hbPositionalMass (m j : ℕ) (z y : ℝ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (a b d : List ℕ) : ℂ :=
  ∑ h ∈ factorTuples (2 * (j + 1)) m,
    W a b d h * roughTupleWeight z y (roles j) h

/-- Unlike a formal coefficient bound, this is derived from the genuine
literal ordered rough-HB mass.  The geometry bound A is an ordinary
pointwise hypothesis, NOT an analytic PP/discrepancy input. -/
theorem hbPositionalMass_norm_le_tau
    (m j : ℕ) (z y : ℝ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (a b d : List ℕ) (A : ℝ)
    (hm : m ≠ 0) (hz : 0 ≤ z) (hA : 0 ≤ A)
    (hW : ∀ h ∈ factorTuples (2 * (j + 1)) m,
      ‖W a b d h‖ ≤ A) :
    ‖hbPositionalMass m j z y W a b d‖ ≤
      A * (Real.log (m : ℝ) *
        ((m.divisors.card : ℝ) ^ (2 * (j + 1)))) := by
  calc
    ‖hbPositionalMass m j z y W a b d‖ ≤
      ∑ h ∈ factorTuples (2 * (j + 1)) m,
        ‖W a b d h * roughTupleWeight z y (roles j) h‖ := by
          unfold hbPositionalMass
          exact norm_sum_le _ _
    _ = ∑ h ∈ factorTuples (2 * (j + 1)) m,
          ‖W a b d h‖ * ‖roughTupleWeight z y (roles j) h‖ := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [norm_mul]
    _ ≤ ∑ h ∈ factorTuples (2 * (j + 1)) m,
          A * ‖roughTupleWeight z y (roles j) h‖ := by
          apply Finset.sum_le_sum
          intro h hh
          exact mul_le_mul_of_nonneg_right (hW h hh) (norm_nonneg _)
    _ = A * roughLiteralHBAbsMass z y j m := by
          simp only [roughLiteralHBAbsMass, Finset.mul_sum]
    _ ≤ A * (Real.log (m : ℝ) *
          ((m.divisors.card : ℝ) ^ (2 * (j + 1)))) :=
      mul_le_mul_of_nonneg_left
        (roughLiteralHBAbsMass_le_tau_pow hz y j m hm) hA

/-- Actual three-prime-word source with its ordered HB factorisation
already summed but with the COMPLETE physical product unchanged. -/
def threeWholeHBFixedAtQ (N m j q : ℕ) (τ z y : ℝ)
    (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) : ℂ :=
  let B := actualPrimeFineLabelFinset N τ
  ∑ a ∈ actualPrimeSlotBox B u,
    ∑ b ∈ actualPrimeSlotBox B v,
      ∑ d ∈ actualPrimeSlotBox B w,
        hbPositionalMass m j z y W a b d *
          (((fineKernel N q (a.prod * b.prod * d.prod * m) : ℝ) : ℂ))

/-- A substantive fibre collapse: the exact real physical modulus kernel
does not vary with the ORIGINAL positional HB factorisation, since the
literal factorTuples carrier has product m.  In particular no fake
mu(a.prod*b.prod*d.prod*m) is inserted in the HB coefficient. -/
theorem threeWholeHBAtQ_eq_fixed
    (N m j q : ℕ) (τ z y : ℝ)
    (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) :
    threeWholeHBAtQ N m j q τ z y u v w W =
      threeWholeHBFixedAtQ N m j q τ z y u v w W := by
  unfold threeWholeHBAtQ threeWholeHBFixedAtQ
  dsimp
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  unfold hbPositionalMass
  calc
    (∑ h ∈ factorTuples (2 * (j + 1)) m,
      (W a b d h * roughTupleWeight z y (roles j) h) *
        (((fineKernel N q (a.prod * b.prod * d.prod * h.prod) : ℝ) : ℂ))) =
      ∑ h ∈ factorTuples (2 * (j + 1)) m,
        (W a b d h * roughTupleWeight z y (roles j) h) *
          (((fineKernel N q (a.prod * b.prod * d.prod * m) : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [(factorTuples_spec (2 * (j + 1)) m h hh).2.1]
    _ = _ := by rw [Finset.sum_mul]

/-- Signed, full PHYSICAL modulus response for the actual complete
product r*m.  The identical integer rho occurs in count and coprime mean. -/
def sameRhoFixedProductResponse
    (N r m : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ) : ℂ :=
  ∑ q ∈ Q, (rho q : ℂ) *
    (((fineKernel N q (r * m) : ℝ) : ℂ))

/-- Pull the SAME signed physical q-sum through the actual HB factorisation
and all THREE independent original prime boxes.  No absolute values,
position sorting, value quotient, or premature triangle inequality.
This isolates a single full-product arithmetic response for each triple,
which is the actual next input to a shifted-divisor-moment calculation. -/
theorem threeWholeHB_sameRho_fixed
    (N m j : ℕ) (τ z y : ℝ)
    (u v w : List ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      threeWholeHBAtQ N m j q τ z y u v w W) =
      ∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
        ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
          ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
            hbPositionalMass m j z y W a b d *
              sameRhoFixedProductResponse N (a.prod * b.prod * d.prod)
                m Q rho := by
  have hfixed (q : ℕ) :
      threeWholeHBAtQ N m j q τ z y u v w W =
        threeWholeHBFixedAtQ N m j q τ z y u v w W :=
    threeWholeHBAtQ_eq_fixed N m j q τ z y u v w W
  calc
    _ = ∑ q ∈ Q, (rho q : ℂ) *
          threeWholeHBFixedAtQ N m j q τ z y u v w W := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [hfixed]
    _ = _ := by
      unfold threeWholeHBFixedAtQ
      dsimp
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      unfold sameRhoFixedProductResponse
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

end
end ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
