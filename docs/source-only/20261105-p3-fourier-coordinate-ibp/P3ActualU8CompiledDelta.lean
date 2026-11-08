import ImbalancedChen.P3ActualU8CommonCarrierPP
import ImbalancedChen.P3ActualU8UnitPhysicalNorm
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Exact *coefficient perturbation* for the actual U8 sharp-K rank-three
labelled PP on ONE common physical carrier. The compiler-side input is
an arbitrary explicitly INTEGER-valued rough coefficient; this is NOT
an identification of the manuscript's final causal rho_T with an
existing producer. It is mapped through the original small Rosser
attachment, NOT substituted directly for a physical coefficient.

The complete signed discrepancy retains the original ordered labels,
the p2=q wall, the exact coprime mean, and full physical moduli.
No smallness of the compiler-minus-raw difference is assumed or proved.
-/

namespace ImbalancedChen.P3ActualU8CompiledDelta

noncomputable section
open scoped BigOperators
open Classical

private def commonQ (N cap : ℕ) (w : ℝ) (rough : Finset ℕ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) rough

private def rawCommonRho (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) rough
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

private def integerCompiledRho (N cap : ℕ) (w L : ℝ)
    (rough : Finset ℕ) (compiled : ℕ → ℤ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) rough
    (fun d => (compiled d : ℝ))
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

/-- Every physical modulus on the common product carrier is positive
when each added rough factor is a genuine nonzero rough product.
No assumption is made that a compiler-only modulus has legal level. -/
theorem commonQ_positive (N cap : ℕ) (w : ℝ) (rough : Finset ℕ)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d) :
    ∀ q ∈ commonQ N cap w rough, 0 < q := by
  intro q hq
  unfold commonQ smallRoughModuli smallRoughPairs at hq
  rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
  rcases Finset.mem_product.mp ha with ⟨hs, hr⟩
  have hs0 : a.1 ≠ 0 :=
    (actualSmallRosserSupport_squarefree N cap w hs).ne_zero
  have hr0 : a.2 ≠ 0 := (hrough a.2 hr).1
  exact Nat.mul_pos (Nat.pos_of_ne_zero hs0) (Nat.pos_of_ne_zero hr0)

/-- Coefficient linearity is applied to the REAL original sorted U8
family, before taking absolute values. All congruence and primitive
means use exactly the same physical modulus q and unchanged labels. -/
theorem actual_u8_signed_PP_difference (N : ℕ) (Q : Finset ℕ)
    (rhoCompiled rhoRaw : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N Q rhoCompiled
        (P5U8SharpKSource.physicalWeight N) =
      Part3.primeProductSignedError 3 N N Q rhoRaw
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError
        (P5U8SharpKSource.arithmeticTriples N)
        P5U8SharpKSource.product (fun _ => (1 : ℝ)) N Q
        (fun q => rhoCompiled q - rhoRaw q) := by
  calc
    _ = p5z_labelledDistributionError
          (P5U8SharpKSource.arithmeticTriples N)
          P5U8SharpKSource.product (fun _ => (1 : ℝ))
          N Q rhoCompiled :=
      (P5U8SharpKSource.distribution_eq_physicalPP N Q rhoCompiled).symm
    _ = p5z_labelledDistributionError
          (P5U8SharpKSource.arithmeticTriples N)
          P5U8SharpKSource.product (fun _ => (1 : ℝ))
          N Q rhoRaw +
        p5z_labelledDistributionError
          (P5U8SharpKSource.arithmeticTriples N)
          P5U8SharpKSource.product (fun _ => (1 : ℝ))
          N Q (fun q => rhoCompiled q - rhoRaw q) := by
      unfold p5z_labelledDistributionError
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      rw [P5U8SharpKSource.distribution_eq_physicalPP N Q rhoRaw]

/-- True integer rough candidates pass through the SAME small Rosser
attachment. The raw leg is then transported to its literal original
carrier, while the full compiled-minus-raw delta is charged on the
common physical carrier, including compiler-only moduli. -/
theorem actual_u8_integer_compiler_raw_delta
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough)
    (compiled : ℕ → ℤ) :
    Part3.primeProductSignedError 3 N N
        (commonQ N cap w rough)
        (integerCompiledRho N cap w L rough compiled)
        (P5U8SharpKSource.physicalWeight N) =
      Part3.primeProductSignedError 3 N N
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L)
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError
        (P5U8SharpKSource.arithmeticTriples N)
        P5U8SharpKSource.product (fun _ => (1 : ℝ)) N
        (commonQ N cap w rough)
        (fun q => integerCompiledRho N cap w L rough compiled q -
          rawCommonRho retainOdd N cap w z L rough q) := by
  have hdelta := actual_u8_signed_PP_difference N
    (commonQ N cap w rough)
    (integerCompiledRho N cap w L rough compiled)
    (rawCommonRho retainOdd N cap w z L rough)
  have hraw :
      Part3.primeProductSignedError 3 N N (commonQ N cap w rough)
          (rawCommonRho retainOdd N cap w z L rough)
          (P5U8SharpKSource.physicalWeight N) =
        Part3.primeProductSignedError 3 N N
          (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L)
          (P5U8SharpKSource.physicalWeight N) :=
    P3ActualU8CommonCarrierPP.actual_u8_rank3_PP_common_eq_raw
      retainOdd N cap w z L rough hcover
  rw [hraw] at hdelta
  exact hdelta

/-- A rigorous finite *criterion* for compiler coefficient payment,
NOT a claimed estimate on the real causal compiler: positive physical
carrier support and the true U8 original card, no relative-Theta demand. -/
theorem actual_u8_integer_compiler_delta_l1
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled : ℕ → ℤ) :
    |Part3.primeProductSignedError 3 N N
        (commonQ N cap w rough)
        (integerCompiledRho N cap w L rough compiled)
        (P5U8SharpKSource.physicalWeight N) -
      Part3.primeProductSignedError 3 N N
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L)
        (P5U8SharpKSource.physicalWeight N)| ≤
      ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        (∑ q ∈ commonQ N cap w rough,
          |integerCompiledRho N cap w L rough compiled q -
            rawCommonRho retainOdd N cap w z L rough q|) := by
  have hpoint := P3ActualU8UnitPhysicalNorm.labelled_unit_signed_error_le_l1
    (P5U8SharpKSource.arithmeticTriples N) P5U8SharpKSource.product
    N (commonQ N cap w rough)
    (fun q => integerCompiledRho N cap w L rough compiled q -
      rawCommonRho retainOdd N cap w z L rough q)
    (commonQ_positive N cap w rough hrough)
  have hEq := actual_u8_integer_compiler_raw_delta
    retainOdd N cap w z L rough hcover compiled
  calc
    _ = |p5z_labelledDistributionError
          (P5U8SharpKSource.arithmeticTriples N)
          P5U8SharpKSource.product (fun _ => (1 : ℝ))
          N (commonQ N cap w rough)
          (fun q => integerCompiledRho N cap w L rough compiled q -
            rawCommonRho retainOdd N cap w z L rough q)| := by
            rw [hEq]
            congr 1
            ring
    _ ≤ _ := hpoint

end

end ImbalancedChen.P3ActualU8CompiledDelta
