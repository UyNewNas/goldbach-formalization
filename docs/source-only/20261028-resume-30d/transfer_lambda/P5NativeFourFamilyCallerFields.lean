import ImbalancedChen.P5ActualSelectedAtomSmoothCaller
import ImbalancedChen.P5NativeSelectedFourOrderedEuler

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
All the fixed-rank FOUR fields below concern the actual native profile.
The arbitrary-rank Family bank still needs its other independently proved
rank components. No zero-padding is used to claim their coverage.
-/
namespace ImbalancedChen.P5Z.NativeFourFamilyCallerFields

noncomputable section
open Classical
open U11Integral U1011OriginalFifteenNativeGridCells
open NativeSelectedFourIntegerProfile NativeSelectedFourOrderedEuler
open ActualSelectedAtomSmoothCaller
open AdmissibleAllRankIntegerGeometricFamily
open IndependentSmoothWPhysicalChartInterface
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler

-- There is no free ambient/W field in this witness: every assertion is
-- about the independently fixed native Data and its actual profile.
structure NativeFourFamily (D : Data) (side : Bool) : Prop where
  smooth : ∀ N : ℕ, ContDiff ℝ ∞ (profile D side N)
  exponent_pos : 0 < (lower : ℝ) - D.width
  support : ∀ (N : ℕ) (p : Fin 4 → ℝ), profile D side N p ≠ 0 →
    (∀ i, (N : ℝ)^((lower : ℝ)-D.width) ≤ p i) ∧ (∏ i, p i) ≤ (N : ℝ)
  finitePrimeSupport : ∀ N : ℕ,
    Set.Finite {u : Fin 4 → ℕ |
      (∀ i, (u i).Prime) ∧ integerWeight D side N u ≠ 0}
  mixedEuler : ∀ r : ℕ, ∃ C B : ℕ, 0 < C ∧
    ∀ (N : ℕ) (w : List (Fin 4)) (p : Fin 4 → ℝ), w.length ≤ r →
      |eulerWord w (profile D side N) p| ≤
        (C : ℝ) * (Real.log ((N : ℝ)+2))^B

theorem nativeFourFamily (D : Data) (side : Bool) : NativeFourFamily D side := by
  constructor
  · exact profile_global_smooth D side
  · exact NativeSelectedFourIntegerProfile.exponent_pos D
  · intro N p hp
    have hs := profile_support D side hp
    exact ⟨fun i => (hs.2.1 i).le, hs.2.2⟩
  · exact finite_prime_support D side
  · intro r
    obtain ⟨C, hC, hb⟩ := native_mixedEuler D r
    refine ⟨C, 0, hC, ?_⟩
    intro N w p hw
    simpa only [pow_zero, mul_one] using hb side N w p hw

-- The smooth-test fields and the ORIGINAL sharp selected caller refer
-- to the SAME frozen state/owner/mask data. The equality is an exact
-- remainder decomposition; actual wall payment is still visible.
theorem actual_selected_atom_native_family_receiver (D : Data) :
    (∀ side : Bool, NativeFourFamily D side) ∧
      ∃ C : ℕ, 0 < C ∧ ∀ (side : Bool) (n N : ℕ), 2 ≤ N →
        ∀ (eta : ℚ) (w B : ℝ) (E : ℕ × ℕ → Prop),
          |actualSmoothSignedRows n N eta w B E (sharpSelectedWeight D N) -
            actualSmoothSignedRows n N eta w B E (primeWeight D side N)| ≤
            (1+(C : ℝ)) * reservePayment D side N (jointSupport n N eta w E)
              (jointPresievedSigma n N eta w B E) := by
  exact ⟨nativeFourFamily D, native_selected_actual_rows_wall_payment D⟩

end
end ImbalancedChen.P5Z.NativeFourFamilyCallerFields
