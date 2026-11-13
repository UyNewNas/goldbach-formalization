import ImbalancedChen.Part3OriginalWeightedPetersson
import ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov

noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicWeightSum20261112
open Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open OriginalPositiveStrip20261112 (residual)
open OriginalOppositeMarkedKuznetsov20261112 (modulusTerm)
open OriginalSignedTraceInput20261102 (traceModulus)
open OriginalPeterssonNormalizedOrbits20261112 (modulus)
open OriginalPeterssonLipschitz20261112 (argument)
open OriginalPositivePeterssonTrace20261112 (coincidence)
open OriginalHolomorphicProjectionPrices20261112

def oddProjection (ell : D4→ℤ) (Y q : ℝ) : ℂ := spectralTest ell Y q-residual ell Y q

def holSpectrum (z p b : ℕ) [NeZero z] (Φ : ℝ→ℂ) : ℂ :=
  ∑' j : ℕ,∑ i,basisTerm z p b Φ j i

theorem physical_modulus (z p h : ℕ) (ell : D4→ℤ) (Y : ℝ) (d : ℕ+) :
    modulusTerm (oddProjection ell Y) z p (h:ℤ) d=projectedRow z p h ell Y d := by
  by_cases good : z.Coprime (d:ℕ)
  · have qE : 4*Real.pi*Real.sqrt ((p:ℝ)*(h:ℝ))/traceModulus z d=qMark z p h d := by
      rw [Real.sqrt_mul (Nat.cast_nonneg p)];dsimp [qMark,argument,modulus,traceModulus];ring
    simp only [modulusTerm,projectedRow,arithmetic,dif_pos good,oddProjection,Int.natAbs_natCast,qE] <;> rfl
  · simp [modulusTerm,projectedRow,arithmetic,good]

/-- The exact positive integer mark at the physical modulus, with the original phase
and both collision tests in the same form as the scalar remainder. -/
theorem positive_mark_holomorphic (z p : ℕ) [NeZero z] {b : ℤ} (hp : 0<p)
    (hb : 0<b) (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun d : ℕ+ => ‖modulusTerm (oddProjection ell Y) z p b d‖) ∧
    (∑' d : ℕ+,modulusTerm (oddProjection ell Y) z p b d)=
      holSpectrum z p b.natAbs (spectralTest ell Y)+
        (if z=1 ∧ (p:ℤ)=b then diagonalMoment 0 (spectralTest ell Y)/(2*(Real.pi:ℂ)) else 0) := by
  lift b to ℕ using hb.le
  have hh : 0<b := by exact_mod_cast hb
  have E := weighted_petersson z p b hp hh ell hY
  simp only [Int.natAbs_natCast]
  simp_rw [physical_modulus]
  refine ⟨E.2.1,E.2.2.2.trans ?_⟩
  congr 1
  by_cases c : z=1 ∧ p=b
  · simp [diagonalTerm,coincidence,c,c.1,c.2]
  · have nc : ¬(z=1 ∧ (p:ℤ)=(b:ℤ)) := by simpa only [Int.natCast_inj] using c
    simp [diagonalTerm,coincidence,c,nc]

end ImbalancedChen.Part3.OriginalHolomorphicWeightSum20261112
end
