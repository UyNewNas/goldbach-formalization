import ImbalancedChen.Part3FiniteKloostermanSourceCauchy
import ImbalancedChen.Part3ActualReciprocalSquarePoisson

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual finite completed-square consumer, on a fixed physical c,f fibre of
`ActualReciprocalSquarePoissonSourceOnly.completedPiece`. M,N are exactly
the two physical smooth scales. T,H,lambda,omega and signed a,f retain
their original meanings, and both original unit gates survive. K is an
arbitrary finite set of completed integer frequencies: it can be the
original truncated common interval or its nonzero subset, without a
replacement by complete residues. Residue collisions are charged.

The source equality and bound below are unconditional finite results.
They do not prove the truncation error, coefficient collision energy
saving, summation over physical c,f, or the spectral 7/32 return. Those
remain OPEN. In particular no hNonzero/hKuz assumption is introduced.
-/

namespace ImbalancedChen.Part3.ActualSmallGcdFiniteKloosterman20261026b

noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.FiniteSource20261026b
open ActualReciprocalSquarePoissonSourceOnly
open scoped BigOperators

abbrev SourceIndex := (Inner × Inner) × ℤ

def actualSourceCarrier (T : Finset ℕ) (H : ℕ) (K : Finset ℤ) : Finset SourceIndex :=
  (finiteInnerCarrier T H ×ˢ finiteInnerCarrier T H) ×ˢ K

def actualSourceWeight (A c : ℕ) (a : ℤ) (N : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (i : SourceIndex) : ℂ :=
  if fixedUnit A a i.1.1.1 ∧ fixedUnit A a i.1.2.1 ∧
      c.Coprime (level i.1.1 i.1.2) then
    (scaledDyadicCutoff N c : ℂ) *
      (atomCoeff lambda omega i.1.1 * star (atomCoeff lambda omega i.1.2))
  else 0

def actualY (f : ℤ) (i : SourceIndex) : ℤ := outputY f i.1.1 i.1.2
def actualZ (i : SourceIndex) : ℤ := (level i.1.1 i.1.2 : ℤ)
def actualM (i : SourceIndex) : ℤ := i.2

/-- Literal finite restriction of the completed square, before any norm. -/
def actualFiniteCompletedFibre (A c : ℕ) (a f : ℤ)
    (T : Finset ℕ) (H : ℕ) (K : Finset ℤ) (lambda : ℕ → ℂ)
    (omega : ℤ → ℂ) (M N : ℝ) : ℂ :=
  (scaledDyadicCutoff N c : ℂ) *
    ∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
      if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
        (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
          ∑ m ∈ K, frequency M c a (outputY f u v) (level u v : ℤ) m
      else 0

/-- The coefficient is determined by the original common lambda/omega;
there is no freedom to prescribe it independently on the output residues. -/
def actualSourceCoefficient (A c : ℕ) (a f : ℤ)
    (T : Finset ℕ) (H : ℕ) (K : Finset ℤ) (lambda : ℕ → ℂ)
    (omega : ℤ → ℂ) (M N : ℝ) (r : ZMod c × ZMod c) : ℂ :=
  sourceCoefficient (actualSourceCarrier T H K)
    (actualSourceWeight A c a N lambda omega) M c a
    (actualY f) actualZ actualM r

theorem actualFiniteCompletedFibre_eq_source (A c : ℕ) (a f : ℤ)
    (T : Finset ℕ) (H : ℕ) (K : Finset ℤ) (lambda : ℕ → ℂ)
    (omega : ℤ → ℂ) (M N : ℝ) :
    actualFiniteCompletedFibre A c a f T H K lambda omega M N =
      finiteFrequencySource (actualSourceCarrier T H K)
        (actualSourceWeight A c a N lambda omega) M c a
        (actualY f) actualZ actualM := by
  unfold actualFiniteCompletedFibre finiteFrequencySource actualSourceCarrier
  simp only [Finset.sum_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hg : fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v)
  · simp only [hg, if_true, Finset.mul_sum, actualSourceWeight,
      actualY, actualZ, actualM]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  · simp [actualSourceWeight, hg]

theorem actualFiniteCompletedFibre_residue_pairing (A c : ℕ) [NeZero c] (a f : ℤ)
    (T : Finset ℕ) (H : ℕ) (K : Finset ℤ) (lambda : ℕ → ℂ)
    (omega : ℤ → ℂ) (M N : ℝ) :
    actualFiniteCompletedFibre A c a f T H K lambda omega M N =
      ∑ r : ZMod c × ZMod c,
        actualSourceCoefficient A c a f T H K lambda omega M N r *
          kloosterman c (r.1.val : ℤ) (r.2.val : ℤ) := by
  rw [actualFiniteCompletedFibre_eq_source, sourceCoefficient_pairing]
  rfl

/-- The exact physical-modulus gcd split also applies to the actual
source; the zero residue belongs to the d=c stratum. -/
theorem actualFiniteCompletedFibre_gcd_split (A c : ℕ) [NeZero c] (a f : ℤ)
    (T : Finset ℕ) (H : ℕ) (K : Finset ℤ) (lambda : ℕ → ℂ)
    (omega : ℤ → ℂ) (M N : ℝ) :
    actualFiniteCompletedFibre A c a f T H K lambda omega M N =
      ∑ d ∈ c.divisors, ∑ r : ZMod c × ZMod c,
        if c.gcd r.1.val = d then
          actualSourceCoefficient A c a f T H K lambda omega M N r *
            kloosterman c (r.1.val : ℤ) (r.2.val : ℤ) else 0 := by
  rw [actualFiniteCompletedFibre_eq_source]
  exact sourceCoefficient_gcd_split _ _ M c a _ _ _

/-- A genuine bound on each original physical c,f finite subfamily. The
constant is the true TWO-frequency complete moment c^2*phi(c). -/
theorem actualFiniteCompletedFibre_norm_sq_le (A c : ℕ) [NeZero c] (a f : ℤ)
    (T : Finset ℕ) (H : ℕ) (K : Finset ℤ) (lambda : ℕ → ℂ)
    (omega : ℤ → ℂ) (M N : ℝ) :
    ‖actualFiniteCompletedFibre A c a f T H K lambda omega M N‖ ^ 2 ≤
      ((c : ℝ)^2 * (Nat.totient c : ℝ)) *
        ∑ r : ZMod c × ZMod c,
          ‖actualSourceCoefficient A c a f T H K lambda omega M N r‖ ^ 2 := by
  rw [actualFiniteCompletedFibre_eq_source]
  exact finiteFrequencySource_norm_sq_le _ _ M c a _ _ _

/-- For a fixed original inner pair, y is fixed and the sharper true
one-frequency complete moment applies. K may be any retained nonzero
frequency window; its signed Fourier amplitudes remain in the coefficient. -/
theorem actualFixedInnerPair_norm_sq_le (A c : ℕ) [NeZero c] (a f : ℤ)
    (u v : Inner) (K : Finset ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N : ℝ) :
    ‖∑ m ∈ K,
        actualSourceWeight A c a N lambda omega ((u,v),m) *
          frequency M c a (outputY f u v) (level u v : ℤ) m‖ ^ 2 ≤
      ((c : ℝ) * (Nat.totient c : ℝ)) *
        ∑ r : ZMod c,
          ‖linearSourceCoefficient K
            (fun m => actualSourceWeight A c a N lambda omega ((u,v),m))
            M c (fun _ => (level u v : ℤ)) (fun m => m) r‖ ^ 2 := by
  exact finiteFixedRightSource_norm_sq_le K
    (fun m => actualSourceWeight A c a N lambda omega ((u,v),m))
    M c a (outputY f u v) (fun _ => (level u v : ℤ)) (fun m => m)

/-- A proved boundary subfamily, with NO assumed coefficient-energy bound:
for one original inner pair, take any retained frequencies sampled at most
once in 0 <= m < c. The actual original unit gate licenses inverse-z
injectivity. Removing zero from J gives the nonzero subfamily directly.
This is not the full spectral estimate on the longer original m window. -/
theorem actualFixedInnerPair_residueWindow_norm_sq_le
    (A c : ℕ) [NeZero c] (a f : ℤ) (u v : Inner)
    (hcop : c.Coprime (level u v)) (J : Finset (ZMod c))
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) :
    ‖∑ r ∈ J,
        actualSourceWeight A c a N lambda omega ((u,v),(r.val : ℤ)) *
          frequency M c a (outputY f u v) (level u v : ℤ) (r.val : ℤ)‖ ^ 2 ≤
      ((c : ℝ) * (Nat.totient c : ℝ)) *
        ∑ r ∈ J,
          ‖actualSourceWeight A c a N lambda omega ((u,v),(r.val : ℤ)) *
            frequencyAmplitude M c (r.val : ℤ)‖ ^ 2 := by
  have hz : IsUnit (level u v : ZMod c) :=
    (ZMod.isUnit_iff_coprime (level u v) c).mpr hcop.symm
  have hinj : Function.Injective (fun r : ZMod c =>
      (((r.val : ℤ) * inverseResidue c (level u v : ℤ) : ℤ) : ZMod c)) := by
    intro r s heq
    have heq' : r * (level u v : ZMod c)⁻¹ = s * (level u v : ZMod c)⁻¹ := by
      simpa only [Int.cast_mul, inverseResidue, Int.cast_natCast,
        ZMod.natCast_zmod_val] using heq
    have hm := congrArg (fun t : ZMod c => t * (level u v : ZMod c)) heq'
    simpa only [mul_assoc, ZMod.inv_mul_of_unit _ hz, mul_one] using hm
  exact finiteFixedRightSource_norm_sq_le_of_injOn J
    (fun r => actualSourceWeight A c a N lambda omega ((u,v),(r.val : ℤ)))
    M c a (outputY f u v) (fun _ => (level u v : ℤ))
    (fun r => (r.val : ℤ)) hinj.injOn

end
end ImbalancedChen.Part3.ActualSmallGcdFiniteKloosterman20261026b
