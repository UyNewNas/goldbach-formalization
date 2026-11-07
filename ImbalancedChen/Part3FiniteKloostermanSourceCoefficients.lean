import ImbalancedChen.Part3CoprimeKloostermanCRT
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Finite source coefficients for the literal physical Poisson summand. The
original signed a,y,z,m, physical B and finite carrier are unchanged. In
particular the inverse-z twist is inside the linear residue coordinate.
Both complex Fourier amplitude and original coefficient are pushed forward,
before taking a norm. Gcd strata include the zero linear residue. CRT uses
the actual inverse twists on BOTH local frequencies.

This is finite algebra, not the spectral 7/32 estimate, not an infinite-tail
payment, and not an assertion that a new independent beta can replace the
actual lambda/omega coefficients. All original N/rho/range restrictions can
be retained in the input carrier and weight without changing this identity.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteSource20261026b

noncomputable section
open Classical Finset CommonSmoothCutoff
open scoped BigOperators SchwartzMap FourierTransform

variable {ι : Type*}

def frequencyAmplitude (B : ℝ) (c : ℕ) (m : ℤ) : ℂ :=
  (B / (c : ℝ)) • (𝓕 dyadicCutoffSchwartz) ((B / (c : ℝ)) * (m : ℝ))

def finiteFrequencySource (I : Finset ι) (w : ι → ℂ) (B : ℝ) (c : ℕ)
    (a : ℤ) (y z m : ι → ℤ) : ℂ :=
  ∑ i ∈ I, w i * frequency B c a (y i) (z i) (m i)

/-- Signed pushforward onto the TWO actual frequency residues. -/
def sourceCoefficient (I : Finset ι) (w : ι → ℂ) (B : ℝ) (c : ℕ)
    (a : ℤ) (y z m : ι → ℤ) (r : ZMod c × ZMod c) : ℂ :=
  ∑ i ∈ I,
    if ((m i * inverseResidue c (z i) : ℤ) : ZMod c) = r.1 ∧
        ((a * y i : ℤ) : ZMod c) = r.2 then
      w i * frequencyAmplitude B c (m i) else 0

/-- Equality of residues is the only periodicity input. -/
theorem kloosterman_eq_of_cast_eq (c : ℕ) [NeZero c]
    {m n m' n' : ℤ} (hm : (m : ZMod c) = (m' : ZMod c))
    (hn : (n : ZMod c) = (n' : ZMod c)) :
    kloosterman c m n = kloosterman c m' n' := by
  simp only [Physical.kloosterman_eq_zmod, hm, hn]

theorem sourceCoefficient_pairing (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (c : ℕ) [NeZero c] (a : ℤ) (y z m : ι → ℤ) :
    finiteFrequencySource I w B c a y z m =
      ∑ r : ZMod c × ZMod c, sourceCoefficient I w B c a y z m r *
        kloosterman c (r.1.val : ℤ) (r.2.val : ℤ) := by
  unfold sourceCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold finiteFrequencySource
  apply Finset.sum_congr rfl
  intro i hi
  let r0 : ZMod c × ZMod c :=
    (((m i * inverseResidue c (z i) : ℤ) : ZMod c), ((a * y i : ℤ) : ZMod c))
  have hgate (r : ZMod c × ZMod c) :
      (((m i * inverseResidue c (z i) : ℤ) : ZMod c) = r.1 ∧
        ((a * y i : ℤ) : ZMod c) = r.2) ↔ r = r0 := by
    constructor
    · rintro ⟨h1,h2⟩
      exact Prod.ext h1.symm h2.symm
    · intro hr
      subst r
      exact ⟨rfl,rfl⟩
  simp_rw [hgate, ite_mul, zero_mul]
  rw [Finset.sum_eq_single r0]
  · simp only [if_pos rfl]
    have hK : kloosterman c (r0.1.val : ℤ) (r0.2.val : ℤ) =
        kloosterman c (m i * inverseResidue c (z i)) (a * y i) := by
      apply kloosterman_eq_of_cast_eq c
      · simp [r0]
      · simp [r0]
    rw [hK]
    simp only [frequency, frequencyAmplitude]
    ring
  · intro r hr hne
    exact if_neg hne
  · simp

/-- Unique exact gcd splitting, with no use of divisors of a zero shift.
The divisor set is that of the positive physical modulus c. -/
theorem sourceCoefficient_gcd_split (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (c : ℕ) [NeZero c] (a : ℤ) (y z m : ι → ℤ) :
    finiteFrequencySource I w B c a y z m =
      ∑ d ∈ c.divisors, ∑ r : ZMod c × ZMod c,
        if c.gcd r.1.val = d then
          sourceCoefficient I w B c a y z m r *
            kloosterman c (r.1.val : ℤ) (r.2.val : ℤ) else 0 := by
  rw [sourceCoefficient_pairing, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hd : c.gcd r.1.val ∈ c.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne c⟩
  rw [Finset.sum_eq_single (c.gcd r.1.val)]
  · simp
  · intro d hd' hne
    exact if_neg (Ne.symm hne)
  · exact fun hnot => (hnot hd).elim

/-- A fixed original y fibre needs only one complete-frequency moment. -/
def linearSourceCoefficient (I : Finset ι) (w : ι → ℂ) (B : ℝ) (c : ℕ)
    (z m : ι → ℤ) (r : ZMod c) : ℂ :=
  ∑ i ∈ I, if ((m i * inverseResidue c (z i) : ℤ) : ZMod c) = r then
    w i * frequencyAmplitude B c (m i) else 0

theorem fixedRightSource_pairing (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (c : ℕ) [NeZero c] (a y0 : ℤ) (z m : ι → ℤ) :
    finiteFrequencySource I w B c a (fun _ => y0) z m =
      ∑ r : ZMod c, linearSourceCoefficient I w B c z m r *
        kloosterman c (r.val : ℤ) (a*y0) := by
  unfold linearSourceCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold finiteFrequencySource
  apply Finset.sum_congr rfl
  intro i hi
  let r0 : ZMod c := ((m i * inverseResidue c (z i) : ℤ) : ZMod c)
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_eq_single r0]
  · simp only [if_pos rfl]
    have hK : kloosterman c (r0.val : ℤ) (a*y0) =
        kloosterman c (m i * inverseResidue c (z i)) (a*y0) := by
      apply kloosterman_eq_of_cast_eq c
      · simp [r0]
      · rfl
    rw [hK]
    simp only [frequency, frequencyAmplitude]
    ring
  · intro r hr hne
    exact if_neg (Ne.symm hne)
  · simp

/-- Exact CRT decomposition of the original finite source. No coefficients
are replaced by independent local coefficients, and B/(q*r) stays literal. -/
theorem finiteFrequencySource_coprime_crt (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (q r : ℕ) [NeZero q] [NeZero r] (hqr : q.Coprime r)
    (a : ℤ) (y z m : ι → ℤ) :
    finiteFrequencySource I w B (q*r) a y z m =
      ∑ i ∈ I, (w i * frequencyAmplitude B (q*r) (m i)) *
        (kloosterman q
          (Nat.gcdB q r * (m i * inverseResidue (q*r) (z i)))
          (Nat.gcdB q r * (a * y i)) *
         kloosterman r
          (Nat.gcdA q r * (m i * inverseResidue (q*r) (z i)))
          (Nat.gcdA q r * (a * y i))) := by
  unfold finiteFrequencySource frequency
  apply Finset.sum_congr rfl
  intro i hi
  rw [CoprimeCRTSourceOnly.kloosterman_coprime_crt hqr]
  simp only [frequencyAmplitude]
  ring

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteSource20261026b
