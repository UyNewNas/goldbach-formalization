import ImbalancedChen.Part3OriginalKloostermanOperatorL2
import ImbalancedChen.Part3FiniteKloostermanSourceCoefficients
import ImbalancedChen.Part3ComplexDispersion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Separable bilinear q^2 L2 bound for the literal original Kloosterman sum.
The physical packet application below has a PROVED rank-one coefficient:
its input is literally a Cartesian product, separate m/y weights and a
fixed physical z. All residue collisions and the original Fourier
amplitude remain in the two pushforwards. No arbitrary sourceCoefficient
matrix, original M2 packet or retained masked-W source is declared rank1.
This is a finite analytic primitive; full long-modulus 7/32 remains OPEN.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteOperator20261026b
noncomputable section
open Classical Finset FiniteSource20261026b
open scoped BigOperators

def separableBilinear (q : ℕ) [NeZero q] (A B : ZMod q → ℂ) : ℂ :=
  ∑ a : ZMod q, ∑ n : ZMod q,
    A a * B n * kloosterman q (a.val : ℤ) (n.val : ℤ)

theorem separableBilinear_eq_operator_pairing (q : ℕ) [NeZero q]
    (A B : ZMod q → ℂ) :
    separableBilinear q A B = ∑ a : ZMod q, A a * originalOperator q B a := by
  unfold separableBilinear originalOperator
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Compared with arbitrary-matrix Frobenius, the factor phi(q) is saved.
The hypothesis is an ACTUAL separable coefficient, not a claim that all
source coefficient matrices factor. -/
theorem separableBilinear_norm_sq_le (q : ℕ) [NeZero q] (A B : ZMod q → ℂ) :
    ‖separableBilinear q A B‖^2 ≤ (q : ℝ)^2 * (energy q A * energy q B) := by
  rw [separableBilinear_eq_operator_pairing]
  have hcs := ImbalancedChen.Part3.complex_finset_cauchy_norm_sq Finset.univ A (originalOperator q B)
  change ‖∑ a : ZMod q, A a*originalOperator q B a‖^2 ≤
    energy q A*energy q (originalOperator q B) at hcs
  calc
    _ ≤ energy q A*energy q (originalOperator q B) := hcs
    _ ≤ energy q A*((q : ℝ)^2*energy q B) :=
      mul_le_mul_of_nonneg_left (originalOperator_energy_le q B)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = (q : ℝ)^2*(energy q A*energy q B) := by ring

def separablePhysicalPacket (q : ℕ) [NeZero q] (M Y : Finset ℤ)
    (alpha beta : ℤ → ℂ) (B : ℝ) (a z : ℤ) : ℂ :=
  ∑ m ∈ M, ∑ y ∈ Y, alpha m * beta y * frequency B q a y z m

def packetLeftCoefficient (q : ℕ) [NeZero q] (M : Finset ℤ)
    (alpha : ℤ → ℂ) (B : ℝ) (z : ℤ) (u : ZMod q) : ℂ :=
  ∑ m ∈ M, if ((m*inverseResidue q z : ℤ) : ZMod q) = u then
    alpha m * frequencyAmplitude B q m else 0

def packetRightCoefficient (q : ℕ) [NeZero q] (Y : Finset ℤ)
    (beta : ℤ → ℂ) (a : ℤ) (v : ZMod q) : ℂ :=
  ∑ y ∈ Y, if ((a*y : ℤ) : ZMod q) = v then beta y else 0

/-- The rank-one property is DERIVED from this literal source packet.
No scalar is divided by a Fourier amplitude, and zeros cause no problem. -/
theorem separablePhysicalPacket_sourceCoefficient (q : ℕ) [NeZero q]
    (M Y : Finset ℤ) (alpha beta : ℤ → ℂ) (B : ℝ) (a z : ℤ)
    (u v : ZMod q) :
    sourceCoefficient (M ×ˢ Y) (fun t => alpha t.1*beta t.2) B q a
      (fun t => t.2) (fun _ => z) (fun t => t.1) (u,v) =
      packetLeftCoefficient q M alpha B z u * packetRightCoefficient q Y beta a v := by
  unfold sourceCoefficient packetLeftCoefficient packetRightCoefficient
  simp only [Finset.sum_product,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hu : ((m*inverseResidue q z : ℤ) : ZMod q) = u <;>
    by_cases hv : ((a*y : ℤ) : ZMod q) = v <;> simp [hu,hv] <;> ring

theorem separablePhysicalPacket_eq_separableBilinear (q : ℕ) [NeZero q]
    (M Y : Finset ℤ) (alpha beta : ℤ → ℂ) (B : ℝ) (a z : ℤ) :
    separablePhysicalPacket q M Y alpha beta B a z =
      separableBilinear q (packetLeftCoefficient q M alpha B z)
        (packetRightCoefficient q Y beta a) := by
  calc
    _ = finiteFrequencySource (M ×ˢ Y) (fun t => alpha t.1*beta t.2) B q a
        (fun t => t.2) (fun _ => z) (fun t => t.1) := by
      simp only [separablePhysicalPacket,finiteFrequencySource,Finset.sum_product]
    _ = ∑ r : ZMod q × ZMod q,
        sourceCoefficient (M ×ˢ Y) (fun t => alpha t.1*beta t.2) B q a
          (fun t => t.2) (fun _ => z) (fun t => t.1) r *
            kloosterman q (r.1.val : ℤ) (r.2.val : ℤ) := sourceCoefficient_pairing _ _ B q a _ _ _
    _ = separableBilinear q (packetLeftCoefficient q M alpha B z)
        (packetRightCoefficient q Y beta a) := by
      rw [Fintype.sum_prod_type]
      simp_rw [separablePhysicalPacket_sourceCoefficient]
      rfl

/-- Genuine physical finite separable source bound, including both
collision energies and the actual original inverse-z frequency twist. -/
theorem separablePhysicalPacket_norm_sq_le (q : ℕ) [NeZero q]
    (M Y : Finset ℤ) (alpha beta : ℤ → ℂ) (B : ℝ) (a z : ℤ) :
    ‖separablePhysicalPacket q M Y alpha beta B a z‖^2 ≤ (q : ℝ)^2 *
      (energy q (packetLeftCoefficient q M alpha B z) *
        energy q (packetRightCoefficient q Y beta a)) := by
  rw [separablePhysicalPacket_eq_separableBilinear]
  exact separableBilinear_norm_sq_le q _ _

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteOperator20261026b
