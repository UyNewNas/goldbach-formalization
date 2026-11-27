import ImbalancedChen.Part3ActualPositiveLatticeSmoothCore
import ImbalancedChen.Part3ActualCompletedSourceLanes

/-!
# Original smooth reciprocal squares and their completed pieces

Recover the finite-row and smooth-mass bridge from the original
Part3ActualReciprocalSquarePoisson, blob 58e9a86e0bd60aee30ebc7a15c781f2dd96a49c9.
The row, the unit gates, the signed h and f windows, and all three original
smooth-mass endpoint statements are retained. Every marked fragment is copied
verbatim except one invocation of the existing Poisson theorem.

The current Part3ActualReciprocalSquarePoissonCore already owns a generalized
reciprocal_square_b_poisson with an explicit finite b carrier. The single
adapted call below supplies the original Ioc carrier and full_b_support, then
rewrites reciprocalRow using the recovered finiteRow_eq_atoms. No second
Poisson proof or duplicate definition of completedPiece is installed.

The one-piece identity requires M > 0 and M <= 2 B; the six-piece identity
requires B > 0. Neither deletes the y = 0 contribution. This is the finite
smooth-square input to the 1106 manuscript's exact b-Poisson formula, lines
689-694. The OriginalData construction, common cutoff bounds, zero/tail
estimates and actual spectral inputs remain separate obligations.
-/

namespace ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly

noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.Physical ActualFixedFeaturePacketPushforwardSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open scoped BigOperators SchwartzMap FourierTransform
attribute [local instance] Classical.propDecidable

-- BEGIN recovered original_inner_gate
private theorem inner_gate_iff (A : ℕ) (a : ℤ) (c t : ℕ) :
    (t.Coprime (A*c) ∧ t.Coprime (a.natAbs*c)) ↔ fixedUnit A a t ∧ t.Coprime c := by
  simp only [Nat.coprime_mul_iff_right, fixedUnit]
  tauto
-- END recovered original_inner_gate

-- BEGIN recovered original_finite_row
def finiteReciprocalRow (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (k : Packet) : ℂ :=
  ∑ t ∈ T,
    if t.Coprime (A*k.1.2) ∧ t.Coprime (a.natAbs*k.1.2) then
      lambda t * ∑ h ∈ poissonNonzeroFrequencyWindow H,
        omega h * fourier (a*h*k.2)
          (((CanonicalReciprocalPhase.wPhaseInverse (k.1.1*t) k.1.2 : ℝ) /
            (k.1.2 : ℝ) : ℝ) : UnitAddCircle)
    else 0
-- END recovered original_finite_row

-- BEGIN recovered original_row_atoms
theorem finiteRow_eq_atoms (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (b c : ℕ) (f : ℤ) :
    finiteReciprocalRow A a T H lambda omega ((b,c),f) =
      ∑ u ∈ finiteInnerCarrier T H, atom A a f b c lambda omega u := by
  simp only [finiteReciprocalRow, finiteInnerCarrier, sum_product]
  apply sum_congr rfl
  intro t ht
  simp only [inner_gate_iff]
  by_cases hu : fixedUnit A a t ∧ t.Coprime c
  · simp only [if_pos hu, atom, atomCoeff, phase, mul_sum, mul_assoc]
  · simp only [if_neg hu, atom, sum_const_zero]
-- END recovered original_row_atoms

-- BEGIN recovered original_full_b_support
private theorem full_b_support {M B : ℝ} (_hM : 0 < M) (hMB : M ≤ 2*B)
    (b : ℕ) (hb : scaledDyadicCutoff M b ≠ 0) : b ∈ Ioc 0 (Nat.floor (5*B)) := by
  have hp : dyadicCutoffSchwartz ((b : ℝ)/M) ≠ 0 := by
    simpa only [scaledDyadicCutoff, dyadicCutoffSchwartz_apply, ne_eq, Complex.ofReal_eq_zero] using hb
  obtain ⟨_, hbp, _, hhi⟩ := physical_cutoff_nonzero_nat_modulus hp
  exact mem_Ioc.mpr ⟨hbp, Nat.le_floor (by linarith)⟩
-- END recovered original_full_b_support

-- BEGIN recovered original_smooth_mass_gated_squares
theorem smoothMass_eq_gated_squares (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    (smoothMass M N (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
      ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
        if f ≠ 0 then (scaledDyadicCutoff N c : ℂ) *
          (∑ b ∈ Ioc 0 (Nat.floor (5*B)), (scaledDyadicCutoff M b : ℂ) *
            (if b.Coprime c then
              ((‖finiteReciprocalRow A a T H lambda omega ((b,c),f)‖^2 : ℝ) : ℂ) else 0)) else 0 := by
  rw [smoothMass_lattice]
  simp only [Complex.ofReal_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · rw [if_pos hfn, mul_sum]
    apply sum_congr rfl
    intro b hb
    by_cases hbc : b.Coprime c
    · have hgate : b.Coprime c ∧ f ≠ 0 := ⟨hbc,hfn⟩
      simp only [if_pos hgate, if_pos hbc, Complex.ofReal_mul]
      ring
    · have hgate : ¬ (b.Coprime c ∧ f ≠ 0) := fun h => hbc h.1
      simp only [if_neg hgate, if_neg hbc, Complex.ofReal_zero, mul_zero]
  · simp [hfn]
-- END recovered original_smooth_mass_gated_squares

-- BEGIN recovered original_smooth_mass_completed_pairs
theorem smoothMass_eq_completed_pairs (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M B : ℝ} (hM : 0 < M) (hMB : M ≤ 2*B)
    (N C F : ℝ) :
    (smoothMass M N (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
      ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
        if f ≠ 0 then (scaledDyadicCutoff N c : ℂ) *
          (∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
            if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) then
              (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
                ∑' m : ℤ, frequency M c a (outputY f u v) (level u v : ℤ) m else 0) else 0 := by
  rw [smoothMass_eq_gated_squares]
  apply sum_congr rfl
  intro c hc
  let : NeZero c := ⟨(mem_Ioc.mp hc).1.ne'⟩
  apply sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · rw [if_pos hfn, if_pos hfn]
    apply congrArg (fun z : ℂ => (scaledDyadicCutoff N c : ℂ) * z)
    simpa only [reciprocalRow, ← finiteRow_eq_atoms] using
      reciprocal_square_b_poisson (c := c) hM
        (Ioc 0 (Nat.floor (5*B))) (full_b_support hM hMB)
        A a (finiteInnerCarrier T H) lambda omega f
  · rw [if_neg hfn, if_neg hfn]
-- END recovered original_smooth_mass_completed_pairs

-- BEGIN recovered original_six_smooth_mass_completed
theorem sixSmoothMass_eq_completed (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {B : ℝ} (hB : 0 < B) (C F : ℝ) :
    (sixSmoothMass B C (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
      completedPiece A a T H lambda omega B C B C F +
      completedPiece A a T H lambda omega B (2*C) B C F +
      completedPiece A a T H lambda omega B (4*C) B C F +
      completedPiece A a T H lambda omega (2*B) C B C F +
      completedPiece A a T H lambda omega (2*B) (2*C) B C F +
      completedPiece A a T H lambda omega (2*B) (4*C) B C F := by
  have hp (M N : ℝ) (hM : 0 < M) (hMB : M ≤ 2*B) :
      (smoothMass M N (packetBox B C F) (finiteReciprocalRow A a T H lambda omega) : ℂ) =
        completedPiece A a T H lambda omega M N B C F :=
    smoothMass_eq_completed_pairs A a T H lambda omega hM hMB N C F
  have hb : B ≤ 2*B := by linarith
  have hb2 : 0 < 2*B := by positivity
  simp only [sixSmoothMass, Complex.ofReal_add]
  rw [hp B C hB hb, hp B (2*C) hB hb, hp B (4*C) hB hb,
    hp (2*B) C hb2 le_rfl, hp (2*B) (2*C) hb2 le_rfl, hp (2*B) (4*C) hb2 le_rfl]
-- END recovered original_six_smooth_mass_completed

end
end ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
