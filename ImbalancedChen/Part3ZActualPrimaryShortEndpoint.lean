import ImbalancedChen.Part3FixedRhoPrimarySignedFiniteDecomposition
import ImbalancedChen.Part3ActualLiteralPacketIntegral
import Mathlib.Tactic

/-!
# P3 actual finite beta at the short primary endpoint

Source-written, uncompiled. Dyadic support is obtained from an explicit
filter of the actual Source carrier, never attributed to arbitrary beta.
The original generic PacketData carrier only has a wider normalized box.
-/

namespace ImbalancedChen.P3ZActualPrimaryShortEndpoint

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3 (CoprimePacket CommonCompletedVariable)
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)

def signedY (negative : Bool) (y : ℕ) : ℤ := if negative then -(y : ℤ) else (y : ℤ)

theorem signedY_abs (negative : Bool) (y : ℕ) : |(signedY negative y : ℝ)| = (y : ℝ) := by
  cases negative <;> simp [signedY]

theorem signedY_natAbs (negative : Bool) (y : ℕ) : (signedY negative y).natAbs = y := by
  cases negative <;> simp [signedY]

theorem signedY_div (negative : Bool) {nu : ℕ} (hnu : 0 < nu) (n : ℕ) :
    (signedY negative (nu * n) / (nu : ℤ)).natAbs = n := by
  have hprod : signedY negative (nu * n) = (nu : ℤ) * signedY negative n := by
    cases negative <;> simp [signedY, Nat.cast_mul, mul_neg]
  have hnuZ : (nu : ℤ) ≠ 0 := by exact_mod_cast hnu.ne'
  rw [hprod, Int.mul_ediv_cancel_left _ hnuZ, signedY_natAbs]

/-- A literal primary/sign/dyadic restriction of the actual finite source.
The nonzero filter supplies the existing primaryFibre_gate hypothesis. -/
def dyadicSource (rho : ℤ) (S : Finset Source) (nu : ℕ) (U : ℝ)
    (negative : Bool) : Finset Source :=
  (primaryFibre rho (nonzeroSource S) nu).filter fun s =>
    U < |((output s).2 : ℝ)| ∧ |((output s).2 : ℝ)| ≤ 2 * U ∧
      (if negative then (output s).2 < 0 else 0 < (output s).2)

def dyadicBeta (rho : ℤ) (S : Finset Source) (nu : ℕ) (U : ℝ) (negative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (y z : ℕ) : ℂ :=
  beta (dyadicSource rho S nu U negative) lambda omega (z, signedY negative y)

theorem dyadicSource_subset (rho : ℤ) (S : Finset Source) (nu : ℕ) (U : ℝ)
    (negative : Bool) : dyadicSource rho S nu U negative ⊆ S := by
  intro s hs
  exact (mem_filter.mp (mem_filter.mp (mem_filter.mp hs).1).1).1

theorem dyadicBeta_source_witness {rho : ℤ} {S : Finset Source} {nu : ℕ} {U : ℝ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {y z : ℕ}
    (hb : dyadicBeta rho S nu U negative lambda omega y z ≠ 0) :
    ∃ s ∈ dyadicSource rho S nu U negative, output s = (z, signedY negative y) := by
  exact mem_image.mp (beta_ne_zero_mem_image hb)

theorem dyadicBeta_support {rho : ℤ} {S : Finset Source} {nu : ℕ} {U : ℝ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {y z : ℕ}
    (hb : dyadicBeta rho S nu U negative lambda omega y z ≠ 0) :
    U < (y : ℝ) ∧ (y : ℝ) ≤ 2 * U := by
  obtain ⟨s, hs, hout⟩ := dyadicBeta_source_witness hb
  have h := (mem_filter.mp hs).2
  simpa only [hout, signedY_abs] using And.intro h.1 h.2.1

theorem dyadicBeta_multiplier_pos {rho : ℤ} {S : Finset Source} {nu : ℕ} {U : ℝ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {y z : ℕ}
    (hb : dyadicBeta rho S nu U negative lambda omega y z ≠ 0) : 0 < nu := by
  obtain ⟨s, hs, _⟩ := dyadicBeta_source_witness hb
  have hkey := (mem_filter.mp (mem_filter.mp hs).1).2
  simpa only [hkey] using rhoPrimaryNu_pos rho (output s).2

theorem dyadicBeta_coprime {rho : ℤ} {S : Finset Source} {nu : ℕ} {U : ℝ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {n z : ℕ}
    (hb : dyadicBeta rho S nu U negative lambda omega (nu * n) z ≠ 0) :
    Nat.Coprime n rho.natAbs := by
  obtain ⟨s, hs, hout⟩ := dyadicBeta_source_witness hb
  have hgate := primaryFibre_gate
    (rho := rho) (U := nonzeroSource S)
    (fun t ht => (mem_filter.mp ht).2) (mem_filter.mp hs).1
  have hnu := dyadicBeta_multiplier_pos hb
  simpa only [hout, signedY_div negative hnu n] using hgate.2

/-- Nonempty actual beta blocks have nu<=2U and U/nu>=1/2.
The strict lower dyadic support is read from the filter itself. -/
theorem nonempty_endpoint_bounds {rho : ℤ} {S : Finset Source} {nu : ℕ} {U : ℝ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {n z : ℕ}
    (hU : 0 < U) (hb : dyadicBeta rho S nu U negative lambda omega (nu * n) z ≠ 0) :
    0 < nu ∧ 0 < n ∧ (nu : ℝ) ≤ 2 * U ∧ (1 : ℝ) / 2 ≤ U / (nu : ℝ) := by
  have hs := dyadicBeta_support hb
  have hnu := dyadicBeta_multiplier_pos hb
  have hn : 0 < n := by
    by_contra hn
    have hz : n = 0 := by omega
    simp only [hz, mul_zero, Nat.cast_zero] at hs
    linarith
  have hprodN : nu ≤ nu * n := by
    simpa only [mul_one] using Nat.mul_le_mul_left nu (show 1 ≤ n by omega)
  have hprod : (nu : ℝ) ≤ ((nu * n : ℕ) : ℝ) := by exact_mod_cast hprodN
  have hupper : (nu : ℝ) ≤ 2 * U := hprod.trans hs.2
  have hnuR : 0 < (nu : ℝ) := by exact_mod_cast hnu
  have hhalf : (1 : ℝ) / 2 ≤ U / (nu : ℝ) := by
    apply (le_div_iff₀ hnuR).mpr
    linarith
  exact ⟨hnu, hn, hupper, hhalf⟩

theorem short_nonzero_index_eq_one {rho : ℤ} {S : Finset Source} {nu : ℕ} {U : ℝ}
    {negative : Bool} {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {n z : ℕ}
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (hb : dyadicBeta rho S nu U negative lambda omega (nu * n) z ≠ 0) : n = 1 := by
  have hbds := nonempty_endpoint_bounds hU hb
  have hnuR : 0 < (nu : ℝ) := by exact_mod_cast hbds.1
  have hUnu : U < (nu : ℝ) := by
    simpa only [one_mul] using (div_lt_iff₀ hnuR).mp hshort
  have hs := (dyadicBeta_support hb).2
  push_cast at hs
  have hnreal : (n : ℝ) < 2 := by
    apply (mul_lt_mul_left hnuR).mp
    nlinarith only [hs, hUnu]
  have hnlt : n < 2 := by exact_mod_cast hnreal
  omega

def dyadicPacket (rho : ℤ) (S : Finset Source) (nu z : ℕ) (U : ℝ) (negative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z) :
    CoprimePacket where
  residue := rho.natAbs
  level := z
  multiplier := nu
  level_pos := hz
  residue_coprime := hc
  beta := dyadicBeta rho S nu U negative lambda omega

theorem short_signedCoefficient_zero (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1) {n : ℕ} (hn : n ≠ 1) :
    signedCoefficient negative (dyadicPacket rho S nu z U negative lambda omega hz hc) n = 0 := by
  have hb : dyadicBeta rho S nu U negative lambda omega (nu * n) z = 0 := by
    by_contra hb
    exact hn (short_nonzero_index_eq_one hU hshort hb)
  simp only [signedCoefficient, dyadicPacket]
  split_ifs <;> simp only [hb, zero_mul]

theorem short_modeCoefficient_zero (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (k : D4 → ℤ) (Z : ℝ) {n : ℕ} (hn : n ≠ 1) :
    signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n = 0 := by
  rw [signedCoefficient_modePacket, short_signedCoefficient_zero rho S nu z U negative
    lambda omega hz hc hU hshort hn, zero_mul]

/-- Generic finite-singleton identity used only to consume the proved
actual short coefficient support; it imposes no analytic estimate. -/
private theorem finite_singleton {E : Type*} [AddCommMonoid E]
    (N : Finset ℕ) (F : ℕ → E) (hF : ∀ n, n ≠ 1 → F n = 0) :
    (∑ n ∈ N, F n) = if 1 ∈ N then F 1 else 0 := by
  by_cases h1 : 1 ∈ N
  · rw [if_pos h1]
    apply sum_eq_single 1
    · intro n _ hn
      exact hF n hn
    · intro hn
      exact False.elim (hn h1)
  · rw [if_neg h1]
    apply sum_eq_zero
    intro n hn
    apply hF
    intro heq
    exact h1 (heq ▸ hn)

/-- Actual finite beta mass reduction, with the original coprime gate and
mode phase still in the coefficient. This is not a duplicate L2 bound. -/
theorem short_mode_mass (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (k : D4 → ℤ) (Z : ℝ) (N : Finset ℕ) :
    (∑ n ∈ N, ‖signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n‖ ^ 2) =
      if 1 ∈ N then ‖signedCoefficient negative
        (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) 1‖ ^ 2 else 0 := by
  apply finite_singleton
  intro n hn
  rw [short_modeCoefficient_zero rho S nu z U negative lambda omega hz hc hU hshort k Z hn]
  norm_num

theorem modeCoefficient_one_norm (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z) (k : D4 → ℤ) (Z : ℝ) :
    ‖signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) 1‖ =
        ‖dyadicBeta rho S nu U negative lambda omega nu z‖ := by
  rw [norm_signedCoefficient_modePacket, ← signedCoefficient_false_eq_actual]
  simp [signedCoefficient, dyadicPacket, cuspPhase,
    P3Period64NativeReconstructionSourceOnly.norm_e]

theorem short_mode_mass_eq_beta (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (k : D4 → ℤ) (Z : ℝ) (N : Finset ℕ) :
    (∑ n ∈ N, ‖signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n‖ ^ 2) =
      if 1 ∈ N then ‖dyadicBeta rho S nu U negative lambda omega nu z‖ ^ 2 else 0 := by
  rw [short_mode_mass rho S nu z U negative lambda omega hz hc hU hshort k Z N,
    modeCoefficient_one_norm rho S nu z U negative lambda omega hz hc k Z]

/-- Literal packet reduction to n=1. The common completed-variable phase
is exactly the same object at every m and is never moved or discarded. -/
theorem short_common_phase_packet (rho : ℤ) (S : Finset Source) (nu z : ℕ)
    (U : ℝ) (negative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hz : 0 < z) (hc : Nat.Coprime rho.natAbs z)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (k : D4 → ℤ) (Z : ℝ) (I : CommonCompletedVariable)
    (M N : Finset ℕ) (K : ℕ → ℕ → ℂ) :
    (∑ m ∈ M, ∑ n ∈ N, I.weight m * signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n * K m n) =
      if 1 ∈ N then ∑ m ∈ M, I.weight m * signedCoefficient negative
        (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) 1 * K m 1 else 0 := by
  have hs (m : ℕ) := finite_singleton N
    (fun n => I.weight m * signedCoefficient negative
      (modePacket (dyadicPacket rho S nu z U negative lambda omega hz hc) k U Z) n * K m n)
    (fun n hn => by
      rw [short_modeCoefficient_zero rho S nu z U negative lambda omega hz hc hU hshort k Z hn]
      simp)
  simp_rw [hs]
  by_cases h1 : 1 ∈ N <;> simp only [h1, if_true, if_false, sum_const_zero]

/-- Direct specialization to the installed actual nonzero source. Residue
sign and output-y sign are independent parameters. -/
abbrev actualDyadicBeta (e : ImbalancedChen.Part3.MediumAtom) (D delta g l : ℕ)
    (Z : ℝ) (residueNegative yNegative : Bool) (nu : ℕ) (U : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (y z : ℕ) : ℂ :=
  dyadicBeta
    (ImbalancedChen.Part3.ActualSeparatedRowPacketMatchSourceOnly.signedResidue residueNegative e.residue)
    (ImbalancedChen.Part3.ActualModeBetaPositiveCountSourceOnly.actualNonzeroSource
      e D delta g l Z residueNegative) nu U yNegative lambda omega y z

theorem actual_nonempty_endpoint_bounds (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (residueNegative yNegative : Bool)
    (nu n z : ℕ) (U : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hU : 0 < U)
    (hb : actualDyadicBeta e D delta g l Z residueNegative yNegative nu U lambda omega (nu * n) z ≠ 0) :
    0 < nu ∧ 0 < n ∧ (nu : ℝ) ≤ 2 * U ∧ (1 : ℝ) / 2 ≤ U / (nu : ℝ) := by
  exact nonempty_endpoint_bounds hU hb

theorem actual_short_index_eq_one (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (residueNegative yNegative : Bool)
    (nu n z : ℕ) (U : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hU : 0 < U) (hshort : U / (nu : ℝ) < 1)
    (hb : actualDyadicBeta e D delta g l Z residueNegative yNegative nu U lambda omega (nu * n) z ≠ 0) :
    n = 1 := by
  exact short_nonzero_index_eq_one hU hshort hb

theorem actual_nonzero_coprime (e : ImbalancedChen.Part3.MediumAtom)
    (D delta g l : ℕ) (Z : ℝ) (residueNegative yNegative : Bool)
    (nu n z : ℕ) (U : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hb : actualDyadicBeta e D delta g l Z residueNegative yNegative nu U lambda omega (nu * n) z ≠ 0) :
    Nat.Coprime n e.residue.natAbs := by
  simpa only [ImbalancedChen.Part3.ActualM2FinitePoissonAdapterSourceOnly.signedResidue_natAbs] using
    dyadicBeta_coprime hb

end

end ImbalancedChen.P3ZActualPrimaryShortEndpoint
