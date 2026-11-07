import ImbalancedChen.Part3OriginalS2ActualTailTransfer
import ImbalancedChen.Part3MediumGenuinePoissonFibre
import ImbalancedChen.Part3OriginalS2OneCongruencePoisson
import Mathlib.Tactic

/-!
Actual primitive/native-key S2, with its independently defined paperPsi
q/m carriers and lambdaTrim, is passed through one-congruence Poisson.
The zero mode and complete signed nonzero series are separate. The two
ordered S2 gate corrections remain explicit. No Gram variance estimate
is an input. SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode

open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2OneCongruencePoisson
open ImbalancedChen.Part3OriginalS2ZeroGramCompiler
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2ActualTailTransfer
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open Classical Finset MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

noncomputable section

def s2PrimitiveGates (v : FibreIndex) : Prop :=
  v.2.1.2.Coprime (leftModulus v) ∧ v.2.2.2.Coprime (rightModulus v)

def s2InverseResidue (d : MediumAtom) (v : FibreIndex) : ℤ :=
  d.residue * inverseResidue (leftModulus v) (v.2.1.2 : ℤ)

def actualRestoredS2Fibre (d : MediumAtom) (z y : ℝ) (k : Key) (v : FibreIndex) : ℂ :=
  ∑ m ∈ paperPsiNaturalCarrier d.V,
    restoredTerm d z y k (lift v m)

def actualS2ZeroFibre (d : MediumAtom) (z y : ℝ) (k : Key) (v : FibreIndex) : ℂ :=
  if s2PrimitiveGates v then
    headCoefficient d z y k v *
      ((d.V / (leftModulus v : ℝ)) • (𝓕 paperPsiComplex) 0) /
        (Nat.totient (rightModulus v) : ℂ)
  else 0

def actualS2NonzeroFibre (d : MediumAtom) (z y : ℝ) (k : Key) (v : FibreIndex) : ℂ :=
  if s2PrimitiveGates v then
    headCoefficient d z y k v *
      (∑' h : ℤ, paperPsiNonzeroMode (d.V / (leftModulus v : ℝ))
        ((s2InverseResidue d v : ℝ) / leftModulus v) h) /
        (Nat.totient (rightModulus v) : ℂ)
  else 0

def actualS2ZeroMode (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier d k, actualS2ZeroFibre d z y k v

def actualS2NonzeroModes (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier d k, actualS2NonzeroFibre d z y k v

/-- The inverse class uses the original physical q*d*r modulus, and
the second exact mean denominator remains phi(q*d*s). -/
theorem restoredTerm_eq_inverse_progression (d : MediumAtom) (z y : ℝ) (k : Key)
    (v : FibreIndex) (m : ℕ) :
    restoredTerm d z y k (lift v m) =
      if s2PrimitiveGates v then
        headCoefficient d z y k v *
          (if Int.ModEq (leftModulus v) (m : ℤ) (s2InverseResidue d v) then
            scaledPaperPsi d.V m else 0) /
              (Nat.totient (rightModulus v) : ℂ)
      else 0 := by
  by_cases hg : s2PrimitiveGates v
  · have h₁ := hg.1
    have h₂ := hg.2
    have hinv := one_congruence_iff_inverse (leftModulus v) m v.2.1.2 d.residue hg.1
    have hprod : Int.ModEq (leftModulus v)
        (((m * v.2.1.2 : ℕ) : ℤ)) d.residue ↔
        Int.ModEq (leftModulus v) (m : ℤ) (s2InverseResidue d v) := hinv
    unfold restoredTerm samePsiTerm s2TermWithM canonicalIndex lift
      headCoefficient leftModulus rightModulus at *
    simp only [s2PrimitiveGates, leftModulus, rightModulus] at hg
    by_cases hc : Int.ModEq ((v.1.1 * v.1.2) * v.2.1.1)
        (((m * v.2.1.2 : ℕ) : ℤ)) d.residue
    · have hb := hprod.mp hc
      simp [s2PrimitiveGates, h₁, h₂, hc, hb, actualPsiQWeight, actualPsiMWeight, paperQWeight,
        scaledPaperPsi, paperPsiComplex]
    · have hb : ¬Int.ModEq ((v.1.1 * v.1.2) * v.2.1.1)
          (m : ℤ) (s2InverseResidue d v) := fun h => hc (hprod.mpr h)
      simp [s2PrimitiveGates, h₁, h₂, hc, hb]
  · by_cases h₁ : v.2.1.2.Coprime (leftModulus v)
    · have h₂ : ¬v.2.2.2.Coprime (rightModulus v) := fun h => hg ⟨h₁, h⟩
      simp [restoredTerm, samePsiTerm, s2TermWithM, canonicalIndex, lift,
        s2PrimitiveGates, leftModulus, rightModulus, h₁, h₂]
    · simp [restoredTerm, samePsiTerm, s2TermWithM, canonicalIndex, lift,
        s2PrimitiveGates, leftModulus, rightModulus, h₁]

/-- The actual finite m carrier is exactly the paperPsi progression
source; no older smooth cutoff is substituted. -/
theorem actualRestoredS2Fibre_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (v : FibreIndex) (hv : v ∈ fibreCarrier d k) :
    actualRestoredS2Fibre d z y k v =
      actualS2ZeroFibre d z y k v + actualS2NonzeroFibre d z y k v := by
  have hM : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hL := (fibre_moduli_positive (zero_lt_one.trans_le hd.2.2.1) hv).1
  unfold actualRestoredS2Fibre
  simp_rw [restoredTerm_eq_inverse_progression]
  by_cases hg : s2PrimitiveGates v
  · simp only [if_pos hg, actualS2ZeroFibre, actualS2NonzeroFibre]
    rw [← Finset.sum_div, ← Finset.mul_sum,
      paperPsi_finite_residue_poisson_packet hM hL (s2InverseResidue d v)]
    ring
  · simp [actualS2ZeroFibre, actualS2NonzeroFibre, hg]

/-- Genuine actual-source S2 Poisson identity with the common d and
both independent rough/alpha labels preserved. -/
theorem restoredSum_eq_actual_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    restoredSum d z y k = actualS2ZeroMode d z y k + actualS2NonzeroModes d z y k := by
  unfold restoredSum actualS2ZeroMode actualS2NonzeroModes
  rw [sum_paired_eq_fibres, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  exact actualRestoredS2Fibre_eq_zero_add_nonzero hd z y k v hv

theorem actual_preliminary_S2_zero_mode_identity
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    primitiveS2 d z y k + (otherRoughCorrection d z y k).re +
        (singleZeroCorrection d z y k).re =
      (actualS2ZeroMode d z y k).re + (actualS2NonzeroModes d z y k).re := by
  rw [← actual_preliminary_S2_real_identity hd z y k,
    restoredSum_eq_actual_zero_add_nonzero hd z y k, Complex.add_re]

/-- Zero mode after summing the same source alpha coordinates. B_r is
the original primitive mass, not a mean supplied by the variance bound. -/
def actualS2ZeroCollapsed (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ q ∈ nativeQCarrier d, ∑ small ∈ dyadicWindow k.d,
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      (paperQWeight d q : ℂ) * lambdaTrim d z y k small r *
        star (lambdaTrim d z y k small s) *
        ((d.V / ((q * small * r : ℕ) : ℝ)) • (𝓕 paperPsiComplex) 0) /
          (Nat.totient (q * small * s) : ℂ) *
        (primitiveMass d (q * small) r * star (primitiveMass d (q * small) s))

theorem actualS2ZeroMode_eq_collapsed (d : MediumAtom) (z y : ℝ) (k : Key) :
    actualS2ZeroMode d z y k = actualS2ZeroCollapsed d z y k := by
  unfold actualS2ZeroMode actualS2ZeroCollapsed fibreCarrier innerCarrier
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro small hsmall
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [primitiveMass_mul_star]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  apply Finset.sum_congr rfl
  intro n₂ hn₂
  by_cases h₁ : n₁.Coprime (q * small * r) <;>
    by_cases h₂ : n₂.Coprime (q * small * s) <;>
    simp [actualS2ZeroFibre, s2PrimitiveGates, headCoefficient,
      leftModulus, rightModulus, h₁, h₂] <;> ring

end
end ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
