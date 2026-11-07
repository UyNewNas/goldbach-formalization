import ImbalancedChen.Part3OriginalGevreyCleanE2Quotient
import ImbalancedChen.Part3OriginalCanonicalS2Stages
import ImbalancedChen.Part3OriginalMediumPhysicalE3RowReindex
import ImbalancedChen.Part3MediumReceiverCutoffArithmetic
import ImbalancedChen.Part3ActualReciprocalSquarePoisson
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.

The preliminary smooth d is the FIRST coordinate of the actual canonical
labelDW image. It is not redefined to be the gcd of two unsplit tail labels.
The exact Lambda fiber supplies its coprimality with each admitted rough w.
This constructs a FixedBlock with the actual Lambda and actual paperPsi
Fourier profiles while retaining its original geometry and clean carrier.

The full preliminary-d family of raw six-coordinate physical Poisson terms
is split disjointly by the original E3 clean carrier. Every nonclean term
retains its complete physical lcm, constructed CRT residue, signed h,
actual psi and coefficients. No estimate or zero claim is made for that
complement. Clean inverse licenses and the physical lcm specialization
are derived from the original clean gate, only on that gate.
-/

noncomputable section
open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalGevreyCleanE2Quotient20261028
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalE3RowReindex

namespace ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028

private theorem smooth_pos (z : ℝ) (n : ℕ) : 0 < zSmoothPart z n := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _

private theorem rough_pos (z : ℝ) (n : ℕ) : 0 < zRoughPart z n := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _

private theorem prime_dvd_smooth_le {z : ℝ} {n p : ℕ}
    (hp : p.Prime) (hd : p ∣ zSmoothPart z n) : (p : ℝ) ≤ z := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨hqn, hqz⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq.symm ▸ hqz

private theorem prime_dvd_rough_gt {z : ℝ} {n p : ℕ}
    (hp : p.Prime) (hd : p ∣ zRoughPart z n) : z < (p : ℝ) := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨hqn, hqz⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq.symm ▸ hqz

/-- Prime powers remain entire on their actual smooth/rough sides,
including the cutoff prime on the smooth side. -/
theorem actual_smooth_coprime_actual_rough (z : ℝ) (n m : ℕ) :
    (zSmoothPart z n).Coprime (zRoughPart z m) := by
  apply (Nat.disjoint_primeFactors (smooth_pos z n).ne' (rough_pos z m).ne').mp
  rw [Finset.disjoint_left]
  intro p hs hr
  have hp := Nat.prime_of_mem_primeFactors hs
  have hsmall := prime_dvd_smooth_le hp (Nat.dvd_of_mem_primeFactors hs)
  have hrough := prime_dvd_rough_gt hp (Nat.dvd_of_mem_primeFactors hr)
  exact (not_lt_of_ge hsmall) hrough

/-- Literal preliminary d and its actual rough product are coprime. -/
theorem labelDW_preliminary_coprime (z : ℝ) (v : ℕ × ℕ) :
    (labelDW z v).1.Coprime (labelDW z v).2 := by
  exact Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_right.mpr
      ⟨actual_smooth_coprime_actual_rough z v.1 v.1,
        actual_smooth_coprime_actual_rough z v.1 v.2⟩,
      Nat.coprime_mul_iff_right.mpr
      ⟨actual_smooth_coprime_actual_rough z v.2 v.1,
        actual_smooth_coprime_actual_rough z v.2 v.2⟩⟩

/-- The coefficient support licence is proved from the actual finite
fiber. It is not supplied as a new source or E2 conclusion premise. -/
theorem actual_Lambda_support_coprime (atom : MediumAtom) (z : ℝ)
    (small w : ℕ) (hw : Lambda atom z small w ≠ 0) : small.Coprime w := by
  by_contra hbad
  apply hw
  unfold Lambda
  apply Finset.sum_eq_zero
  intro v hv
  have hlabel := labelDW_preliminary_coprime z v
  rw [(Finset.mem_filter.mp hv).2] at hlabel
  exact (hbad hlabel).elim

/-- The geometry stays in the original fixed block; only formerly opaque
coefficient/profile fields are now the exact canonical manuscript objects. -/
def actualBlock (B : FixedBlock) (z : ℝ) : FixedBlock :=
  { B with
    lambdaD := Lambda B.atom z B.d
    lambdaD_support_coprime := actual_Lambda_support_coprime B.atom z B.d
    psi0 := paperPsiComplex
    psi0_support := by
      intro v hv
      change (paperPsi v : ℂ) = 0
      rw [paperPsi_zero_outside v hv]
      rfl
    psiHat0 := 𝓕 paperPsiComplex }

@[simp] theorem actualBlock_d (B : FixedBlock) (z : ℝ) :
    (actualBlock B z).d = B.d := rfl

@[simp] theorem actualBlock_atom (B : FixedBlock) (z : ℝ) :
    (actualBlock B z).atom = B.atom := rfl

@[simp] theorem actualBlock_lambda (B : FixedBlock) (z : ℝ) (w : ℕ) :
    (actualBlock B z).lambdaD w = Lambda B.atom z B.d w := rfl

/-- All original coprimalities, separation and exact index windows remain. -/
@[simp] theorem actualBlock_carrier (B : FixedBlock) (z : ℝ) :
    (actualBlock B z).carrier = B.carrier := rfl

/-- Exact literal preliminary-d ownership; the numerator is a product of
the two true smooth parts, not the tail gcd of an unrelated paired row. -/
theorem preliminary_d_mem_actual_carrier {atom : MediumAtom} {z : ℝ}
    {v : ℕ × ℕ} (hv : v ∈ factorCarrier atom.Q2 ×ˢ factorCarrier atom.Q3) :
    (labelDW z v).1 ∈ dCarrier atom z :=
  Finset.mem_image.mpr ⟨labelDW z v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, rfl⟩

/-- Same six-coordinate physical box already used by the E3 reindexer. -/
def noncleanBox (B : FixedBlock) : Finset Raw :=
  (rawBox B).filter (fun r => pack r ∉ B.carrier)

def cleanBox (B : FixedBlock) : Finset Raw :=
  (rawBox B).filter (fun r => pack r ∈ B.carrier)

/-- Every actual E3 tuple occurs exactly once in the clean raw box. -/
theorem cleanBox_image (B : FixedBlock) : (cleanBox B).image pack = B.carrier := by
  ext t
  constructor
  · intro ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hr).2
  · intro ht
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp (carrier_subset_rawBox_image B ht)
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, heq.symm ▸ ht⟩, heq⟩

/-- The same physical CRT kernel before the clean gate. In particular
q is never replaced by q*d, and the preliminary d remains explicit. -/
def fullPhysicalL (B : FixedBlock) (t : Index) : ℕ :=
  (t.q * B.d * t.w1).lcm (t.q * B.d * t.w2)

def fullPhysicalResidue (B : FixedBlock) (t : Index) : ℤ :=
  ComplexCRT.residue (t.q * B.d * t.w1) (t.q * B.d * t.w2)
    t.n1 t.n2 B.atom.residue

def fullPhysicalTerm (B : FixedBlock) (z : ℝ) (t : Index) : ℂ :=
  if ComplexCRT.Compatible (t.q * B.d * t.w1) (t.q * B.d * t.w2)
      t.n1 t.n2 then
    Lambda B.atom z B.d t.w1 * star (Lambda B.atom z B.d t.w2) *
      B.atom.alpha t.n1 * star (B.atom.alpha t.n2) *
      paperPsiComplex ((t.q : ℝ) / B.atom.Q1) *
      paperPsiNonzeroMode (B.atom.V / (fullPhysicalL B t : ℝ))
        ((fullPhysicalResidue B t : ℝ) / (fullPhysicalL B t : ℝ)) t.h
  else 0

def fullPhysicalSum (B : FixedBlock) (z : ℝ) : ℂ :=
  ∑ r ∈ rawBox B, fullPhysicalTerm B z (pack r)

def cleanPhysicalSum (B : FixedBlock) (z : ℝ) : ℂ :=
  ∑ r ∈ cleanBox B, fullPhysicalTerm B z (pack r)

def noncleanPhysicalSum (B : FixedBlock) (z : ℝ) : ℂ :=
  ∑ r ∈ noncleanBox B, fullPhysicalTerm B z (pack r)

/-- Exact actual finite clean/complement partition. No part of the
complement is bounded, replaced, or declared zero in this identity. -/
theorem fullPhysicalSum_eq_clean_add_nonclean (B : FixedBlock) (z : ℝ) :
    fullPhysicalSum B z = cleanPhysicalSum B z + noncleanPhysicalSum B z := by
  unfold fullPhysicalSum cleanPhysicalSum noncleanPhysicalSum cleanBox noncleanBox
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hc : pack r ∈ B.carrier <;> simp [hc]

/-- Bind the clean part to the original E3 carrier, with its unchanged
physical CRT payload. This is an identity of carriers, not a claim that
all actual terms belong to the clean carrier. -/
theorem cleanPhysicalSum_eq_E3_carrier (B : FixedBlock) (z : ℝ) :
    cleanPhysicalSum B z = ∑ t ∈ (actualBlock B z).carrier,
      fullPhysicalTerm B z t := by
  rw [actualBlock_carrier]
  unfold cleanPhysicalSum
  rw [← cleanBox_image B,
    Finset.sum_image (fun r _ r' _ h => pack_injective h)]

/-- On the original clean branch the rough pair is coprime. -/
theorem E3_clean_rough_coprime {B : FixedBlock} {t : Index}
    (ht : B.clean t) : t.w1.Coprime t.w2 := by
  obtain ⟨hq, hw1, hw2, hmod, hn1, hn2, hsep⟩ := ht
  exact hw1.of_dvd_right (dvd_mul_left _ _)

/-- The preliminary d becomes the tail gcd ONLY after the actual clean
rough-pair gate has been imposed. It is not true on the whole raw box. -/
theorem E3_clean_tail_gcd {B : FixedBlock} {t : Index}
    (ht : B.clean t) : (B.d * t.w1).gcd (B.d * t.w2) = B.d := by
  rw [Nat.gcd_mul_left, (E3_clean_rough_coprime ht).gcd_eq_one, mul_one]

/-- Actual complete lcm on the clean E3 branch. -/
theorem E3_clean_complete_lcm {B : FixedBlock} {t : Index}
    (ht : B.clean t) : fullPhysicalL B t = t.q * B.d * t.w1 * t.w2 := by
  unfold fullPhysicalL
  rw [Nat.lcm_mul_left, (E3_clean_rough_coprime ht).lcm_eq_mul]
  ring

/-- The original E3 clean gate supplies the exact full physical CRT
compatibility. No independent compatibility condition is required. -/
theorem E3_clean_CRT_compatible {B : FixedBlock} {t : Index}
    (ht : B.clean t) :
    ComplexCRT.Compatible (t.q * B.d * t.w1) (t.q * B.d * t.w2) t.n1 t.n2 := by
  have hww := E3_clean_rough_coprime ht
  obtain ⟨hq, hw1, hw2, hmod, hn1, hn2, hsep⟩ := ht
  refine ⟨hn1.of_dvd_right ⟨t.n2, by ring⟩,
    hn2.of_dvd_right ⟨t.n1, by ring⟩, ?_⟩
  simpa only [Nat.gcd_mul_left, hww.gcd_eq_one, mul_one, mul_assoc] using hmod

/-- Exact inverse licenses on the original E3 clean gate. These are
needed by (21), and are derived here from its literal source gates. -/
theorem E3_clean_inverse_licenses {B : FixedBlock} {t : Index}
    (ht : B.clean t) :
    (t.n1 * t.w2).Coprime (t.q * B.d * t.w1) ∧
      (t.n2 * (t.q * B.d * t.w1)).Coprime t.w2 ∧
      (t.n2 * (t.q * B.d * t.w1)).Coprime (t.n1 * t.w2) := by
  obtain ⟨hq, hw1, hw2, hmod, hn1, hn2, hsep⟩ := ht
  have hN1A : t.n1.Coprime (t.q * B.d * t.w1) :=
    hn1.of_dvd_right ⟨t.n2, by ring⟩
  have hN2B : t.n2.Coprime t.w2 := hn2.of_dvd_right ⟨t.n1 * t.q * B.d, by ring⟩
  have hN12 : t.n1.Coprime t.n2 := hn1.of_dvd_right ⟨t.q * B.d * t.w1, by ring⟩
  have hAB : (t.q * B.d * t.w1).Coprime t.w2 :=
    hw2.symm.of_dvd_left ⟨B.atom.residue.natAbs, by ring⟩
  refine ⟨Nat.coprime_mul_iff_left.mpr ⟨hN1A, hAB.symm⟩,
    Nat.coprime_mul_iff_left.mpr ⟨hN2B, hAB⟩, ?_⟩
  exact Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_right.mpr ⟨hN12.symm, hN2B⟩,
      Nat.coprime_mul_iff_right.mpr ⟨hN1A.symm, hAB⟩⟩

/-- A family must bind its structural atom and preliminary d to the
actual source image before it is called the preliminary E2 family.
These are field identities, not an E2 estimate or a clean-cover premise. -/
structure PreliminaryBlockFamily (atom : MediumAtom) (z : ℝ) where
  blocks : ℕ → FixedBlock
  atom_eq : ∀ small ∈ dCarrier atom z, (blocks small).atom = atom
  d_eq : ∀ small ∈ dCarrier atom z, (blocks small).d = small

/-- Every preliminary-d block retains its own original d. The family
geometry may depend on d; it is fixed before evaluating any row. -/
def globalPreliminaryE2 (atom : MediumAtom) (z : ℝ)
    (F : PreliminaryBlockFamily atom z) : ℂ :=
  ∑ small ∈ dCarrier atom z,
    ((1 / atom.V : ℝ) : ℂ) * fullPhysicalSum (F.blocks small) z

def globalCleanE2 (atom : MediumAtom) (z : ℝ)
    (F : PreliminaryBlockFamily atom z) : ℂ :=
  ∑ small ∈ dCarrier atom z,
    ((1 / atom.V : ℝ) : ℂ) * cleanPhysicalSum (F.blocks small) z

def globalNoncleanE2 (atom : MediumAtom) (z : ℝ)
    (F : PreliminaryBlockFamily atom z) : ℂ :=
  ∑ small ∈ dCarrier atom z,
    ((1 / atom.V : ℝ) : ℂ) * noncleanPhysicalSum (F.blocks small) z

/-- Actual global finite partition, including the nonclean general-D
payload. Neither a family estimate nor a clean-cover assertion is a premise. -/
theorem globalPreliminaryE2_eq_clean_add_nonclean (atom : MediumAtom) (z : ℝ)
    (F : PreliminaryBlockFamily atom z) :
    globalPreliminaryE2 atom z F =
      globalCleanE2 atom z F + globalNoncleanE2 atom z F := by
  unfold globalPreliminaryE2 globalCleanE2 globalNoncleanE2
  simp only [fullPhysicalSum_eq_clean_add_nonclean, mul_add, Finset.sum_add_distrib]

/-- The canonical actual profile/coefficient update preserves the
source preliminary-d identity, independently of any tail-gcd parameter. -/
theorem actual_block_family_d {atom : MediumAtom} {z : ℝ}
    (F : PreliminaryBlockFamily atom z)
    (small : ℕ) (hs : small ∈ dCarrier atom z) :
    (actualBlock (F.blocks small) z).d = small := F.d_eq small hs

/-- Correct normalization of the clean raw Poisson factor. It produces
V/d times the E3 denominator 1/(q*w1*w2), with no extra d in E3. -/
theorem E3_clean_denominator (V : ℝ) {q small w1 w2 : ℕ}
    (hq : 0 < q) (hd : 0 < small) (hw1 : 0 < w1) (hw2 : 0 < w2) :
    V / ((q * small * w1 * w2 : ℕ) : ℝ) =
      (V / (small : ℝ)) * (1 / ((q * w1 * w2 : ℕ) : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hdR : (small : ℝ) ≠ 0 := by positivity
  have h1R : (w1 : ℝ) ≠ 0 := by positivity
  have h2R : (w2 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp [hqR, hdR, h1R, h2R]
  ring


private theorem actual_carrier_positive {B : FixedBlock} {t : Index}
    (ht : t ∈ B.carrier) : 0 < t.q ∧ 0 < t.w1 ∧ 0 < t.w2 ∧ 0 < t.n1 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (carrier_subset_rawBox_image B ht)
  rcases r with ⟨q, w1, w2, n1, n2, h⟩
  simp only [rawBox, Finset.mem_product] at hr
  obtain ⟨hq, hw1, hw2, hn1, hn2, hh⟩ := hr
  have hq0 : (0 : ℝ) < q := B.q0_pos.trans_le
    (B.qLo_block.trans (by exact_mod_cast (Finset.mem_Icc.mp hq).1))
  have hfactor {Q : ℝ} (hQ : 0 < Q) {n : ℕ}
      (hn : n ∈ factorCarrier Q) : 0 < n := by
    exact (Nat.ceil_pos.mpr hQ).trans_le (Finset.mem_Icc.mp hn).1
  change 0 < q ∧ 0 < w1 ∧ 0 < w2 ∧ 0 < n1
  exact ⟨by exact_mod_cast hq0, hfactor B.rough_pos hw1,
    hfactor B.rough_pos hw2, hfactor B.U_pos (Finset.mem_filter.mp hn1).1⟩

/-- Equation (21) now consumes membership in the ACTUAL E3 carrier;
it no longer asks the caller for inverse or CRT-phase identities. -/
theorem actual_E3_CRT_phase_eq21 {B : FixedBlock} {t : Index}
    (ht : t ∈ B.carrier) :
    fourier t.h ((((fullPhysicalResidue B t : ℝ) /
      (fullPhysicalL B t : ℝ)) : ℝ) : UnitAddCircle) =
      fourier t.h ((((B.atom.residue : ℝ) * ((t.n1 : ℝ) - t.n2) *
        CanonicalReciprocalPhase.wPhaseInverse (t.n2 * (t.q * B.d * t.w1))
          (t.n1 * t.w2) / ((t.n1 : ℝ) * t.w2)) : ℝ) : UnitAddCircle) *
      fourier t.h ((((B.atom.residue : ℝ) /
        ((t.q : ℝ) * B.d * t.w1 * t.w2 * t.n1)) : ℝ) : UnitAddCircle) := by
  have hclean : B.clean t := (Finset.mem_filter.mp ht).2
  have hcompat := E3_clean_CRT_compatible hclean
  have hb := ComplexCRT.residue_spec B.atom.residue hcompat
  obtain ⟨hq0, hw10, hw20, hn10⟩ := actual_carrier_positive ht
  have hA0 : 0 < t.q * B.d * t.w1 :=
    Nat.mul_pos (Nat.mul_pos hq0 B.d_pos) hw10
  obtain ⟨hu, hv, hinv⟩ := E3_clean_inverse_licenses hclean
  have hAB : (t.q * B.d * t.w1).Coprime t.w2 := by
    obtain ⟨hq, hw1, hw2, hmod, hn1, hn2, hsep⟩ := hclean
    exact hw2.symm.of_dvd_left ⟨B.atom.residue.natAbs, by ring⟩
  have hbA : Int.ModEq (t.q * B.d * t.w1)
      (fullPhysicalResidue B t * t.n1) B.atom.residue := hb.1
  have hbB : Int.ModEq t.w2
      (fullPhysicalResidue B t * t.n2) B.atom.residue :=
    hb.2.1.of_dvd (by exact_mod_cast (dvd_mul_left t.w2 (t.q * B.d)))
  have hcircle := clean_CRT_circle_eq_two_inverse hA0 hw20 hAB hu hv
    B.atom.residue (fullPhysicalResidue B t) hbA hbB
  have hF := congrArg (fun z : UnitAddCircle => fourier t.h z) hcircle
  have heq := clean_two_inverse_phase_eq21 hA0 hw20 hn10 hu hv hinv B.atom.residue t.h
  calc
    _ = fourier t.h (((((B.atom.residue : ℝ) *
        CanonicalReciprocalPhase.wPhaseInverse (t.n1 * t.w2)
          (t.q * B.d * t.w1) / (t.q * B.d * t.w1)) +
        (B.atom.residue : ℝ) *
          CanonicalReciprocalPhase.wPhaseInverse (t.n2 * (t.q * B.d * t.w1))
            t.w2 / t.w2) : ℝ) : UnitAddCircle) := by
      simpa only [E3_clean_complete_lcm hclean, Nat.cast_mul] using hF
    _ = _ := by
      simpa only [Nat.cast_mul, mul_assoc] using heq

/-- Exact actual analytic profiles of E3 after preliminary d binding;
psiHat0 is the Fourier transform of the same time-domain paperPsi. -/
theorem actualBlock_weight (B : FixedBlock) (z : ℝ) (t : Index) :
    (actualBlock B z).weight t =
      paperPsiComplex ((t.q : ℝ) / B.atom.Q1) *
        (𝓕 paperPsiComplex) ((t.h : ℝ) * B.atom.V /
          ((t.q * B.d * t.w1 * t.w2 : ℕ) : ℝ)) *
        Complex.exp (((2 * Real.pi *
          ((B.atom.residue : ℝ) * (t.h : ℝ) /
            ((t.q * B.d * t.w1 * t.w2 * t.n1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := rfl

/-- The actual preliminary-d coefficients have exactly the original E3
q*w1*w2 denominator. The only d in the coupled weight is the physical
Poisson/slow-phase modulus, as in the manuscript. -/
theorem actualBlock_coeff (B : FixedBlock) (z : ℝ) (t : Index) :
    (actualBlock B z).coeff t =
      (Lambda B.atom z B.d t.w1 * Complex.conj (Lambda B.atom z B.d t.w2) *
        B.atom.alpha t.n1 * Complex.conj (B.atom.alpha t.n2) /
          ((t.q * t.w1 * t.w2 : ℕ) : ℂ)) * B.firstPhase t := rfl


open MediumReceiverCutoffArithmetic20261028
open MediumGlobalDyadicOwnership20261028

/-- The strict receiver fiber at the exact translated integer cutoff.
This is an untrimmed source fiber; no key/window/trim condition is erased. -/
def receiverLambdaFiber (atom : MediumAtom) (z : ℝ) (small w : ℕ) : ℂ :=
  ∑ v ∈ factorCarrier atom.Q2 ×ˢ factorCarrier atom.Q3
      with actualD (strictReceiverCutoff z) v = small ∧
        actualW (strictReceiverCutoff z) v = w,
    atom.gamma2 v.1 * atom.gamma3 v.2

/-- Original smooth p<=z/rough p>z equals the strict receiver p<c/rough
p>=c at c=floor(z)+1/2. No no-boundary-prime assumption is introduced. -/
theorem actual_Lambda_eq_receiverFiber (atom : MediumAtom) (z : ℝ)
    (hz : 0 ≤ z) (small w : ℕ) :
    Lambda atom z small w = receiverLambdaFiber atom z small w := by
  unfold Lambda receiverLambdaFiber
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  rw [originalLabelDW_eq_receiver z hz v]
  simp only [Prod.mk.injEq]

/-- The actualBlock lambda field now has a proved exact strict receiver
fiber identity. This is deliberately not an identity with lambdaTrim,
whose independent chart windows and trimming still have to be bound. -/
theorem actualBlock_lambda_eq_receiverFiber (B : FixedBlock) (z : ℝ)
    (hz : 0 ≤ z) (w : ℕ) :
    (actualBlock B z).lambdaD w = receiverLambdaFiber B.atom z B.d w :=
  actual_Lambda_eq_receiverFiber B.atom z hz B.d w


/-- Reuse the installed inverse-representative congruence. This bridges
our Bezout phase to the exact ZMod inverse used by the typed E3 source. -/
theorem actual_E3_firstPhase_eq_canonical {B : FixedBlock} {t : Index}
    (ht : t ∈ B.carrier) :
    B.firstPhase t =
      fourier t.h (((((B.atom.residue * ((t.n1 : ℤ) - t.n2) *
        CanonicalReciprocalPhase.wPhaseInverse (t.n2 * t.q * B.d * t.w1)
          (t.n1 * t.w2) : ℤ) : ℝ) / ((t.n1 * t.w2 : ℕ) : ℝ)) : ℝ) :
          UnitAddCircle) := by
  have hclean : B.clean t := (Finset.mem_filter.mp ht).2
  obtain ⟨hq0, hw10, hw20, hn10⟩ := actual_carrier_positive ht
  have hc0 : 0 < t.n1 * t.w2 := Nat.mul_pos hn10 hw20
  letI : NeZero (t.n1 * t.w2) := ⟨hc0.ne'⟩
  obtain ⟨hu, hv, hinv⟩ := E3_clean_inverse_licenses hclean
  have hunit : (t.n2 * t.q * B.d * t.w1).Coprime (t.n1 * t.w2) := by
    simpa only [mul_assoc] using hinv
  have hmod := ActualReciprocalSquarePoissonSourceOnly.canonical_inverse_modEq hunit
  have hmod' : Int.ModEq (t.n1 * t.w2)
      (CanonicalReciprocalPhase.wPhaseInverse (t.n2 * t.q * B.d * t.w1)
        (t.n1 * t.w2))
      (OriginalMediumPhysicalE3Block.inverseResidue (t.n1 * t.w2)
        (t.n2 * t.q * B.d * t.w1)) := by
    simpa only [OriginalSmoothPoissonTail.inverseResidue,
      OriginalMediumPhysicalE3Block.inverseResidue, Int.cast_natCast] using hmod
  have hcircle := CanonicalReciprocalPhase.wPhase_circle_eq_of_modEq hc0
    (hmod'.mul_left (B.atom.residue * ((t.n1 : ℤ) - t.n2)))
  have hF := congrArg (fun z : UnitAddCircle => fourier t.h z) hcircle
  have hfirst : B.firstPhase t =
      fourier t.h (((((B.atom.residue * ((t.n1 : ℤ) - t.n2) *
        OriginalMediumPhysicalE3Block.inverseResidue (t.n1 * t.w2)
          (t.n2 * t.q * B.d * t.w1) : ℤ) : ℝ) /
            ((t.n1 * t.w2 : ℕ) : ℝ)) : ℝ) : UnitAddCircle) := by
    unfold FixedBlock.firstPhase
    simp only [fourier_coe_apply]
    congr 1
    push_cast
    ring
  exact hfirst.trans (by simpa only [mul_assoc] using hF.symm)

/-- The slow phase in the coupled original E3 weight is exactly the
second factor of (21), with no Taylor deletion or extra frequency weight. -/
theorem actual_E3_slowPhase_fourier (B : FixedBlock) (t : Index) :
    fourier t.h ((((B.atom.residue : ℝ) /
      ((t.q * B.d * t.w1 * t.w2 * t.n1 : ℕ) : ℝ)) : ℝ) : UnitAddCircle) =
      Complex.exp (((2 * Real.pi *
        ((B.atom.residue : ℝ) * (t.h : ℝ) /
          ((t.q * B.d * t.w1 * t.w2 * t.n1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  simp only [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Actual constructed CRT phase, now in the typed E3 representatives.
The complete coupled analytic weight and first arithmetic phase can be
used together without an inverse-representative hypothesis. -/
theorem actual_E3_CRT_phase_eq_typed (B : FixedBlock) {t : Index}
    (ht : t ∈ B.carrier) :
    fourier t.h ((((fullPhysicalResidue B t : ℝ) /
      (fullPhysicalL B t : ℝ)) : ℝ) : UnitAddCircle) =
      B.firstPhase t *
        Complex.exp (((2 * Real.pi *
          ((B.atom.residue : ℝ) * (t.h : ℝ) /
            ((t.q * B.d * t.w1 * t.w2 * t.n1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  have hc := actual_E3_CRT_phase_eq21 ht
  have hf := actual_E3_firstPhase_eq_canonical ht
  have hs := actual_E3_slowPhase_fourier B t
  have hfirst : B.firstPhase t =
      fourier t.h ((((B.atom.residue : ℝ) * ((t.n1 : ℝ) - t.n2) *
        CanonicalReciprocalPhase.wPhaseInverse (t.n2 * (t.q * B.d * t.w1))
          (t.n1 * t.w2) / ((t.n1 : ℝ) * t.w2)) : ℝ) : UnitAddCircle) := by
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Nat.cast_mul,
      mul_assoc] using hf
  have hslow :
      fourier t.h ((((B.atom.residue : ℝ) /
        ((t.q : ℝ) * B.d * t.w1 * t.w2 * t.n1)) : ℝ) : UnitAddCircle) =
      Complex.exp (((2 * Real.pi *
        ((B.atom.residue : ℝ) * (t.h : ℝ) /
          ((t.q * B.d * t.w1 * t.w2 * t.n1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    simpa only [Nat.cast_mul] using hs
  rw [← hfirst, hslow] at hc
  exact hc

end ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028
