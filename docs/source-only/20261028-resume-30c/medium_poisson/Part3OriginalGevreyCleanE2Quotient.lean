import ImbalancedChen.Part3OriginalGevreySharedRowDictionary
import ImbalancedChen.Part3ActualSeparatedRowFiniteMatcher
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.

Exact gcd partition and quotient reindex of the actual Gevrey physical
paired row. The old finite matcher is polymorphic in its payload, so its
arithmetic bijection is reused with the current paperPsi Fourier packet,
actualPsiQWeight and unchanged alpha/gamma coefficients. No old dyadic bump
or low-pass multiplier occurs in this payload. The time-domain m weight
remains paperMWeight from the preceding actual W dictionary.

The separate clean phase lemma proves manuscript equation (21) from the
literal inverse licenses. A general normalized original row need not have
those clean licenses: it is not silently thrown away or declared clean.
The full general-D/root packet remains necessary on the other branches.
-/

noncomputable section
open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalPhysicalGevreyFrequencyScale20261028
open ImbalancedChen.Part3.OriginalPhysicalPoissonTruncation20261028
open ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter

namespace ImbalancedChen.Part3.OriginalGevreyCleanE2Quotient20261028

open GeneralDGateNormalization

/-- The physical gcd is D; delta=gcd(r,D), q=D/delta and t=s/q.
These definitions are exactly the installed arithmetic matcher's data. -/
def delta (r D : ℕ) : ℕ := r.gcd D

def w1 (r D t : ℕ) : ℕ := reducedLeft r D * t

def w2 (w D : ℕ) : ℕ := w / D

def normalizedL (p r w D t : ℕ) : ℕ := (p * D) * w1 r D t * w2 w D

def originalL (p r w s : ℕ) : ℕ := (p * (r * s)).lcm (p * w)

def originalResidue (d : MediumAtom) (p r w N1 N2 s : ℕ) : ℤ :=
  ComplexCRT.residue (p * (r * s)) (p * w) N1 N2 d.residue

def dWindow (d : MediumAtom) (x : ℝ) (D : ℕ) : ℕ :=
  physicalH (Real.log x ^ 5) d.Q1 d.Q3 d.Q2 d.V D

def originalGevreyPayload (d : MediumAtom) (x : ℝ)
    (p r w D N1 N2 s : ℕ) : ℂ :=
  d.gamma2 s *
    ∑ h ∈ signedWindow (dWindow d x D),
      paperPsiNonzeroMode (d.V / (originalL p r w s : ℝ))
        ((originalResidue d p r w N1 N2 s : ℝ) / (originalL p r w s : ℝ)) h

def normalizedGevreyPayload (d : MediumAtom) (x : ℝ)
    (p r w D N1 N2 t : ℕ) : ℂ :=
  d.gamma2 (quotient r D * t) *
    ∑ h ∈ signedWindow (dWindow d x D),
      paperPsiNonzeroMode (d.V / (normalizedL p r w D t : ℝ))
        ((originalResidue d p r w N1 N2 (quotient r D * t) : ℝ) /
          (normalizedL p r w D t : ℝ)) h

/-- The normalized modulus is the same complete physical lcm on the
actual quotient carrier, rather than a replacement support level. -/
theorem actual_normalized_payload_eq {d : MediumAtom} {x : ℝ}
    {p r w D N1 N2 t : ℕ} (hr : 0 < r) (hD : 0 < D) (hDw : D ∣ w)
    (ho : outerGate p r w D N1 N2)
    (ht : t ∈ normalizedCarrier (factorCarrier d.Q2) r w D N1) :
    originalGevreyPayload d x p r w D N1 N2 (quotient r D * t) =
      normalizedGevreyPayload d x p r w D N1 N2 t := by
  have hq := (quotient_data hr hD).1
  have hunit := ((mem_normalizedCarrier hq).mp ht).2
  have hL := normalized_lcm hr hD hDw ho hunit
  simpa only [originalGevreyPayload, normalizedGevreyPayload,
    originalL, normalizedL, w1, w2, hL]

/-- Cost-one exact reindex: no rounding, Cartesian completion, endpoint
extension, absolute values or change to the actual paperPsi payload. -/
theorem actual_D_row_quotient_reindex (d : MediumAtom) (x : ℝ)
    {p r w D N1 N2 : ℕ} (hr : 0 < r) (hD : 0 < D) (hDw : D ∣ w) :
    (∑ s ∈ factorCarrier d.Q2,
      if originalGate p r w D N1 N2 s then
        originalGevreyPayload d x p r w D N1 N2 s else 0) =
      if outerGate p r w D N1 N2 then
        ∑ t ∈ normalizedCarrier (factorCarrier d.Q2) r w D N1,
          normalizedGevreyPayload d x p r w D N1 N2 t
      else 0 := by
  rw [sum_gate_reindex hr hD hDw]
  by_cases ho : outerGate p r w D N1 N2
  · simp only [if_pos ho]
    apply Finset.sum_congr rfl
    intro t ht
    exact actual_normalized_payload_eq hr hD hDw ho ht
  · simp only [if_neg ho]

/-- qWeight and all external original paired coefficients are retained
before and after quotienting the varying original s label. -/
def fixedCoefficient (d : MediumAtom) (p r r' s' N1 N2 : ℕ) : ℂ :=
  actualPsiQWeight d p * d.gamma3 r * star (d.gamma2 s' * d.gamma3 r') *
    d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2)

def actualDRow (d : MediumAtom) (x : ℝ) (p r r' s' D N1 N2 : ℕ) : ℂ :=
  fixedCoefficient d p r r' s' N1 N2 *
    ∑ s ∈ factorCarrier d.Q2,
      if originalGate p r (r' * s') D N1 N2 s then
        originalGevreyPayload d x p r (r' * s') D N1 N2 s else 0

theorem actualDRow_eq_quotient (d : MediumAtom) (x : ℝ)
    {p r r' s' D N1 N2 : ℕ}
    (hr : 0 < r) (hD : 0 < D) (hDw : D ∣ r' * s') :
    actualDRow d x p r r' s' D N1 N2 =
      fixedCoefficient d p r r' s' N1 N2 *
        (if outerGate p r (r' * s') D N1 N2 then
          ∑ t ∈ normalizedCarrier (factorCarrier d.Q2) r (r' * s') D N1,
            normalizedGevreyPayload d x p r (r' * s') D N1 N2 t
        else 0) := by
  exact congrArg (fun z : ℂ => fixedCoefficient d p r r' s' N1 N2 * z)
    (actual_D_row_quotient_reindex d x hr hD hDw)

/-- This is the prior batch's same actual retained physical row on the
selected gcd branch. The m majorant therefore remains paperMWeight. -/
theorem payload_eq_previous_actual_row (d : MediumAtom) (x : ℝ)
    {p r r' s s' D N1 N2 : ℕ}
    (hD : (r * s).gcd (r' * s') = D)
    (hc : ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2) :
    originalGevreyPayload d x p r (r' * s') D N1 N2 s =
      d.gamma2 s * rowRetained d x p ((s,r),N1) ((s',r'),N2) := by
  have hc' : pairCompatible p ((s,r),N1) ((s',r'),N2) := by
    simpa only [pairCompatible, tailProduct, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hc
  simp only [rowRetained, if_pos hc', rowWindow, tailGcd, tailProduct]
  have hD' : (s * r).gcd (s' * r') = D := by
    simpa only [Nat.mul_comm] using hD
  rw [hD']
  simp only [originalGevreyPayload, originalL, originalResidue, completeModulus,
    pairResidue, tailProduct, dWindow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Finite complete ownership of the actual D values for this original
s carrier. Reindexing by D does not require a guessed universal D box. -/
def gcdCarrier (d : MediumAtom) (r w : ℕ) : Finset ℕ :=
  (factorCarrier d.Q2).image (fun s => (r * s).gcd w)

theorem exact_gcd_partition (d : MediumAtom) (p r w N1 N2 : ℕ)
    (F : ℕ → ℂ) :
    (∑ s ∈ factorCarrier d.Q2,
      if ComplexCRT.Compatible (p * (r * s)) (p * w) N1 N2 then F s else 0) =
      ∑ D ∈ gcdCarrier d r w, ∑ s ∈ factorCarrier d.Q2,
        if originalGate p r w D N1 N2 s then F s else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hm : (r * s).gcd w ∈ gcdCarrier d r w :=
    Finset.mem_image.mpr ⟨s, hs, rfl⟩
  symm
  rw [Finset.sum_eq_single ((r * s).gcd w)]
  · simp [originalGate]
  · intro D hD hne
    have hg : (r * s).gcd w ≠ D := Ne.symm hne
    simp only [originalGate, hg, false_and, if_false]
  · intro hnot
    exact (hnot hm).elim

/-! The exact clean two-inverse identity of manuscript equation (21). -/

open CanonicalReciprocalPhase

private theorem clean_phase_numerator_dvd {A B n m : ℕ}
    (hAnB : (n * B).Coprime A) (hmA_B : (m * A).Coprime B)
    (hmA_nB : (m * A).Coprime (n * B)) :
    let u := wPhaseInverse (n * B) A
    let v := wPhaseInverse (m * A) B
    let t := wPhaseInverse (m * A) (n * B)
    ((A * (n * B) : ℕ) : ℤ) ∣
      u * B * n + v * A * n - (A : ℤ) * ((n : ℤ) - m) * t - 1 := by
  dsimp only
  let u := wPhaseInverse (n * B) A
  let v := wPhaseInverse (m * A) B
  let t := wPhaseInverse (m * A) (n * B)
  let E : ℤ := u * B * n + v * A * n - (A : ℤ) * ((n : ℤ) - m) * t - 1
  have hu := wPhaseInverse_spec hAnB
  have hv := wPhaseInverse_spec hmA_B
  have ht := wPhaseInverse_spec hmA_nB
  have htB : Int.ModEq B (((m * A : ℕ) : ℤ) * t) 1 :=
    ht.of_dvd (by exact_mod_cast (dvd_mul_left B n : B ∣ n * B))
  have htv : Int.ModEq B t v := by
    have h1 := hv.mul_right t
    have h2 := htB.mul_right v
    simpa only [mul_assoc, mul_comm, mul_left_comm, one_mul] using
      h1.symm.trans h2
  obtain ⟨ku, hku⟩ := hu.dvd
  obtain ⟨kt, hkt⟩ := ht.dvd
  obtain ⟨kv, hkv⟩ := htv.dvd
  have hAE : (A : ℤ) ∣ E := by
    refine ⟨-ku + v * n - ((n : ℤ) - m) * t, ?_⟩
    dsimp only [E]
    push_cast at hku
    linear_combination -hku
  have hnBE : ((n * B : ℕ) : ℤ) ∣ E := by
    refine ⟨u + (A : ℤ) * kv - kt, ?_⟩
    dsimp only [E]
    push_cast at hkt ⊢
    linear_combination -hkt + (A : ℤ) * n * hkv
  have hboth := Int.coe_lcm_dvd_iff.mpr ⟨hAE, hnBE⟩
  simpa only [Int.lcm, Int.natAbs_natCast, hAnB.symm.lcm_eq_mul] using hboth

/-- The actual inverse arithmetic identity behind (21), valid for every
signed a and Fourier frequency h. Here A=q*d*w1 and B=w2. The clean unit
licenses are explicit; they are not asserted for every general-D row. -/
theorem clean_two_inverse_phase_eq21 {A B n m : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hn : 0 < n)
    (hAnB : (n * B).Coprime A) (hmA_B : (m * A).Coprime B)
    (hmA_nB : (m * A).Coprime (n * B)) (a h : ℤ) :
    fourier h (((((a : ℝ) * wPhaseInverse (n * B) A / A) +
      (a : ℝ) * wPhaseInverse (m * A) B / B) : ℝ) : UnitAddCircle) =
      fourier h ((((a : ℝ) * ((n : ℝ) - m) *
        wPhaseInverse (m * A) (n * B) / ((n : ℝ) * B)) : ℝ) : UnitAddCircle) *
      fourier h ((((a : ℝ) / ((A : ℝ) * B * n)) : ℝ) : UnitAddCircle) := by
  let u := wPhaseInverse (n * B) A
  let v := wPhaseInverse (m * A) B
  let t := wPhaseInverse (m * A) (n * B)
  have hdiv := clean_phase_numerator_dvd hAnB hmA_B hmA_nB
  change ((A * (n * B) : ℕ) : ℤ) ∣
    u * B * n + v * A * n - (A : ℤ) * ((n : ℤ) - m) * t - 1 at hdiv
  have hmod : Int.ModEq (A * (n * B) : ℕ)
      (a * (u * B * n + v * A * n))
      (a * ((A : ℤ) * ((n : ℤ) - m) * t + 1)) := by
    apply Int.modEq_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨-a * k, ?_⟩
    linear_combination -a * hk
  have hc := wPhase_circle_eq_of_modEq
    (Nat.mul_pos hA (Nat.mul_pos hn hB)) hmod
  have hAr : (A : ℝ) ≠ 0 := by positivity
  have hBr : (B : ℝ) ≠ 0 := by positivity
  have hnr : (n : ℝ) ≠ 0 := by positivity
  have hleft :
      (((a * (u * B * n + v * A * n) : ℤ) : ℝ) /
        ((A * (n * B) : ℕ) : ℝ)) =
      (a : ℝ) * u / A + (a : ℝ) * v / B := by
    push_cast
    field_simp [hAr, hBr, hnr]
    ring
  have hright :
      (((a * ((A : ℤ) * ((n : ℤ) - m) * t + 1) : ℤ) : ℝ) /
        ((A * (n * B) : ℕ) : ℝ)) =
      (a : ℝ) * ((n : ℝ) - m) * t / ((n : ℝ) * B) +
        (a : ℝ) / ((A : ℝ) * B * n) := by
    push_cast
    field_simp [hAr, hBr, hnr]
    ring
  rw [hleft, hright] at hc
  have hF := congrArg (fun z : UnitAddCircle => fourier h z) hc
  simpa only [u, v, t, fourier_apply, AddCircle.coe_add, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul] using hF


/-- The original left physical modulus, expressed in the actual quotient
coordinates. This equality precedes all clean inverse licenses. -/
theorem actual_left_modulus_quotient {p r D t : ℕ}
    (hr : 0 < r) (hD : 0 < D) :
    p * (r * (quotient r D * t)) = (p * D) * w1 r D t := by
  obtain ⟨hq, hr0, hcop, hDfact, hrfact⟩ := quotient_data hr hD
  calc
    _ = p * ((r.gcd D * reducedLeft r D) * (quotient r D * t)) := by
      rw [hrfact]
    _ = (p * (r.gcd D * quotient r D)) * (reducedLeft r D * t) := by ring
    _ = _ := by rw [hDfact]; rfl

/-- Explicit clean gates on the normalized actual row imply every inverse
license of (21). The source outerGate and inner unit mask alone are not
claimed to imply the two additional clean gates. -/
theorem actual_clean_inverse_licenses {d : MediumAtom}
    {p r w D N1 N2 t : ℕ} (hr : 0 < r) (hD : 0 < D) (hDw : D ∣ w)
    (ho : outerGate p r w D N1 N2)
    (ht : t ∈ normalizedCarrier (factorCarrier d.Q2) r w D N1)
    (hclean : ((p * D) * w1 r D t).Coprime (w2 w D))
    (hN12 : N1.Coprime N2) :
    (N1 * w2 w D).Coprime ((p * D) * w1 r D t) ∧
      (N2 * ((p * D) * w1 r D t)).Coprime (w2 w D) ∧
      (N2 * ((p * D) * w1 r D t)).Coprime (N1 * w2 w D) := by
  have hq := (quotient_data hr hD).1
  have hunit := ((mem_normalizedCarrier hq).mp ht).2
  have hg : originalGate p r w D N1 N2 (quotient r D * t) :=
    (originalGate_iff hr hD hDw).mpr
      ⟨dvd_mul_right _ _, ho, by simpa only [Nat.mul_div_cancel_left t hq] using hunit⟩
  have hN1A : N1.Coprime ((p * D) * w1 r D t) := by
    have h := hg.2.1
    rwa [actual_left_modulus_quotient hr hD] at h
  have hBdiv : w2 w D ∣ p * w := by
    refine ⟨p * D, ?_⟩
    dsimp only [w2]
    have hwfact : D * (w / D) = w := Nat.mul_div_cancel' hDw
    calc
      p * w = p * (D * (w / D)) := by rw [hwfact]
      _ = (w / D) * (p * D) := by ring
  have hN2B : N2.Coprime (w2 w D) := hg.2.2.1.of_dvd_right hBdiv
  refine ⟨Nat.coprime_mul_iff_left.mpr ⟨hN1A, hclean.symm⟩,
    Nat.coprime_mul_iff_left.mpr ⟨hN2B, hclean⟩, ?_⟩
  exact Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_right.mpr ⟨hN12.symm, hN2B⟩,
      Nat.coprime_mul_iff_right.mpr ⟨hN1A.symm, hclean⟩⟩

/-- Equation (21) on the normalized physical clean branch, with
A=p*D*w1, B=w2, n=N1 and m=N2, and all integer h signs retained. -/
theorem actual_normalized_clean_phase_eq21 {d : MediumAtom}
    {p r w D N1 N2 t : ℕ} (hp : 0 < p) (hr : 0 < r)
    (hw : 0 < w) (hD : 0 < D) (hDw : D ∣ w) (hN1 : 0 < N1)
    (ho : outerGate p r w D N1 N2)
    (ht : t ∈ normalizedCarrier (factorCarrier d.Q2) r w D N1)
    (ht0 : 0 < t)
    (hclean : ((p * D) * w1 r D t).Coprime (w2 w D))
    (hN12 : N1.Coprime N2) (a h : ℤ) :
    let A := (p * D) * w1 r D t
    let B := w2 w D
    fourier h (((((a : ℝ) * wPhaseInverse (N1 * B) A / A) +
      (a : ℝ) * wPhaseInverse (N2 * A) B / B) : ℝ) : UnitAddCircle) =
      fourier h ((((a : ℝ) * ((N1 : ℝ) - N2) *
        wPhaseInverse (N2 * A) (N1 * B) / ((N1 : ℝ) * B)) : ℝ) : UnitAddCircle) *
      fourier h ((((a : ℝ) / ((A : ℝ) * B * N1)) : ℝ) : UnitAddCircle) := by
  dsimp only
  have hA : 0 < (p * D) * w1 r D t :=
    Nat.mul_pos (Nat.mul_pos hp hD) (Nat.mul_pos (quotient_data hr hD).2.1 ht0)
  have hB : 0 < w2 w D := Nat.div_pos (Nat.le_of_dvd hw hDw) hD
  obtain ⟨hu, hv, htinv⟩ := actual_clean_inverse_licenses hr hD hDw ho ht hclean hN12
  exact clean_two_inverse_phase_eq21 hA hB hN1 hu hv htinv a h


/-- The two inverse phases are the actual constructed CRT residue, not
an assumed phase representation. The clean factors A and B are coprime,
while the original two complete moduli may still share p*D. -/
theorem clean_CRT_circle_eq_two_inverse {A B N1 N2 : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A.Coprime B)
    (hN1BA : (N1 * B).Coprime A) (hN2AB : (N2 * A).Coprime B)
    (a b : ℤ) (hbA : Int.ModEq A (b * N1) a)
    (hbB : Int.ModEq B (b * N2) a) :
    ((((b : ℝ) / ((A : ℝ) * B)) : ℝ) : UnitAddCircle) =
      ((((a : ℝ) * wPhaseInverse (N1 * B) A / A) +
        (a : ℝ) * wPhaseInverse (N2 * A) B / B) : ℝ) := by
  let u := wPhaseInverse (N1 * B) A
  let v := wPhaseInverse (N2 * A) B
  let b0 : ℤ := a * (u * B + v * A)
  have hu := wPhaseInverse_spec hN1BA
  have hv := wPhaseInverse_spec hN2AB
  have hbu : Int.ModEq A b (a * u * B) := by
    have hx := hu.mul_left b
    have hy := hbA.mul_right (u * B)
    exact (by simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm,
      mul_one] using hx.symm).trans
        (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hy)
  have hb0A : Int.ModEq A b0 (a * u * B) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-a * v, ?_⟩
    dsimp [b0]
    ring
  have hbv : Int.ModEq B b (a * v * A) := by
    have hx := hv.mul_left b
    have hy := hbB.mul_right (v * A)
    exact (by simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm,
      mul_one] using hx.symm).trans
        (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hy)
  have hb0B : Int.ModEq B b0 (a * v * A) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-a * u, ?_⟩
    dsimp [b0]
    ring
  have hboth : Int.ModEq (A * B : ℕ) b b0 := by
    apply (Int.modEq_and_modEq_iff_modEq_mul
      (by simpa only [Int.natAbs_natCast] using hAB :
        (A : ℤ).natAbs.Coprime (B : ℤ).natAbs)).mp
    exact ⟨hbu.trans hb0A.symm, hbv.trans hb0B.symm⟩
  have hc := wPhase_circle_eq_of_modEq (Nat.mul_pos hA hB) hboth
  have hAr : (A : ℝ) ≠ 0 := by positivity
  have hBr : (B : ℝ) ≠ 0 := by positivity
  have hfrac : (b0 : ℝ) / ((A : ℝ) * B) =
      (a : ℝ) * u / A + (a : ℝ) * v / B := by
    dsimp [b0]
    push_cast
    field_simp [hAr, hBr]
    ring
  simpa only [Nat.cast_mul, hfrac, u, v] using hc

/-- Actual physical CRT phase of the quotient row equals the right side
of (21). This is the original retained slow factor, not its removal. -/
theorem actual_CRT_phase_eq21 {d : MediumAtom}
    {p r w D N1 N2 t : ℕ} (hp : 0 < p) (hr : 0 < r)
    (hw : 0 < w) (hD : 0 < D) (hDw : D ∣ w) (hN1 : 0 < N1)
    (ho : outerGate p r w D N1 N2)
    (ht : t ∈ normalizedCarrier (factorCarrier d.Q2) r w D N1)
    (ht0 : 0 < t)
    (hclean : ((p * D) * w1 r D t).Coprime (w2 w D))
    (hN12 : N1.Coprime N2) (h : ℤ) :
    let A := (p * D) * w1 r D t
    let B := w2 w D
    fourier h ((((originalResidue d p r w N1 N2 (quotient r D * t) : ℝ) /
      (normalizedL p r w D t : ℝ)) : ℝ) : UnitAddCircle) =
      fourier h ((((d.residue : ℝ) * ((N1 : ℝ) - N2) *
        wPhaseInverse (N2 * A) (N1 * B) / ((N1 : ℝ) * B)) : ℝ) : UnitAddCircle) *
      fourier h ((((d.residue : ℝ) / ((A : ℝ) * B * N1)) : ℝ) : UnitAddCircle) := by
  dsimp only
  have hq := (quotient_data hr hD).1
  have hunit := ((mem_normalizedCarrier hq).mp ht).2
  have hg : originalGate p r w D N1 N2 (quotient r D * t) :=
    (originalGate_iff hr hD hDw).mpr
      ⟨dvd_mul_right _ _, ho, by simpa only [Nat.mul_div_cancel_left t hq] using hunit⟩
  have hb := ComplexCRT.residue_spec d.residue hg.2
  have hleft := actual_left_modulus_quotient (p := p) (t := t) hr hD
  have hbA : Int.ModEq ((p * D) * w1 r D t)
      (originalResidue d p r w N1 N2 (quotient r D * t) * N1) d.residue := by
    simpa only [originalResidue, hleft] using hb.1
  have hBdiv : w2 w D ∣ p * w := by
    refine ⟨p * D, ?_⟩
    dsimp only [w2]
    have hwfact : D * (w / D) = w := Nat.mul_div_cancel' hDw
    calc
      p * w = p * (D * (w / D)) := by rw [hwfact]
      _ = (w / D) * (p * D) := by ring
  have hbB : Int.ModEq (w2 w D)
      (originalResidue d p r w N1 N2 (quotient r D * t) * N2) d.residue := by
    simpa only [originalResidue] using
      hb.2.1.of_dvd (by exact_mod_cast hBdiv)
  have hA : 0 < (p * D) * w1 r D t :=
    Nat.mul_pos (Nat.mul_pos hp hD) (Nat.mul_pos (quotient_data hr hD).2.1 ht0)
  have hB : 0 < w2 w D := Nat.div_pos (Nat.le_of_dvd hw hDw) hD
  obtain ⟨hu, hv, hinv⟩ := actual_clean_inverse_licenses hr hD hDw ho ht hclean hN12
  have hcircle := clean_CRT_circle_eq_two_inverse hA hB hclean hu hv
    d.residue (originalResidue d p r w N1 N2 (quotient r D * t)) hbA hbB
  have hFourier := congrArg (fun z : UnitAddCircle => fourier h z) hcircle
  have heq := clean_two_inverse_phase_eq21 hA hB hN1 hu hv hinv d.residue h
  calc
    _ = fourier h (((((d.residue : ℝ) *
          wPhaseInverse (N1 * w2 w D) ((p * D) * w1 r D t) /
            ((p * D) * w1 r D t)) +
          (d.residue : ℝ) * wPhaseInverse (N2 * ((p * D) * w1 r D t)) (w2 w D) /
            (w2 w D)) : ℝ) : UnitAddCircle) := by
      simpa only [normalizedL, Nat.cast_mul] using hFourier
    _ = _ := heq


/-- The original retained row has its own actual gcd-dependent window;
it is not first replaced by a common larger frequency carrier. -/
def fullOriginalRow (d : MediumAtom) (x : ℝ) (p r r' s' N1 N2 : ℕ) : ℂ :=
  fixedCoefficient d p r r' s' N1 N2 *
    ∑ s ∈ factorCarrier d.Q2,
      if ComplexCRT.Compatible (p * (r * s)) (p * (r' * s')) N1 N2 then
        originalGevreyPayload d x p r (r' * s') ((r * s).gcd (r' * s')) N1 N2 s
      else 0

/-- Exact ownership of the varying window by its D branch, with all
same-rho coefficients and both frequency signs kept before quotienting. -/
theorem fullOriginalRow_eq_D_rows (d : MediumAtom) (x : ℝ)
    (p r r' s' N1 N2 : ℕ) :
    fullOriginalRow d x p r r' s' N1 N2 =
      ∑ D ∈ gcdCarrier d r (r' * s'), actualDRow d x p r r' s' D N1 N2 := by
  unfold fullOriginalRow
  rw [exact_gcd_partition d p r (r' * s') N1 N2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  unfold actualDRow
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hg : originalGate p r (r' * s') D N1 N2 s
  · simp only [if_pos hg]
    rw [hg.1]
  · simp only [if_neg hg]

/-- Actual full retained physical row to its quotient rows. Positivity
and D|right-tail are derived on every owned gcd value, including the
actual window. There is no independently supplied quotient cover. -/
theorem fullOriginalRow_eq_quotient_rows (d : MediumAtom) (x : ℝ)
    {p r r' s' N1 N2 : ℕ} (hr : 0 < r) (hQ2 : 1 ≤ d.Q2) :
    fullOriginalRow d x p r r' s' N1 N2 =
      ∑ D ∈ gcdCarrier d r (r' * s'),
        fixedCoefficient d p r r' s' N1 N2 *
          (if outerGate p r (r' * s') D N1 N2 then
            ∑ t ∈ normalizedCarrier (factorCarrier d.Q2) r (r' * s') D N1,
              normalizedGevreyPayload d x p r (r' * s') D N1 N2 t
          else 0) := by
  rw [fullOriginalRow_eq_D_rows]
  apply Finset.sum_congr rfl
  intro D hD
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hD
  have hs0 : 0 < s := by
    have hlo := (Finset.mem_Icc.mp hs).1
    have hc : 1 ≤ Nat.ceil d.Q2 := by exact_mod_cast hQ2.trans (Nat.le_ceil d.Q2)
    omega
  exact actualDRow_eq_quotient d x hr
    (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hr hs0)) (Nat.gcd_dvd_right _ _)

end ImbalancedChen.Part3.OriginalGevreyCleanE2Quotient20261028
