import ImbalancedChen.P1Full87RealCoprimeGate
import ImbalancedChen.ActualUpperCountingInputs
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The exact manuscript real half-product cutoff T = 2 * N^(1-kappa)
already clears a real sieve endpoint N^theta when
theta <= (1-kappa) * b/(1+b), for every integer N >= 1.
Unlike a natural-ceiling sieve gate, no strict exponent gap or
eventual rounding lemma is required.  The finite RAW/LICENSED full87
physical coprime invoice is then exactly zero for the explicitly
instantiated scale w=N^(epsilon^2), z=N^(19/96), L=N^epsilon,
provided 0<=epsilon<=1/8, b>=1/2 and kappa<=1/4.

This is a genuine instance of the original two policies and original
real half-product source.  It does NOT establish that the frozen final
full87 constructor chooses these precise epsilon/w/z/L/cap parameters,
nor does it pay the signed primitive discrepancy or establish PP licence.
No added assumptions, proof escapes or external analytic proof.
-/

namespace ImbalancedChen.P1Full87RealManuscriptGate

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaRho)

/-- The literal REAL cutoff avoids the strict exponent margin required
to absorb Nat.ceil at a natural sieve endpoint.  The factor 2 in the
manuscript product threshold is not dropped. -/
theorem manuscript_real_endpoint_gate_of_weak_exponent
    {b kappa theta : ℝ} (hb : 0 < b)
    (htheta : theta ≤ (1 - kappa) * (b / (1 + b)))
    (N : ℕ) (hN : 1 ≤ N) :
    0 < manuscriptHalfProductCutoff kappa N ∧
      (N : ℝ) ^ theta ≤
        (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hNreal
  have hpower : 0 < (N : ℝ) ^ (1 - kappa) :=
    Real.rpow_pos_of_pos hNpos _
  have halpha : 0 ≤ b / (1 + b) :=
    div_nonneg hb.le (by linarith)
  constructor
  · change 0 < 2 * (N : ℝ) ^ (1 - kappa)
    exact mul_pos (by norm_num) hpower
  · calc
      (N : ℝ) ^ theta ≤
          (N : ℝ) ^ ((1 - kappa) * (b / (1 + b))) :=
        Real.rpow_le_rpow_of_exponent_le hNreal htheta
      _ = ((N : ℝ) ^ (1 - kappa)) ^ (b / (1 + b)) :=
        Real.rpow_mul hNpos.le _ _
      _ ≤ (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) := by
        apply Real.rpow_le_rpow hpower.le _ halpha
        change (N : ℝ) ^ (1 - kappa) ≤
          2 * (N : ℝ) ^ (1 - kappa)
        linarith

/-- The original bad-product range b>=1/2 and the mild manuscript
product trim kappa<=1/4 leave a STRICT margin above 19/96.
In fact (1-kappa)*b/(1+b) >= 1/4 > 19/96. -/
theorem original_nineteen_over_ninety_six_has_source_margin
    {b kappa : ℝ} (hb : (1 / 2 : ℝ) ≤ b)
    (hkappa : kappa ≤ (1 / 4 : ℝ)) :
    (19 / 96 : ℝ) <
      (1 - kappa) * (b / (1 + b)) := by
  have hden : 0 < 1 + b := by linarith
  have hbeta : (1 / 3 : ℝ) ≤ b / (1 + b) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hb]
  have htrim : (3 / 4 : ℝ) ≤ 1 - kappa := by linarith
  have hquarter : (1 / 4 : ℝ) ≤
      (1 - kappa) * (b / (1 + b)) := by
    calc
      (1 / 4 : ℝ) = (3 / 4) * (1 / 3) := by norm_num
      _ ≤ (1 - kappa) * (b / (1 + b)) :=
        mul_le_mul htrim hbeta (by norm_num) (by linarith)
  exact (by norm_num : (19 / 96 : ℝ) < 1 / 4).trans_le hquarter

/-- The explicit compact attachment precision is below the frozen
nineteen-over-ninety-six rough upper cutoff, without assuming an
unrelated physical modulus cap. -/
private theorem compact_precision_square_le_nineteen_over_ninety_six
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilon8 : epsilon ≤ (1 / 8 : ℝ)) :
    epsilon ^ 2 ≤ (19 / 96 : ℝ) := by
  have hone : epsilon ≤ (1 : ℝ) :=
    hepsilon8.trans (by norm_num)
  have hsquare : epsilon ^ 2 ≤ epsilon := by
    nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr hone)]
  exact hsquare.trans (hepsilon8.trans (by norm_num))

/-- The same exact full87 original RAW/LICENSED physical difference,
at the literal N^(epsilon^2), N^(19/96), N^epsilon attachment,
has zero real-source coprime correction for every N>=1.
The real T-gate and w<=z are now PROVED, not hypothesis fields. -/
theorem actual_full87_manuscript_coprime_correction_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b kappa epsilon : ℝ) (N cap : ℕ)
    (hN : 1 ≤ N) (hb : (1 / 2 : ℝ) ≤ b)
    (hkappa : kappa ≤ (1 / 4 : ℝ))
    (hepsilon : 0 ≤ epsilon) (hepsilon8 : epsilon ≤ (1 / 8 : ℝ)) :
    let w := (N : ℝ) ^ (epsilon ^ 2)
    let z := (N : ℝ) ^ (19 / 96 : ℝ)
    let L := (N : ℝ) ^ epsilon
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    let Q := actualSmallRoughModuli (S false) N cap w z ∪
      actualSmallRoughModuli (R false) N cap w z
    let rho := trueDDeltaRho (R false) (S false) N cap w z L
    realPhysicalCoprimeCorrection b N
      (manuscriptHalfProductCutoff kappa N) Q rho = 0 := by
  dsimp only
  have hbpos : 0 < b :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hb
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hwz : (N : ℝ) ^ (epsilon ^ 2) ≤
      (N : ℝ) ^ (19 / 96 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNreal
      (compact_precision_square_le_nineteen_over_ninety_six hepsilon hepsilon8)
  obtain ⟨hT, hgate⟩ :=
    manuscript_real_endpoint_gate_of_weak_exponent hbpos
      (original_nineteen_over_ninety_six_has_source_margin hb hkappa).le N hN
  exact P1Full87RealCoprimeGate.actual_full87_delta_real_coprime_correction_zero
    delta n e q om b N cap
    ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
    ((N : ℝ) ^ epsilon) (manuscriptHalfProductCutoff kappa N)
    hbpos hT hwz hgate

/-- Real half-product receiver: no coprime term and one HIGH-d
primitive discrepancy invoice.  This is exact finite arithmetic
for the two ORIGINAL policies; no positive-majorant or analytic
H_N estimate is asserted for their signed difference. -/
theorem actual_full87_manuscript_receiver_high_primitive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b kappa epsilon : ℝ) (N cap : ℕ)
    (hN : 1 ≤ N) (hb : (1 / 2 : ℝ) ≤ b)
    (hkappa : kappa ≤ (1 / 4 : ℝ))
    (hepsilon : 0 ≤ epsilon) (hepsilon8 : epsilon ≤ (1 / 8 : ℝ)) :
    let w := (N : ℝ) ^ (epsilon ^ 2)
    let z := (N : ℝ) ^ (19 / 96 : ℝ)
    let L := (N : ℝ) ^ epsilon
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    let Q := actualSmallRoughModuli (S false) N cap w z ∪
      actualSmallRoughModuli (R false) N cap w z
    let high := Q.filter (fun d => w ^ 5 ≤ (d : ℝ))
    let rho := trueDDeltaRho (R false) (S false) N cap w z L
    (∑ m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N),
      physicalDivisorSum Q rho (N - m)) =
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) *
          physicalDensitySum high rho +
        realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
          high rho ∧
    |(∑ m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N),
          physicalDivisorSum Q rho (N - m)) -
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) *
        physicalDensitySum high rho| ≤
      ∑ d ∈ high,
        |realHalfProductCongruenceMass b N (manuscriptHalfProductCutoff kappa N) d -
          realHalfProductCoprimeMass b N (manuscriptHalfProductCutoff kappa N) d /
            (Nat.totient d : ℝ)| := by
  dsimp only
  have hbpos : 0 < b :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hb
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hepsR :=
    compact_precision_square_le_nineteen_over_ninety_six hepsilon hepsilon8
  have hwz : (N : ℝ) ^ (epsilon ^ 2) ≤
      (N : ℝ) ^ (19 / 96 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNreal hepsR
  have hw : (1 : ℝ) ≤ (N : ℝ) ^ (epsilon ^ 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hNreal (sq_nonneg epsilon)
    simpa using h
  obtain ⟨hT, hgate⟩ :=
    manuscript_real_endpoint_gate_of_weak_exponent hbpos
      (original_nineteen_over_ninety_six_has_source_margin hb hkappa).le N hN
  exact P1Full87RealCoprimeGate.actual_full87_real_receiver_high_only_primitive
    delta n e q om b N cap
    ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
    ((N : ℝ) ^ epsilon) (manuscriptHalfProductCutoff kappa N)
    hw hwz hbpos hT hgate

end
end ImbalancedChen.P1Full87RealManuscriptGate
