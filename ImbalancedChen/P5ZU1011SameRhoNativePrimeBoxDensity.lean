import ImbalancedChen.P5ZU1011SameRhoNativePrimeMeanTransport
import ImbalancedChen.P5ZU1011JointNearCapPrimeReserve
import ImbalancedChen.ActualRosserUpperGeneralLimit

/-!
# Literal same-rho native density on the original joint primebox

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The reciprocal-totient main of the actual joint physical sigma is exactly
the actual original four-prime weighted box sum of its OWN cell-static
Rosser density. The low-fourth band stays unmasked and the high band has
the original E complement. No desired H248 or currentK density is an input.

Every certified actual rational box has positive cutoff and residual and
true ratio>1. The existing all-residual ordinary Rosser theorem therefore
gives that cell's literal normalized density limit, with the genuine
Suzuki upper factor. This is an ordinary-density result; it is NOT a
licence identifying this coefficient with a different enhanced table.
-/

namespace ImbalancedChen.P5Z.U1011SameRhoNativePrimeBoxDensity

noncomputable section

open Set Classical Filter Topology
open scoped BigOperators
open MathlibNt.SieveTheory
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy tupleTag selectedPolicy ownerBox)
open U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenJointNearCapModulusConvolution
open U1011SameRhoNativePrimeMeanTransport
open P5U1011JointOverlap

def cellDensity (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : ℝ :=
  actualSmallRosserPlusDensity N (Nat.ceil (rowZ p B eta N))
    (rowZ p B eta N) (rowD p B eta N)

def ownerDensity (n N : ℕ) (eta : ℚ) (v : LogFour) : ℝ :=
  let B := gridBox n (owner n v)
  cellDensity (boxPolicy B) B eta N

def ordinaryKeep (n N : ℕ) (t : Four) : Prop := tupleTag n N t ≠ 0

theorem ownerDensity_at_native_tuple (n N : ℕ) (eta : ℚ) (t : Four) :
    ownerDensity n N eta (coordinates N t) =
      actualSmallRosserPlusDensity N (Nat.ceil (Z n N eta t)) (Z n N eta t) (D n N eta t) := rfl

/-- Actual lowered-cutoff coprimality is proved at every native row
before phi(b*d) is separated. Full-prefix primes are never discarded. -/
theorem native_row_reciprocalTotient_density {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ ordinaryTuples n N E) :
    (∑ d ∈ support n N eta t, coefficient n N eta t d *
      (1 / (Nat.totient (fullPrefix t * d) : ℝ))) =
        ownerDensity n N eta (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) := by
  have hs := (Finset.mem_filter.mp ht).1
  have hlegal := compiled_legality hN heta ht
  have hz : Z n N eta t ≤ (slots t 3 : ℝ) := by
    simpa only [slots, Matrix.cons_val_three] using hlegal.2.2.1
  have hb := fullPrefix_coprime_lowered_sieve hs hz
  rw [ownerDensity_at_native_tuple]
  simp only [actualSmallRosserPlusDensity, reciprocalTotientDensity, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ sieveProduct N (Nat.ceil (Z n N eta t)) := by
    have hd' := (Nat.mem_divisors.mp hd).1
    rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N _ _ (Nat.le_ceil _)] at hd'
  have hcop := chenQuotient_allowed_coprime hb hdvd
  change coefficient n N eta t d * (1 / (Nat.totient (fullPrefix t * d) : ℝ)) =
    coefficient n N eta t d / (Nat.totient d : ℝ) / (Nat.totient (fullPrefix t) : ℝ)
  rw [Nat.totient_mul hcop, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The physical coefficient's OWN reciprocal-totient density is exactly
the original ordinary-selected harmonic prime sum, at every fixed mesh
and precision. No asymptotic or table-density premise is used. -/
theorem physicalDensity_eq_actual_native_harmonic {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    physicalDensitySum (modulusSupport n N eta E) (sigma n N eta E) =
      JointNearCapPrimeReserve.jointMass N E (ordinaryKeep n N) (ownerDensity n N eta) := by
  have hp := exact_pushforward n N eta E (fun q => 1 / (Nat.totient q : ℝ))
  have hsum : (∑ t ∈ ordinaryTuples n N E,
      ∑ d ∈ support n N eta t, coefficient n N eta t d *
        (1 / (Nat.totient (fullPrefix t * d) : ℝ))) =
      ∑ t ∈ ordinaryTuples n N E,
        ownerDensity n N eta (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact native_row_reciprocalTotient_density hN heta ht
  have hD : (∑ q ∈ modulusSupport n N eta E, sigma n N eta E q *
      (1 / (Nat.totient q : ℝ))) =
      physicalDensitySum (modulusSupport n N eta E) (sigma n N eta E) := by
    simp only [physicalDensitySum, div_eq_mul_inv, one_mul]
  rw [hD, hsum] at hp
  rw [← hp]
  simp only [JointNearCapPrimeReserve.jointMass, ordinaryKeep,
    U1011OriginalSixteenJointNativeCompiler.ordinaryTuples, ordinaryTuples, Finset.sum_filter]

/-- Exact literal primebox transport. The original E remains evaluated
on the true native pair; it is neither snapped nor replaced by a limit. -/
theorem piMain_eq_actual_primebox {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    piMain n N eta E = piMass N *
      ∑ q ∈ BufferedPrimeErrorPayment.tuples N,
        if JointNearCapPrimeReserve.jointKept N E (ordinaryKeep n N) q then
          BufferedPrimeErrorPayment.weight q * ownerDensity n N eta (actualPrimeTupleLog N q)
        else 0 := by
  rw [piMain, physicalDensity_eq_actual_native_harmonic hN heta E,
    JointNearCapPrimeReserve.jointMass_eq_box hN]

def ordinaryLimit (p : Policy) (B : Box) (eta : ℚ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) /
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ)) *
    suzukiContinuousUpperFactor
      ((U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ) /
        (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ))

/-- The true residual/cutoff ratio is >1, derived from the actual all16
certificate and the max(2+rho,...) physical cutoff circuit. -/
theorem actual_cell_density_parameters (p : Policy) (B : Box) (eta : ℚ)
    (hB : B.Valid) (hw : 0 < B.lo 3) (hcert : wholeBoxEligibleTest p B = true) (heta : 0 < eta) :
    0 < (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ) ∧
      1 < (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ) /
        (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ) := by
  have hp := U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p B eta hB hw hcert heta
  have hrho : 0 < U1011OriginalSixteenNearCapBoxProfiles.rho p B eta := hp.2.2.2.2.1
  have hZ : 0 < U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta := hp.2.2.2.2.2.2
  have hcut : U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta ≤
      U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta /
        (2 + U1011OriginalSixteenNearCapBoxProfiles.rho p B eta) := min_le_right _ _
  have hmul := (le_div_iff₀ (by linarith only [hrho] :
    (0 : ℚ) < 2 + U1011OriginalSixteenNearCapBoxProfiles.rho p B eta)).mp hcut
  have hprod : 0 ≤ U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta *
      U1011OriginalSixteenNearCapBoxProfiles.rho p B eta := mul_nonneg hZ.le hrho.le
  have hstrict : U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta <
      U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta := by nlinarith only [hmul, hZ, hprod]
  have hzR : (0 : ℝ) < (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ) := by exact_mod_cast hZ
  refine ⟨hzR, (one_lt_div hzR).mpr ?_⟩
  exact_mod_cast hstrict

/-- The actual coefficient has its genuine ordinary-density limit, with
positive eta fixed BEFORE N. There is no hDensity/hK/hMean input. -/
theorem tendsto_actual_certified_cell_density (p : Policy) (B : Box) (eta : ℚ)
    (hB : B.Valid) (hw : 0 < B.lo 3) (hcert : wholeBoxEligibleTest p B = true) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => cellDensity p B eta N * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (ordinaryLimit p B eta)) := by
  have hparam := actual_cell_density_parameters p B eta hB hw hcert heta
  let u : ℝ := (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ)
  let R : ℝ := (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ)
  have hu : 0 < u := hparam.1
  have hs : 1 < R / u := hparam.2
  have hlim := tendsto_actualSmallRosserPlusDensity_general_normalized u hu (R / u) hs
    (fun N => Nat.ceil ((N : ℝ) ^ u)) (Eventually.of_forall (fun N => Nat.le_ceil _))
  have hmul : (R / u) * u = R := div_mul_cancel₀ R hu.ne'
  simpa only [hmul, cellDensity, rowZ, rowD, ordinaryLimit, u, R] using hlim

def ownerLimit (n : ℕ) (eta : ℚ) (v : LogFour) : ℝ :=
  let B := gridBox n (owner n v)
  ordinaryLimit (boxPolicy B) B eta

/-- Fix the finite causal mesh and positive precision FIRST. A single
threshold then covers every selected original tuple and every outer E.
The finite maximum is over geometric cells, not over N-dependent rows. -/
theorem eventually_uniform_native_owner_density (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ E : ℕ × ℕ → Prop, ∀ t ∈ ordinaryTuples n N E,
        |ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N -
          ownerLimit n eta (coordinates N t)| < epsilon := by
  have hcells : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ j : Grid n, U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox n j) ≠ 0 →
        |cellDensity (boxPolicy (gridBox n j)) (gridBox n j) eta N * Real.log (N : ℝ) /
          singularSeries N - ordinaryLimit (boxPolicy (gridBox n j)) (gridBox n j) eta| < epsilon := by
    apply eventually_all.mpr
    intro j
    by_cases hj : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox n j) ≠ 0
    · have hc := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate (gridBox n j) hj).2
      have ht := tendsto_actual_certified_cell_density (boxPolicy (gridBox n j)) (gridBox n j) eta
        (gridBox_valid n j) (gridBox_lower_positive n j 3) hc heta
      have he := (Metric.tendsto_nhds.mp ht) epsilon hepsilon
      exact he.mono (fun N hN _ => by simpa only [Real.dist_eq] using hN)
    · exact Eventually.of_forall (fun N h => (hj h).elim)
  filter_upwards [hcells] with N hN
  intro E t ht
  have htag := (Finset.mem_filter.mp ht).2
  simpa only [ownerDensity, ownerLimit, tupleTag, ownerBox] using
    hN (owner n (coordinates N t)) htag

/-- Summing the actual normalized density errors costs only the bounded
ORIGINAL reciprocal-prime box mass. No row-count amplification, arithmetic
filter licence, target density bound or H248 comparison is supplied. -/
theorem eventually_actual_primebox_density_error (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ E : ℕ × ℕ → Prop,
        (∑ t ∈ ordinaryTuples n N E,
          |ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N -
            ownerLimit n eta (coordinates N t)| / (Nat.totient (fullPrefix t) : ℝ)) ≤
          epsilon * actualPrimeBoxMass N
            (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) := by
  filter_upwards [eventually_uniform_native_owner_density n eta heta epsilon hepsilon,
    (eventually_gt_atTop (1 : ℕ)).filter_mono inf_le_left] with N hclose hN
  intro E
  let err : LogFour → ℝ := fun v =>
    |ownerDensity n N eta v * Real.log (N : ℝ) / singularSeries N - ownerLimit n eta v|
  have heq : (∑ t ∈ ordinaryTuples n N E,
      err (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ)) =
      JointNearCapPrimeReserve.jointMass N E (ordinaryKeep n N) err := by
    simp only [JointNearCapPrimeReserve.jointMass, ordinaryKeep,
      U1011OriginalSixteenJointNativeCompiler.ordinaryTuples, ordinaryTuples, Finset.sum_filter]
  change (∑ t ∈ ordinaryTuples n N E, err (coordinates N t) /
    (Nat.totient (fullPrefix t) : ℝ)) ≤ _
  rw [heq, JointNearCapPrimeReserve.jointMass_eq_box hN]
  change (∑ q ∈ BufferedPrimeErrorPayment.tuples N,
    if JointNearCapPrimeReserve.jointKept N E (ordinaryKeep n N) q then
      BufferedPrimeErrorPayment.weight q * err (actualPrimeTupleLog N q) else 0) ≤
    epsilon * ∑ q ∈ BufferedPrimeErrorPayment.tuples N, BufferedPrimeErrorPayment.weight q
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hw : 0 ≤ BufferedPrimeErrorPayment.weight q := actualPrimeBoxWeight_nonneg hq
  by_cases hk : JointNearCapPrimeReserve.jointKept N E (ordinaryKeep n N) q
  · have ht : U1011OriginalSixteenNativeHarmonic.unslots q ∈ ordinaryTuples n N E :=
      Finset.mem_filter.mpr ⟨hk.1, hk.2⟩
    have hc := hclose E _ ht
    have herr : err (actualPrimeTupleLog N q) ≤ epsilon := by
      simpa only [err, coordinates, U1011OriginalSixteenNativeHarmonic.slots_unslots] using hc.le
    simp only [if_pos hk]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left herr hw
  · simp only [if_neg hk]
    exact mul_nonneg hepsilon.le hw

end

end ImbalancedChen.P5Z.U1011SameRhoNativePrimeBoxDensity
