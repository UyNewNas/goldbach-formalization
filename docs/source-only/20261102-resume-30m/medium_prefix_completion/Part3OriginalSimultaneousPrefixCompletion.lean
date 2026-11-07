import ImbalancedChen.Part3OriginalReciprocalPrefixDictionary
import ImbalancedChen.Part3ActualCommonIntervalPhysicalLogBudget
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original K maximum may choose a different endpoint for every Outer.
An endpoint-uniform Fourier majorant is used BEFORE summing its squares.
The result has one frequency maximum OUTSIDE the complete outer energy.
No sum of outer/level frequency maxima is substituted for this quantity.

The empty-row PacketData below supplies only the existing interval DFT
geometry.  Its completedPacketSum is zero.  It is explicitly NOT the
original spectral packet and gives no spectral dictionary by itself.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
open ImbalancedChen.Part3.OriginalReciprocalProductAbel20261102
open ImbalancedChen.Part3.OriginalMediumAbelOneCoordinate
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalReciprocalPrefixDictionary20261102
open P3ActualLiteralPacketIntegralSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionNormSourceOnly
open ImbalancedChen.Part3.IntervalHarmonicPairBoundSourceOnly

namespace ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102

attribute [local instance] Classical.propDecidable

/-- An empty packet family used solely to reuse the existing interval
indicator inversion and chord/L1 bounds on [0,S). -/
def prefixGeometry (k : Key) : PacketData Empty where
  rows := ∅
  packet := fun j => nomatch j
  nCarrier := fun j => nomatch j
  lo := 0
  hi := 2 ^ k.u
  V := (2 ^ k.u : ℕ)
  U := 1
  Z := 1
  Y0 := 1
  rho := 0
  sigma := 0
  negativeCusp := false
  kernel := fun j => nomatch j
  V_pos := by exact_mod_cast (pow_pos (by omega : 0 < (2 : ℕ)) k.u)
  U_pos := by norm_num
  Z_pos := by norm_num
  Y0_pos := by norm_num
  m_normalized := by
    intro m hm
    have hS : (0 : ℝ) < (2 ^ k.u : ℕ) := by positivity
    have hmhi : (m : ℝ) < (2 ^ k.u : ℕ) := by
      exact_mod_cast (mem_Ico.mp hm).2
    refine ⟨lt_of_lt_of_le (by norm_num) (div_nonneg (Nat.cast_nonneg _) hS.le), ?_⟩
    have hlt : (m : ℝ) / (2 ^ k.u : ℕ) < 1 := (div_lt_one hS).mpr hmhi
    linarith
  n_normalized := by intro j; exact j.elim
  level_normalized := by intro j; exact j.elim

theorem prefixGeometry_carrier (k : Key) :
    (prefixGeometry k).mCarrier = range (2 ^ k.u) := by
  ext m
  simp [prefixGeometry, PacketData.mCarrier]

def prefixPeriod (k : Key) : ℕ := 2 ^ k.u + 1

theorem prefixPeriod_two_le (k : Key) : 2 ≤ prefixPeriod k := by
  have hS : 0 < (2 : ℕ) ^ k.u := pow_pos (by omega) _
  unfold prefixPeriod
  omega

instance prefixPeriod_neZero (k : Key) : NeZero (prefixPeriod k) :=
  ⟨by have := prefixPeriod_two_le k; omega⟩

theorem prefixGeometry_lt_period (k : Key) :
    (prefixGeometry k).hi < prefixPeriod k := by
  change 2 ^ k.u < 2 ^ k.u + 1
  omega

def prefixCoefficient (k : Key) (i : ℕ) (r : ZMod (prefixPeriod k)) : ℂ :=
  normalizedFourierCoeff (prefixGeometry k) 0 (i+1) (prefixPeriod k) r

/-- Independent of EVERY endpoint and every original outer tuple. -/
def endpointMajorant (N : ℕ) (r : ZMod N) : ℝ :=
  if r = 0 then 1 else
    (1 : ℝ) / (2 * ((min r.val (N-r.val) : ℕ) : ℝ))

theorem endpointMajorant_nonneg (N : ℕ) (r : ZMod N) :
    0 ≤ endpointMajorant N r := by
  unfold endpointMajorant
  split_ifs <;> positivity

theorem prefixCoefficient_le_majorant (k : Key) (i : ℕ)
    (r : ZMod (prefixPeriod k)) :
    ‖prefixCoefficient k i r‖ ≤ endpointMajorant (prefixPeriod k) r := by
  by_cases hr : r = 0
  · subst r
    simpa only [prefixCoefficient, endpointMajorant, if_pos rfl] using
      normalizedFourierCoeff_zero_bound (prefixGeometry k) 0 (i+1)
        (prefixPeriod k) (prefixGeometry_lt_period k)
  · simpa only [prefixCoefficient, endpointMajorant, if_neg hr] using
      normalizedFourierCoeff_nonzero_bound (prefixGeometry k) 0 (i+1)
        (prefixPeriod k) (prefixPeriod_two_le k) (prefixGeometry_lt_period k) r hr

/-- Reuse the old harmonic pair estimate, applied to the positive envelope
itself.  This is stronger than bounding each endpoint's L1 separately. -/
theorem endpointMajorant_sum_le (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    (∑ r : ZMod N, endpointMajorant N r) ≤ 2 + Real.log N := by
  have hn (r : ZMod N) : ‖(endpointMajorant N r : ℂ)‖ = endpointMajorant N r := by
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (endpointMajorant_nonneg N r)]
  have h := cyclic_coefficient_l1_le_two_add_log N hN
    (fun r => (endpointMajorant N r : ℂ))
    (by rw [hn]; simp [endpointMajorant])
    (by intro r hr; rw [hn]; simp only [endpointMajorant, if_neg hr, le_refl])
  simpa only [hn] using h

def completedBare (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (o : Outer) (r : ZMod (prefixPeriod k)) : ℂ :=
  ∑ j ∈ range (2 ^ k.u),
    ZMod.stdAddChar (r * (j : ZMod (prefixPeriod k))) *
      shiftedBare B atom z k small R st st' e o j

/-- One scalar r/(S+1) is applied to every original s in every outer row. -/
theorem completedBare_exp (B : FixedBlock) (atom : MediumAtom) (z : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (o : Outer) (r : ZMod (prefixPeriod k)) :
    completedBare B atom z k small R st st' e o r =
      ∑ j ∈ range (2 ^ k.u),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r.val : ℂ) *
          (j : ℂ) / (prefixPeriod k : ℂ)) *
          shiftedBare B atom z k small R st st' e o j := by
  simp only [completedBare, cyclicCharacter_eq_exp]

/-- Actual K prefixes, not an assumed association with a new packet. -/
theorem original_prefix_completion (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) (i : ℕ) (hi : i < 2 ^ k.u) :
    prefix (shiftedBare B atom z k small R st st' e o) i =
      ∑ r : ZMod (prefixPeriod k), prefixCoefficient k i r *
        completedBare B atom z k small R st st' e o r := by
  let c := shiftedBare B atom z k small R st st' e o
  have hfilter : (range (2 ^ k.u)).filter (fun j => j < i+1) = range (i+1) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  have hind (j : ℕ) (hj : j ∈ range (2 ^ k.u)) :
      (if j < i+1 then (1 : ℂ) else 0) =
        ∑ r : ZMod (prefixPeriod k), prefixCoefficient k i r *
          ZMod.stdAddChar (r * (j : ZMod (prefixPeriod k))) := by
    have hm : j < (prefixGeometry k).hi := mem_range.mp hj
    have h := commonInterval_indicator_inversion (prefixGeometry k) 0 (i+1)
      (prefixPeriod k) (prefixGeometry_lt_period k) j hm
    have he : j ∈ commonInterval (prefixGeometry k) 0 (i+1) ↔ j < i+1 := by
      rw [commonInterval, prefixGeometry_carrier]
      simp only [mem_inter, mem_Ico, zero_le, true_and, hj, and_true]
    rw [he] at h
    simpa only [prefixCoefficient, normalizedFourierCoeff,
      Finset.mul_sum, mul_assoc, cyclicCharacter_eq_exp] using h
  change prefix c i = _
  calc
    _ = ∑ j ∈ range (2 ^ k.u), (if j < i+1 then (1 : ℂ) else 0) * c j := by
      rw [prefix, ← hfilter, sum_filter]
      simp only [ite_mul, one_mul, zero_mul]
    _ = ∑ j ∈ range (2 ^ k.u),
        (∑ r : ZMod (prefixPeriod k), prefixCoefficient k i r *
          ZMod.stdAddChar (r * (j : ZMod (prefixPeriod k)))) * c j := by
      exact sum_congr rfl (fun j hj => congrArg (fun v : ℂ => v * c j) (hind j hj))
    _ = ∑ r : ZMod (prefixPeriod k), prefixCoefficient k i r *
        ∑ j ∈ range (2 ^ k.u),
          ZMod.stdAddChar (r * (j : ZMod (prefixPeriod k))) * c j := by
      simp only [sum_mul]
      rw [sum_comm]
      simp only [mul_sum, mul_assoc]
    _ = _ := rfl

private theorem weighted_norm_sq {α : Type*} (I : Finset α)
    (a v : α → ℂ) (w : α → ℝ) (hw : ∀ r ∈ I, 0 ≤ w r)
    (ha : ∀ r ∈ I, ‖a r‖ ≤ w r) :
    ‖∑ r ∈ I, a r * v r‖^2 ≤
      (∑ r ∈ I, w r) * ∑ r ∈ I, w r * ‖v r‖^2 := by
  have ht : ‖∑ r ∈ I, a r * v r‖ ≤ ∑ r ∈ I, w r * ‖v r‖ := by
    apply (norm_sum_le _ _).trans
    simp only [norm_mul]
    exact sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right (ha r hr) (norm_nonneg _))
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  exact sum_sq_le_sum_mul_sum_of_sq_le_mul I hw
    (fun r hr => mul_nonneg (hw r hr) (sq_nonneg _))
    (fun r hr => le_of_eq (by ring))

/-- The positive weighted energy has the SAME coefficients for all endpoints. -/
def weightedCompletedEnergy (B : FixedBlock) (atom : MediumAtom) (z : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (o : Outer) : ℝ :=
  (∑ r : ZMod (prefixPeriod k), endpointMajorant (prefixPeriod k) r) *
    ∑ r : ZMod (prefixPeriod k), endpointMajorant (prefixPeriod k) r *
      ‖completedBare B atom z k small R st st' e o r‖^2

theorem original_prefix_sq_le_weighted (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) (i : ℕ) (hi : i < 2 ^ k.u) :
    ‖prefix (shiftedBare B atom z k small R st st' e o) i‖^2 ≤
      weightedCompletedEnergy B atom z k small R st st' e o := by
  rw [original_prefix_completion B atom z k small R st st' e o i hi]
  exact weighted_norm_sq _ _ _ _
    (fun r hr => endpointMajorant_nonneg _ r)
    (fun r hr => prefixCoefficient_le_majorant k i r)

/-- No endpoint is chosen independently at a spectral level.  The finite
maximum defining K's envelope is discharged against a common positive sum. -/
theorem rowEnvelope_sq_le_weighted (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) :
    (rowEnvelope B atom z k small R st st' e o)^2 ≤
      weightedCompletedEnergy B atom z k small R st st' e o := by
  have hS : 0 < (2 : ℕ) ^ k.u := pow_pos (by omega) _
  have hlen : 2 ^ k.u - 1 + 1 = 2 ^ k.u := by omega
  have hm := Finset.max'_mem
    (insert 0 ((range (2 ^ k.u - 1 + 1)).image (fun i =>
      ‖prefix (shiftedBare B atom z k small R st st' e o) i‖))) ⟨0, by simp⟩
  change rowEnvelope B atom z k small R st st' e o ∈ _ at hm
  rw [hlen] at hm
  rcases mem_insert.mp hm with hz | hm
  · rw [hz, zero_pow (by omega : 2 ≠ 0)]
    unfold weightedCompletedEnergy
    exact mul_nonneg (sum_nonneg (fun r hr => endpointMajorant_nonneg _ r))
      (sum_nonneg (fun r hr => mul_nonneg (endpointMajorant_nonneg _ r) (sq_nonneg _)))
  · obtain ⟨i, hi, he⟩ := mem_image.mp hm
    rw [← he]
    exact original_prefix_sq_le_weighted B atom z k small R st st' e o i (mem_range.mp hi)

def simultaneousEnergy (B : FixedBlock) (atom : MediumAtom) (z : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (O : Finset Outer) (r : ZMod (prefixPeriod k)) : ℝ :=
  ∑ o ∈ O, ‖completedBare B atom z k small R st st' e o r‖^2

def maxSimultaneousEnergy (B : FixedBlock) (atom : MediumAtom) (z : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (O : Finset Outer) : ℝ :=
  (univ : Finset (ZMod (prefixPeriod k))).sup' univ_nonempty
    (simultaneousEnergy B atom z k small R st st' e O)

theorem simultaneousEnergy_le_max (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (O : Finset Outer) (r : ZMod (prefixPeriod k)) :
    simultaneousEnergy B atom z k small R st st' e O r ≤
      maxSimultaneousEnergy B atom z k small R st st' e O :=
  Finset.le_sup' _ (mem_univ r)

/-- The common phase is selected AFTER the entire positive outer sum.
O can be the exact source image or any licensed post-Cauchy signed-f
enlargement.  No restriction on, or absolute-value substitution for, f
is used by this theorem.  The explicit loss is one squared logarithm. -/
theorem original_simultaneous_prefix_energy (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (O : Finset Outer) :
    (∑ o ∈ O, (rowEnvelope B atom z k small R st st' e o)^2) ≤
      (2 + Real.log (prefixPeriod k))^2 *
        maxSimultaneousEnergy B atom z k small R st st' e O := by
  let L : ℝ := ∑ r : ZMod (prefixPeriod k), endpointMajorant (prefixPeriod k) r
  let M := maxSimultaneousEnergy B atom z k small R st st' e O
  have hL : 0 ≤ L := sum_nonneg (fun r hr => endpointMajorant_nonneg _ r)
  have hM : 0 ≤ M :=
    (sum_nonneg (fun o ho => sq_nonneg _)).trans
      (simultaneousEnergy_le_max B atom z k small R st st' e O 0)
  have hbound : L ≤ 2 + Real.log (prefixPeriod k) :=
    endpointMajorant_sum_le _ (prefixPeriod_two_le k)
  calc
    _ ≤ ∑ o ∈ O, weightedCompletedEnergy B atom z k small R st st' e o :=
      sum_le_sum (fun o ho => rowEnvelope_sq_le_weighted B atom z k small R st st' e o)
    _ = L * ∑ r : ZMod (prefixPeriod k), endpointMajorant (prefixPeriod k) r *
        simultaneousEnergy B atom z k small R st st' e O r := by
      unfold weightedCompletedEnergy simultaneousEnergy L
      rw [mul_sum]
      simp only [mul_sum]
      rw [sum_comm]
    _ ≤ L * ∑ r : ZMod (prefixPeriod k), endpointMajorant (prefixPeriod k) r * M := by
      apply mul_le_mul_of_nonneg_left _ hL
      exact sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
        (simultaneousEnergy_le_max B atom z k small R st st' e O r)
        (endpointMajorant_nonneg _ r))
    _ = L^2 * M := by rw [← sum_mul]; change L * (L * M) = L^2 * M; ring
    _ ≤ (2 + Real.log (prefixPeriod k))^2 * M :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL hbound 2) hM

/-- The single frequency is chosen after O; it cannot depend on o, f,
b, c, or any later level produced by the reciprocal-square dictionary. -/
theorem exists_common_prefix_frequency (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (O : Finset Outer) :
    ∃ r : ZMod (prefixPeriod k),
      (∑ o ∈ O, (rowEnvelope B atom z k small R st st' e o)^2) ≤
        (2 + Real.log (prefixPeriod k))^2 *
          simultaneousEnergy B atom z k small R st st' e O r := by
  obtain ⟨r, hr, he⟩ := Finset.exists_mem_eq_sup'
    (univ_nonempty : (univ : Finset (ZMod (prefixPeriod k))).Nonempty)
    (simultaneousEnergy B atom z k small R st st' e O)
  refine ⟨r, ?_⟩
  have hb := original_simultaneous_prefix_energy B atom z k small R st st' e O
  change _ ≤ (2 + Real.log (prefixPeriod k))^2 *
    (univ : Finset (ZMod (prefixPeriod k))).sup' univ_nonempty
      (simultaneousEnergy B atom z k small R st st' e O) at hb
  rw [he] at hb
  exact hb

/-- The new coefficient is common before every outer variable and every
subsequent y,z fibre.  It has no completed Poisson m argument. -/
def completedLambda (atom : MediumAtom) (st st' : ℕ × ℕ) (e : Fin 4)
    (k : Key) (r : ZMod (prefixPeriod k)) (s : ℕ) : ℂ :=
  ZMod.stdAddChar (r * ((s - 2 ^ k.u : ℕ) : ZMod (prefixPeriod k))) *
    lambdaS atom st st' e s

theorem completedLambda_norm (atom : MediumAtom) (st st' : ℕ × ℕ)
    (e : Fin 4) (k : Key) (r : ZMod (prefixPeriod k)) (s : ℕ) :
    ‖completedLambda atom st st' e k r s‖ = ‖lambdaS atom st st' e s‖ := by
  have he : ZMod.stdAddChar (r * ((s - 2 ^ k.u : ℕ) : ZMod (prefixPeriod k))) =
      P3Period64NativeReconstructionSourceOnly.e
        ((r.val : ℝ) * ((s - 2 ^ k.u : ℕ) : ℝ) / (prefixPeriod k : ℝ)) := by
    rw [cyclicCharacter_eq_exp]
    unfold P3Period64NativeReconstructionSourceOnly.e
    congr 1
    push_cast
    ring
  simp only [completedLambda, he, norm_mul,
    P3Period64NativeReconstructionSourceOnly.norm_e, one_mul]

theorem completedLambda_energy (atom : MediumAtom) (st st' : ℕ × ℕ)
    (e : Fin 4) (k : Key) (r : ZMod (prefixPeriod k)) (T : Finset ℕ) :
    (∑ s ∈ T, ‖completedLambda atom st st' e k r s‖^2) =
      ∑ s ∈ T, ‖lambdaS atom st st' e s‖^2 := by
  simp only [completedLambda_norm]

/-- Full original commonS is restored.  The removed endpoint has become
one common additive modulation of lambdaS, with all other masks unchanged. -/
theorem completedBare_eq_finiteReciprocalRow (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) (r : ZMod (prefixPeriod k)) :
    completedBare B atom z k small R st st' e o r =
      ActualReciprocalSquarePoissonSourceOnly.finiteReciprocalRow 1 B.atom.residue
        (commonS atom z k small st) (Nat.ceil B.H)
        (completedLambda atom st st' e k r) (originalOmega B R)
        ((packetB o, packetC o), o.f) := by
  unfold ActualReciprocalSquarePoissonSourceOnly.finiteReciprocalRow
  have hg (s : ℕ) : (s.Coprime (1 * packetC o) ∧
      s.Coprime (B.atom.residue.natAbs * packetC o)) ↔
      s.Coprime (B.atom.residue.natAbs * packetC o) := by
    simp only [one_mul, Nat.coprime_mul_iff_right]
    tauto
  simp_rw [hg]
  rw [commonS_sum_shift]
  unfold completedBare
  apply sum_congr rfl
  intro j hj
  have hshift : 2 ^ k.u + j - 2 ^ k.u = j := by omega
  by_cases hs : 2 ^ k.u + j ∈ commonS atom z k small st
  · by_cases hu : (2 ^ k.u + j).Coprime (B.atom.residue.natAbs * packetC o)
    · simp only [shiftedBare, bareSAtom, completedLambda, hshift, hs, hu,
        true_and, if_true]
      rw [originalOmega_sum]
      unfold ActualReciprocalSquarePoissonSourceOnly.phase
      ring
    · simp only [shiftedBare, bareSAtom, hs, hu, and_false, if_true, if_false, mul_zero]
  · simp only [shiftedBare, bareSAtom, hs, false_and, if_false, mul_zero]

/-- Exact positive-energy dictionary.  Outer multiplicities are untouched;
this is available on the original source image and on signed-f enlargements. -/
theorem simultaneousEnergy_eq_common_reciprocal (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (O : Finset Outer) (r : ZMod (prefixPeriod k)) :
    simultaneousEnergy B atom z k small R st st' e O r =
      ∑ o ∈ O,
        ‖ActualReciprocalSquarePoissonSourceOnly.finiteReciprocalRow 1 B.atom.residue
          (commonS atom z k small st) (Nat.ceil B.H)
          (completedLambda atom st st' e k r) (originalOmega B R)
          ((packetB o, packetC o), o.f)‖^2 := by
  simp only [simultaneousEnergy, completedBare_eq_finiteReciprocalRow]

/-- Exact 2/S product-Abel charge multiplied by the proved squared log cost. -/
theorem original_abel_prefix_energy (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (O : Finset Outer) :
    (∑ o ∈ O, (2 * rowEnvelope B atom z k small R st st' e o /
      (2 ^ k.u : ℕ))^2) ≤
      ((2 : ℝ) / (2 ^ k.u : ℕ))^2 * (2 + Real.log (prefixPeriod k))^2 *
        maxSimultaneousEnergy B atom z k small R st st' e O := by
  calc
    _ = ((2 : ℝ) / (2 ^ k.u : ℕ))^2 *
        ∑ o ∈ O, (rowEnvelope B atom z k small R st st' e o)^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro o ho
      ring
    _ ≤ ((2 : ℝ) / (2 ^ k.u : ℕ))^2 *
        ((2 + Real.log (prefixPeriod k))^2 *
          maxSimultaneousEnergy B atom z k small R st st' e O) :=
      mul_le_mul_of_nonneg_left
        (original_simultaneous_prefix_energy B atom z k small R st st' e O) (sq_nonneg _)
    _ = _ := by ring

end ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102

end
