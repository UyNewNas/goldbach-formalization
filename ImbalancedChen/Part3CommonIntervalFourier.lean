import Mathlib

/-!
Finite Fourier restriction of one positive dyadic interval.
The elementary geometric, chord and harmonic proofs are adapted from
Part3ActualIntervalGeometricSum, Part3IntervalFourierChordLower, and
Part3IntervalHarmonicPairBound at archived commit
082e55b2b0a82c422b3b9391f41ec21d1f2cbad9. The DFT inversion follows
Part3ActualCommonIntervalCompletion at that same commit.
-/

namespace ImbalancedChen.Part3.ActualIntervalGeometricSumSourceOnly
noncomputable section
open scoped BigOperators

/-- The single-step exponential of the actual additive phase. -/
def phaseBase (α : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ))

/-- Exactly the exponential occurring inside CommonCompletedVariable.weight. -/
def phaseAt (α : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (m : ℂ))

private lemma phaseAt_eq_pow (α : ℝ) (m : ℕ) :
    phaseAt α m = phaseBase α ^ m := by
  calc
    phaseAt α m =
        Complex.exp ((m : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ))) := by
      unfold phaseAt
      congr 1
      ring
    _ = phaseBase α ^ m := by
      rw [Complex.exp_nat_mul]
      rfl

private lemma phaseBase_norm (α : ℝ) : ‖phaseBase α‖ = 1 := by
  have he : phaseBase α =
      Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by
    unfold phaseBase
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_ofReal_mul_I]

private lemma phaseAt_norm (α : ℝ) (m : ℕ) : ‖phaseAt α m‖ = 1 := by
  rw [phaseAt_eq_pow, norm_pow, phaseBase_norm, one_pow]

/-- The phase geometric sum, valid also for an empty interval. -/
theorem phase_geom_identity (α : ℝ) {lo hi : ℕ} (hlo : lo ≤ hi) :
    (1 - phaseBase α) *
        (∑ m ∈ Finset.Ico lo hi, phaseAt α m) =
      phaseAt α lo - phaseAt α hi := by
  simp_rw [phaseAt_eq_pow]
  rw [mul_comm (1 - phaseBase α)
    (∑ m ∈ Finset.Ico lo hi, phaseBase α ^ m)]
  exact geom_sum_Ico_mul_neg (phaseBase α) hlo

private lemma phase_sum_length_bound (α : ℝ) {lo hi : ℕ} (_hlo : lo ≤ hi) :
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
      ((hi - lo : ℕ) : ℝ) := by
  calc
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
        ∑ m ∈ Finset.Ico lo hi, ‖phaseAt α m‖ := norm_sum_le _ _
    _ = ((hi - lo : ℕ) : ℝ) := by
      simp [phaseAt_norm, Nat.card_Ico]

private lemma phase_sum_denominator_bound (α : ℝ) {lo hi : ℕ}
    (hlo : lo ≤ hi) (hne : phaseBase α ≠ 1) :
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
      2 / ‖1 - phaseBase α‖ := by
  have hden : 0 < ‖1 - phaseBase α‖ := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hends : ‖phaseAt α lo - phaseAt α hi‖ ≤ (2 : ℝ) := by
    calc
      ‖phaseAt α lo - phaseAt α hi‖ ≤
          ‖phaseAt α lo‖ + ‖phaseAt α hi‖ := norm_sub_le _ _
      _ = 2 := by norm_num [phaseAt_norm]
  have hmul :
      ‖1 - phaseBase α‖ *
          ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤ 2 := by
    calc
      ‖1 - phaseBase α‖ *
          ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ =
          ‖(1 - phaseBase α) *
            (∑ m ∈ Finset.Ico lo hi, phaseAt α m)‖ :=
        (norm_mul _ _).symm
      _ = ‖phaseAt α lo - phaseAt α hi‖ := by
        rw [phase_geom_identity α hlo]
      _ ≤ 2 := hends
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hmul)

/-- The requested min bound for every real additive phase off resonance. -/
theorem phase_sum_norm_le_min (α : ℝ) {lo hi : ℕ}
    (hlo : lo ≤ hi) (hne : phaseBase α ≠ 1) :
    ‖∑ m ∈ Finset.Ico lo hi, phaseAt α m‖ ≤
      min (((hi - lo : ℕ) : ℝ)) (2 / ‖1 - phaseBase α‖) := by
  exact le_min (phase_sum_length_bound α hlo)
    (phase_sum_denominator_bound α hlo hne)

end
end ImbalancedChen.Part3.ActualIntervalGeometricSumSourceOnly

namespace ImbalancedChen.Part3.IntervalFourierChordLowerSourceOnly
noncomputable section
open scoped BigOperators
open ActualIntervalGeometricSumSourceOnly

private lemma chord_norm (N r : ℕ) (_hN : 0 < N) :
    ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖ =
      2 * |Real.sin (Real.pi * (r : ℝ) / (N : ℝ))| := by
  have he : phaseBase ((r : ℝ) / (N : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (r : ℝ) / (N : ℝ) : ℝ) : ℂ)) := by
    unfold phaseBase
    congr 1
    push_cast
    ring
  rw [norm_sub_rev, he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2 * Real.pi * (r : ℝ) / (N : ℝ)) / 2 =
      Real.pi * (r : ℝ) / (N : ℝ) := by ring
  rw [hhalf]
  simp [Real.norm_eq_abs]

/-- The first half-circle has chord length at least four times r/N. -/
theorem chord_lower_first_half (N r : ℕ)
    (hN : 2 ≤ N) (hr : 1 ≤ r) (hrhalf : r ≤ N / 2) :
    4 * (r : ℝ) / (N : ℝ) ≤
      ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖ := by
  have hNpos : 0 < N := by omega
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have htwor : 2 * r ≤ N := by omega
  have htworReal : (2 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast htwor
  have hrquot : (r : ℝ) / (N : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hNreal).2
    nlinarith
  have hx0 : 0 ≤ Real.pi * (r : ℝ) / (N : ℝ) := by positivity
  have hxhalf : Real.pi * (r : ℝ) / (N : ℝ) ≤ Real.pi / 2 := by
    calc
      Real.pi * (r : ℝ) / (N : ℝ) =
          Real.pi * ((r : ℝ) / (N : ℝ)) := by ring
      _ ≤ Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left hrquot Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hj := Real.mul_le_sin hx0 hxhalf
  have hlin : (2 / Real.pi) *
      (Real.pi * (r : ℝ) / (N : ℝ)) =
      2 * (r : ℝ) / (N : ℝ) := by
    field_simp [Real.pi_pos.ne', hNreal.ne']
  rw [hlin] at hj
  have hsin : 0 ≤ Real.sin (Real.pi * (r : ℝ) / (N : ℝ)) := by
    have : 0 ≤ 2 * (r : ℝ) / (N : ℝ) := by positivity
    exact this.trans hj
  rw [chord_norm N r hNpos, abs_of_nonneg hsin]
  calc
    _ = 2 * (2 * (r : ℝ) / (N : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (by norm_num)

/-- The full nonzero frequency range uses the shorter circular arc. -/
theorem chord_lower_min (N r : ℕ)
    (hN : 2 ≤ N) (hr : 1 ≤ r) (hrlt : r < N) :
    4 * ((min r (N - r) : ℕ) : ℝ) / (N : ℝ) ≤
      ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖ := by
  by_cases hhalf : r ≤ N / 2
  · have hmin : min r (N - r) = r := by
      apply min_eq_left
      omega
    rw [hmin]
    exact chord_lower_first_half N r hN hr hhalf
  · have hspos : 1 ≤ N - r := by omega
    have hshalf : N - r ≤ N / 2 := by omega
    have hmin : min r (N - r) = N - r := by
      apply min_eq_right
      omega
    rw [hmin]
    have hNpos : 0 < N := by omega
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hangle : Real.pi - Real.pi * (r : ℝ) / (N : ℝ) =
        Real.pi * ((N - r : ℕ) : ℝ) / (N : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrlt)]
      field_simp [hNreal.ne']
    have hsin : Real.sin (Real.pi * (r : ℝ) / (N : ℝ)) =
        Real.sin (Real.pi * ((N - r : ℕ) : ℝ) / (N : ℝ)) := by
      rw [← Real.sin_pi_sub, hangle]
    rw [chord_norm N r hNpos, hsin,
      ← chord_norm N (N - r) hNpos]
    exact chord_lower_first_half N (N - r) hN hspos hshalf

/-- The normalized coefficient inherits the geometric and chord bounds. -/
theorem normalized_interval_fourier_coeff_bound (N r lo hi : ℕ)
    (hN : 2 ≤ N) (hr : 1 ≤ r) (hrlt : r < N) (hlo : lo ≤ hi) :
    ‖∑ m ∈ Finset.Ico lo hi,
        phaseAt ((r : ℝ) / (N : ℝ)) m‖ / (N : ℝ) ≤
      min (((hi - lo : ℕ) : ℝ) / (N : ℝ))
        (1 / (2 * ((min r (N - r) : ℕ) : ℝ))) := by
  let s : ℕ := min r (N - r)
  let D : ℝ := ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖
  let S : ℝ := ‖∑ m ∈ Finset.Ico lo hi,
      phaseAt ((r : ℝ) / (N : ℝ)) m‖
  have hsposNat : 0 < s := by
    dsimp [s]
    have hright : 0 < N - r := by omega
    exact lt_min (by omega) hright
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsposNat
  have hNpos : 0 < N := by omega
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hchord : 4 * (s : ℝ) / (N : ℝ) ≤ D :=
    chord_lower_min N r hN hr hrlt
  have hDpos : 0 < D :=
    lt_of_lt_of_le (by positivity : 0 < 4 * (s : ℝ) / (N : ℝ)) hchord
  have hne : phaseBase ((r : ℝ) / (N : ℝ)) ≠ 1 := by
    intro he
    have hz : D = 0 := by simp [D, he]
    linarith
  have hraw := phase_sum_norm_le_min ((r : ℝ) / (N : ℝ)) hlo hne
  have hlength : S ≤ ((hi - lo : ℕ) : ℝ) := by
    exact (le_min_iff.mp hraw).1
  have hden : S ≤ 2 / D := by
    exact (le_min_iff.mp hraw).2
  have hcross : 4 * (s : ℝ) ≤ (N : ℝ) * D :=
    by simpa only [mul_comm D (N : ℝ)] using (div_le_iff₀ hNreal).mp hchord
  have hquot : 2 / D ≤ (N : ℝ) / (2 * (s : ℝ)) := by
    apply (div_le_div_iff₀ hDpos (by positivity : 0 < 2 * (s : ℝ))).2
    nlinarith
  have hlenNorm : S / (N : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right hlength hNreal.le
  have hdenNorm : S / (N : ℝ) ≤ 1 / (2 * (s : ℝ)) := by
    calc
      S / (N : ℝ) ≤
          ((N : ℝ) / (2 * (s : ℝ))) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hden.trans hquot) hNreal.le
      _ = 1 / (2 * (s : ℝ)) := by
        field_simp [hNreal.ne', hspos.ne']
  exact le_min hlenNorm hdenNorm

end
end ImbalancedChen.Part3.IntervalFourierChordLowerSourceOnly

namespace ImbalancedChen.Part3.IntervalHarmonicPairBoundSourceOnly
noncomputable section

open Classical
open scoped BigOperators

/-- Reflection of the complete nonzero residue representative interval. -/
theorem reciprocal_reflection_sum (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / ((N - r : ℕ) : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ) := by
  refine Finset.sum_bij' (fun r _hr => N - r) (fun j _hj => N - j)
    (fun r hr => ?_) (fun j hj => ?_) (fun r hr => ?_)
    (fun j hj => ?_) (fun _r _hr => rfl)
  · simp only [Finset.mem_Icc] at hr ⊢
    omega
  · simp only [Finset.mem_Icc] at hj ⊢
    omega
  · simp only [Finset.mem_Icc] at hr
    omega
  · simp only [Finset.mem_Icc] at hj
    omega

theorem reciprocal_min_le_pair (N r : ℕ) :
    (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ) ≤
      (1 : ℝ) / (r : ℝ) + (1 : ℝ) / ((N - r : ℕ) : ℝ) := by
  by_cases h : r ≤ N - r
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_right (le_of_not_ge h)]
    exact le_add_of_nonneg_left (by positivity)

/-- Exact reflection gives the factor two; it does not discard an endpoint. -/
theorem reciprocal_min_sum_le_twice (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ)) ≤
      2 * ∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ) := by
  calc
    (∑ r ∈ Finset.Icc 1 (N - 1),
        (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ)) ≤
        ∑ r ∈ Finset.Icc 1 (N - 1),
          ((1 : ℝ) / (r : ℝ) + (1 : ℝ) / ((N - r : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum (fun r _hr => reciprocal_min_le_pair N r)
    _ = _ := by
      rw [Finset.sum_add_distrib, reciprocal_reflection_sum]
      ring

theorem real_reciprocal_sum_eq_harmonic (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / (j : ℝ)) = (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]

/-- Enlarge the final endpoint by one before applying the pinned harmonic bound. -/
theorem reciprocal_sum_le_one_add_log (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ)) ≤ 1 + Real.log N := by
  calc
    (∑ j ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / (j : ℝ)) ≤
        ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
        exact Finset.mem_Icc.mpr ⟨hl, le_trans hu (Nat.sub_le N 1)⟩
      · intro j _hj _hj'
        positivity
    _ = (harmonic N : ℝ) := real_reciprocal_sum_eq_harmonic N
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

theorem reciprocal_min_sum_le_log (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ)) ≤
        2 * (1 + Real.log N) := by
  exact (reciprocal_min_sum_le_twice N).trans
    (mul_le_mul_of_nonneg_left (reciprocal_sum_le_one_add_log N) (by norm_num))

/-- The natural representatives of all nonzero cyclic residues, once each. -/
theorem sum_nonzero_zmod_reindex (N : ℕ) [NeZero N] (f : ℕ → ℝ) :
    (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, f r.val) =
      ∑ j ∈ Finset.Icc 1 (N - 1), f j := by
  refine Finset.sum_bij' (fun r _hr => r.val) (fun j _hj => (j : ZMod N))
    (fun r hr => ?_) (fun j hj => ?_) (fun r _hr => ?_)
    (fun j hj => ?_) (fun _r _hr => rfl)
  · have hr0 : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have hv0 : r.val ≠ 0 := fun hz => hr0 ((ZMod.val_eq_zero r).mp hz)
    have hvN := ZMod.val_lt r
    apply Finset.mem_Icc.mpr
    omega
  · rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
    have hjN : j < N := by omega
    apply Finset.mem_erase.mpr
    constructor
    · intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hjN, ZMod.val_zero] at hv
      omega
    · exact Finset.mem_univ _
  · exact ZMod.natCast_zmod_val r
  · exact ZMod.val_natCast_of_lt (by
      rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
      omega)

theorem half_reciprocal_min_sum_le_log (N : ℕ) :
    (∑ r ∈ Finset.Icc 1 (N - 1),
      (1 : ℝ) / (2 * ((min r (N - r) : ℕ) : ℝ))) ≤ 1 + Real.log N := by
  calc
    (∑ r ∈ Finset.Icc 1 (N - 1),
        (1 : ℝ) / (2 * ((min r (N - r) : ℕ) : ℝ))) =
        (1 / 2 : ℝ) * ∑ r ∈ Finset.Icc 1 (N - 1),
          (1 : ℝ) / ((min r (N - r) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [one_div, mul_inv_rev]
      ring
    _ ≤ (1 / 2 : ℝ) * (2 * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (reciprocal_min_sum_le_log N) (by norm_num)
    _ = 1 + Real.log N := by ring

/-- Pure coefficient consequence. The hypotheses are ordinary finite scalar
norm bounds; no spectral or packet estimate is assumed. -/
theorem cyclic_coefficient_l1_le_two_add_log (N : ℕ) [NeZero N]
    (hN : 2 ≤ N) (coeff : ZMod N → ℂ)
    (hzero : ‖coeff 0‖ ≤ 1)
    (hnonzero : ∀ r : ZMod N, r ≠ 0 →
      ‖coeff r‖ ≤ (1 : ℝ) / (2 * ((min r.val (N - r.val) : ℕ) : ℝ))) :
    (∑ r : ZMod N, ‖coeff r‖) ≤ 2 + Real.log N := by
  have htail : (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖coeff r‖) ≤
      1 + Real.log N := by
    calc
      (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖coeff r‖) =
          ∑ j ∈ Finset.Icc 1 (N - 1), ‖coeff (j : ZMod N)‖ := by
        simpa only [ZMod.natCast_zmod_val] using
          sum_nonzero_zmod_reindex N (fun j => ‖coeff (j : ZMod N)‖)
      _ ≤ ∑ j ∈ Finset.Icc 1 (N - 1),
          (1 : ℝ) / (2 * ((min j (N - j) : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        rcases Finset.mem_Icc.mp hj with ⟨hl, hu⟩
        have hjN : j < N := by omega
        have hj0 : (j : ZMod N) ≠ 0 := by
          intro hz
          have hv := congrArg ZMod.val hz
          rw [ZMod.val_natCast_of_lt hjN, ZMod.val_zero] at hv
          omega
        simpa only [ZMod.val_natCast_of_lt hjN] using hnonzero (j : ZMod N) hj0
      _ ≤ 1 + Real.log N := half_reciprocal_min_sum_le_log N
  calc
    (∑ r : ZMod N, ‖coeff r‖) =
        (∑ r ∈ (Finset.univ : Finset (ZMod N)).erase 0, ‖coeff r‖) + ‖coeff 0‖ :=
      (Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
        (fun r => ‖coeff r‖) (Finset.mem_univ (0 : ZMod N))).symm
    _ ≤ (1 + Real.log N) + 1 := add_le_add htail hzero
    _ = 2 + Real.log N := by ring

end
end ImbalancedChen.Part3.IntervalHarmonicPairBoundSourceOnly

namespace ImbalancedChen.Part3.CommonIntervalFourier

noncomputable section
open Classical Finset
open scoped BigOperators
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open IntervalFourierChordLowerSourceOnly (normalized_interval_fourier_coeff_bound)
open IntervalHarmonicPairBoundSourceOnly (cyclic_coefficient_l1_le_two_add_log)

private def intervalMask (hi N : ℕ) (r : ZMod N) : ℂ :=
  if r.val ∈ Finset.Ico 0 hi then 1 else 0

/-- Inverse-normalized Fourier coefficient of the integer prefix `[0,hi)`. -/
def intervalCoeff (hi N : ℕ) [NeZero N] (r : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ZMod.dft (intervalMask hi N) r

private theorem sum_zmod_by_natVal (N : ℕ) [NeZero N] (f : ℕ → ℂ) :
    (∑ r : ZMod N, f r.val) = ∑ m ∈ Finset.range N, f m := by
  refine Finset.sum_bij' (fun r _ => r.val) (fun m _ => (m : ZMod N))
    (fun r _ => ?_) (fun _ _ => ?_) (fun r _ => ?_) (fun m hm => ?_) (fun _ _ => rfl)
  · exact Finset.mem_range.mpr (ZMod.val_lt r)
  · exact Finset.mem_univ _
  · exact ZMod.natCast_zmod_val r
  · exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hm)

private theorem intervalDFT_eq_sum {hi N : ℕ} [NeZero N] (hhi : hi ≤ N) (r : ZMod N) :
    ZMod.dft (intervalMask hi N) r =
      ∑ m ∈ Finset.Ico 0 hi, ZMod.stdAddChar (-((m : ZMod N) * r)) := by
  have hfilter : (Finset.range N).filter (fun m => m ∈ Finset.Ico 0 hi) = Finset.Ico 0 hi := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_iff_right_of_imp (fun hm => (Finset.mem_Ico.mp hm).2.trans_le hhi)
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    _ = ∑ x : ZMod N, if x.val ∈ Finset.Ico 0 hi then
          ZMod.stdAddChar (-((x.val : ZMod N) * r)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x.val ∈ Finset.Ico 0 hi
      · rw [intervalMask, if_pos hx, if_pos hx, mul_one, ZMod.natCast_zmod_val]
      · rw [intervalMask, if_neg hx, if_neg hx, mul_zero]
    _ = ∑ m ∈ Finset.range N, if m ∈ Finset.Ico 0 hi then
          ZMod.stdAddChar (-((m : ZMod N) * r)) else 0 :=
      sum_zmod_by_natVal N (fun m => if m ∈ Finset.Ico 0 hi then
        ZMod.stdAddChar (-((m : ZMod N) * r)) else 0)
    _ = _ := by rw [← Finset.sum_filter, hfilter]

private theorem intervalCoeff_norm {hi N : ℕ} [NeZero N] (r : ZMod N) :
    ‖intervalCoeff hi N r‖ = ‖ZMod.dft (intervalMask hi N) r‖ / (N : ℝ) := by
  rw [intervalCoeff, norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv]
  ring

private theorem cyclicCharacter_eq_exp (N : ℕ) [NeZero N] (r : ZMod N) (m : ℕ) :
    ZMod.stdAddChar (r * (m : ZMod N)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r.val : ℂ) * (m : ℂ) / (N : ℂ)) := by
  have hc : r * (m : ZMod N) = ((r.val * m : ℕ) : ZMod N) := by
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hc, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  push_cast
  congr 1
  ring

private theorem intervalCoeff_nonzero {hi N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (hhi : hi ≤ N) (r : ZMod N) (hr0 : r ≠ 0) :
    ‖intervalCoeff hi N r‖ ≤ (1 : ℝ) / (2 * ((min r.val (N - r.val) : ℕ) : ℝ)) := by
  let s : ℕ := N - r.val
  have hrval0 : r.val ≠ 0 := fun hz => hr0 ((ZMod.val_eq_zero r).mp hz)
  have hrvalN := ZMod.val_lt r
  have hs1 : 1 ≤ s := by dsimp [s]; omega
  have hsN : s < N := by dsimp [s]; omega
  have hsCast : (s : ZMod N) = -r := by
    dsimp [s]
    rw [Nat.cast_sub (Nat.le_of_lt hrvalN), ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
  have hmin : min s (N - s) = min r.val (N - r.val) := by dsimp [s]; omega
  have hphase (m : ℕ) : ZMod.stdAddChar (-((m : ZMod N) * r)) =
      phaseAt ((s : ℝ) / (N : ℝ)) m := by
    have hc : -((m : ZMod N) * r) = (s : ZMod N) * (m : ZMod N) := by rw [hsCast]; ring
    rw [hc, cyclicCharacter_eq_exp, ZMod.val_natCast_of_lt hsN]
    unfold phaseAt
    push_cast
    congr 1
    ring
  rw [intervalCoeff_norm, intervalDFT_eq_sum hhi]
  simp_rw [hphase]
  have hbound := normalized_interval_fourier_coeff_bound N s 0 hi hN hs1 hsN (Nat.zero_le _)
  simpa only [hmin] using (le_min_iff.mp hbound).2

/-- The normalized DFT of the interval mask itself pays the logarithmic cost. -/
theorem intervalCoeff_l1 {hi N : ℕ} [NeZero N] (hN : 2 ≤ N) (hhi : hi ≤ N) :
    (∑ r : ZMod N, ‖intervalCoeff hi N r‖) ≤ 2 + Real.log N := by
  apply cyclic_coefficient_l1_le_two_add_log N hN (intervalCoeff hi N)
  · have hzero : ZMod.dft (intervalMask hi N) 0 = (hi : ℂ) := by
      rw [intervalDFT_eq_sum hhi]
      simp
    rw [intervalCoeff_norm, hzero, Complex.norm_natCast]
    exact (div_le_one (by exact_mod_cast (by omega : 0 < N))).mpr (by exact_mod_cast hhi)
  · exact intervalCoeff_nonzero hN hhi

private theorem intervalMask_inversion {hi N m : ℕ} [NeZero N] (hm : m < N) :
    (if m < hi then (1 : ℂ) else 0) =
      ∑ r : ZMod N, intervalCoeff hi N r * ZMod.stdAddChar (r * (m : ZMod N)) := by
  have hinv := congrArg (fun g : ZMod N → ℂ => g (m : ZMod N))
    ((ZMod.dft (N := N) (E := ℂ)).symm_apply_apply (intervalMask hi N))
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul, intervalMask, ZMod.val_natCast_of_lt hm, Finset.mem_Ico, Nat.zero_le,
    true_and] at hinv
  rw [← hinv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  unfold intervalCoeff
  ring

private theorem common_phase_shift (N : ℕ) [NeZero N] (r : ZMod N) (m : ℕ) (ω : ℝ) :
    ZMod.stdAddChar (r * (m : ZMod N)) * phaseAt ω m =
      phaseAt (ω + (r.val : ℝ) / N) m := by
  rw [cyclicCharacter_eq_exp, phaseAt, phaseAt, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The literal positive dyadic interval and its common upper clipping. -/
def fullBlock (j : ℕ) : Finset ℕ := Finset.Ico (2 ^ j) (2 ^ (j + 1))
def commonBlock (J j : ℕ) : Finset ℕ := Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (J + 1))
def period (j : ℕ) : ℕ := 4 * 2 ^ j + 1

private instance (j : ℕ) : NeZero (period j) := ⟨by unfold period; positivity⟩

/-- `v m` may be the complete vector of levels and spectral multiplicities. -/
def phaseSum {E : Type*} [AddCommMonoid E] [SMul ℂ E]
    (S : Finset ℕ) (ω : ℝ) (v : ℕ → E) : E := ∑ m ∈ S, phaseAt ω m • v m

/-- One Fourier index shifts the same phase in the entire vector. -/
theorem commonBlock_completion {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J j : ℕ) (ω : ℝ) (v : ℕ → E) : phaseSum (commonBlock J j) ω v =
      ∑ r : ZMod (period j), intervalCoeff (min (J + 1) (4 * 2 ^ j)) (period j) r •
        phaseSum (fullBlock j) (ω + (r.val : ℝ) / period j) v := by
  let N := period j
  let hi := min (J + 1) (4 * 2 ^ j)
  have hmask {m : ℕ} (hm : m ∈ fullBlock j) : m < hi ↔ m < J + 1 := by
    have hmid := (Finset.mem_Ico.mp hm).2
    rw [pow_succ] at hmid
    exact lt_min_iff.trans (and_iff_left (by omega))
  have hperiod {m : ℕ} (hm : m ∈ fullBlock j) : m < N := by
    have hmid := (Finset.mem_Ico.mp hm).2
    rw [pow_succ] at hmid
    dsimp [N, period]
    omega
  have hfilter : (fullBlock j).filter (fun m => m < J + 1) = commonBlock J j := by
    ext m
    simp only [fullBlock, commonBlock, Finset.mem_filter, Finset.mem_Ico, lt_min_iff]
    tauto
  change phaseSum (commonBlock J j) ω v = ∑ r : ZMod N,
    intervalCoeff hi N r • phaseSum (fullBlock j) (ω + (r.val : ℝ) / N) v
  calc
    _ = ∑ m ∈ fullBlock j, (if m < hi then (1 : ℂ) else 0) • (phaseAt ω m • v m) := by
      rw [← hfilter, phaseSum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : m < J + 1 <;> simp [h, hmask hm]
    _ = ∑ m ∈ fullBlock j,
        (∑ r : ZMod N, intervalCoeff hi N r * ZMod.stdAddChar (r * (m : ZMod N))) •
          (phaseAt ω m • v m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [intervalMask_inversion (hperiod hm)]
    _ = _ := by
      simp_rw [phaseSum, Finset.sum_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro m _
      rw [smul_smul, smul_smul, mul_assoc, common_phase_shift]

/-- Finite weighted-vector norm completion. The chosen phase is shared across
all levels, because the maximum is taken after forming the complete vector. -/
theorem commonBlock_norm_sq_le_one_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J j : ℕ) (ω : ℝ) (v : ℕ → E) :
    ∃ ω' : ℝ, ‖phaseSum (commonBlock J j) ω v‖ ^ 2 ≤
      (2 + Real.log (period j)) ^ 2 * ‖phaseSum (fullBlock j) ω' v‖ ^ 2 := by
  let N := period j
  let hi := min (J + 1) (4 * 2 ^ j)
  let g := fun r : ZMod N => phaseSum (fullBlock j) (ω + (r.val : ℝ) / N) v
  have hN : 2 ≤ N := by
    have h : 0 < (2 : ℕ) ^ j := by positivity
    dsimp [N, period]
    omega
  have hhi : hi ≤ N := (min_le_right _ _).trans (Nat.le_succ _)
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (ZMod N)).Nonempty) (fun k => ‖g k‖)
  have hmax (k : ZMod N) : ‖g k‖ ≤ ‖g r‖ := by
    rw [← hr]
    exact Finset.le_sup' (fun s => ‖g s‖) (Finset.mem_univ k)
  have hnorm : ‖phaseSum (commonBlock J j) ω v‖ ≤ (2 + Real.log N) * ‖g r‖ := by
    calc
      _ ≤ ∑ s : ZMod N, ‖intervalCoeff hi N s • g s‖ := by
        rw [commonBlock_completion]
        exact norm_sum_le _ _
      _ ≤ ∑ s : ZMod N, ‖intervalCoeff hi N s‖ * ‖g r‖ := by
        apply Finset.sum_le_sum
        intro s _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hmax s) (norm_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (intervalCoeff_l1 hN hhi) (norm_nonneg _)
  refine ⟨ω + (r.val : ℝ) / N, ?_⟩
  simpa only [mul_pow, g] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Apply the common phase to the actual quadratic sum over all indices.
An index can include both a level and a multiplicity slot. -/
theorem commonBlock_weighted_energy_le_one_phase {ι : Type*} [Fintype ι]
    (J j : ℕ) (ω : ℝ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : ι → ℕ → ℂ) :
    ∃ ω' : ℝ,
      (∑ i, w i * ‖∑ m ∈ commonBlock J j, phaseAt ω m * a i m‖ ^ 2) ≤
        (2 + Real.log (period j)) ^ 2 *
          (∑ i, w i * ‖∑ m ∈ fullBlock j, phaseAt ω' m * a i m‖ ^ 2) := by
  let v : ℕ → EuclideanSpace ℂ ι := fun m =>
    WithLp.toLp 2 (fun i => (Real.sqrt (w i) : ℂ) * a i m)
  have hcoord (S : Finset ℕ) (ρ : ℝ) (i : ι) :
      phaseSum S ρ v i = (Real.sqrt (w i) : ℂ) * (∑ m ∈ S, phaseAt ρ m * a i m) := by
    let ev : EuclideanSpace ℂ ι →ₗ[ℂ] ℂ := PiLp.projₗ 2 (fun _ : ι => ℂ) i
    change ev (phaseSum S ρ v) = _
    rw [phaseSum, map_sum, Finset.mul_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro m _
    change phaseAt ρ m * ((Real.sqrt (w i) : ℂ) * a i m) = _
    ring
  have henergy (S : Finset ℕ) (ρ : ℝ) :
      ‖phaseSum S ρ v‖ ^ 2 = ∑ i, w i * ‖∑ m ∈ S, phaseAt ρ m * a i m‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i)]
  obtain ⟨ω', hω'⟩ := commonBlock_norm_sq_le_one_phase J j ω v
  exact ⟨ω', by simpa only [henergy] using hω'⟩

/-- A uniform full-block bound therefore also bounds its clipped energy,
with the genuine finite completion cost. -/
theorem commonBlock_weighted_energy_le_uniform_bound {ι : Type*} [Fintype ι]
    (J j : ℕ) (ω bound : ℝ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : ι → ℕ → ℂ)
    (full_uniform : ∀ ρ : ℝ, (∑ i, w i * ‖∑ m ∈ fullBlock j, phaseAt ρ m * a i m‖ ^ 2) ≤ bound) :
    (∑ i, w i * ‖∑ m ∈ commonBlock J j, phaseAt ω m * a i m‖ ^ 2) ≤
      (2 + Real.log (period j)) ^ 2 * bound := by
  obtain ⟨ω', hω'⟩ := commonBlock_weighted_energy_le_one_phase J j ω w hw a
  exact hω'.trans (mul_le_mul_of_nonneg_left (full_uniform ω') (sq_nonneg _))

/-- Pascadi's printed interval `(M,2M]` is the full positive integer
block for `M = 2^j - 1/2`, including the block `j=0`. -/
theorem mem_fullBlock_iff_classical_interval (j m : ℕ) :
    m ∈ fullBlock j ↔ (m : ℝ) ∈ Set.Ioc
      (((2 ^ j : ℕ) : ℝ) - 1 / 2) (2 * (((2 ^ j : ℕ) : ℝ) - 1 / 2)) := by
  rw [fullBlock, Finset.mem_Ico, Set.mem_Ioc, pow_succ]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hl : ((2 ^ j : ℕ) : ℝ) ≤ m := by exact_mod_cast hlo
    have hu : (m : ℝ) + 1 ≤ ((2 ^ j : ℕ) : ℝ) * 2 := by
      exact_mod_cast (show m + 1 ≤ 2 ^ j * 2 by omega)
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra h
      have hn : m + 1 ≤ 2 ^ j := by omega
      have hr : (m : ℝ) + 1 ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hn
      linarith
    · by_contra h
      have hn : 2 ^ j * 2 ≤ m := by omega
      have hr : ((2 ^ j : ℕ) : ℝ) * 2 ≤ m := by exact_mod_cast hn
      linarith

end
end ImbalancedChen.Part3.CommonIntervalFourier
