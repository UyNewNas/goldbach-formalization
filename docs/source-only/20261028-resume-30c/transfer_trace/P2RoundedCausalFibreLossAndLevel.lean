import ImbalancedChen.P2LowerCanonicalRetainedTrace
import ImbalancedChen.P2CompiledCausalPrimeSourceLower
import ImbalancedChen.P2RoundedU6NativeJointLedger

/-!
# Actual ALL/ANY rounding loss and uniform physical-level inflation

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Negative coefficients are rounded OUTWARD, so the rounded support need not
be contained in the raw retained support. The correct preimage is an actual
raw modulus in the SAME complete logarithmic label fibre. Its existence is
proved from the literal compiler, not supplied as a support hypothesis.
A common rank bound then costs R*tau in exponent. A strict raw level reserve
pays this cost with a mesh fixed before N, and the genuine small beta factor
is included in the physical bound.

The actual density loss is confined to mixed fibres, containing both an
original retained and rejected complete history. No count of N-dependent
prime gaps is used to claim common-mesh asymptotic convergence. Full wall
cover and its uniform arithmetic mass, and the selected-plan raw level/rank
supplier, remain explicit implementation obligations.
-/

namespace ImbalancedChen.P2RoundedCausalFibreLossAndLevel

noncomputable section
open scoped Classical BigOperators
open P2LowerFiniteCellRounding P2LowerFiniteCellBetaCompiler
open P2LowerCapPlanIntegerRetention P2LowerCanonicalRetainedTrace

/-- A genuinely mixed fibre of the actual whole raw-support predicate. -/
def mixed (keep : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  (∃ r ∈ cell N cap w z tau d, r ∈ rawSupport keep N cap w z) ∧
  (∃ r ∈ cell N cap w z tau d, r ∉ rawSupport keep N cap w z)

/-- On an unmixed complete-history fibre, both directed rounding rules
return precisely the original coefficient. No policy monotonicity is used. -/
theorem coefficient_eq_raw_of_not_mixed (keep : List ℕ → Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ)
    (hm : ¬ mixed keep N cap w z tau d) :
    coefficient keep N cap w z tau d = raw keep N cap w z d := by
  rw [raw_value]
  by_cases hd : d ∈ universe N cap w z
  · have hself := self_mem_cell N cap w z tau hd
    by_cases hr : d ∈ rawSupport keep N cap w z
    · have hi : inner keep N cap w z tau d := by
        intro e he
        by_contra hn
        exact hm ⟨⟨d, hself, hr⟩, ⟨e, he, hn⟩⟩
      have ho : outer keep N cap w z tau d :=
        ⟨d, Finset.mem_inter.mpr ⟨hself, hr⟩⟩
      simp [coefficient, hd, hi, ho, hr]
    · have hi : ¬ inner keep N cap w z tau d := fun h => hr (h hself)
      have ho : ¬ outer keep N cap w z tau d := by
        rintro ⟨e, he⟩
        have h := Finset.mem_inter.mp he
        exact hm ⟨⟨e, h.1, h.2⟩, ⟨d, hself, hr⟩⟩
      simp [coefficient, hd, hi, ho, hr]
  · have hr : d ∉ rawSupport keep N cap w z :=
      fun h => hd (rawSupport_subset_universe keep N cap w z h)
    simp [coefficient, hd, hr]

/-- The compiler's actual nonzero output has an ORIGINAL retained witness
in its own complete label fibre, including the outward negative case. -/
theorem coefficient_ne_zero_raw_fibre (keep : List ℕ → Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hn : coefficient keep N cap w z tau d ≠ 0) :
    d ∈ universe N cap w z ∧ ∃ r ∈ rawSupport keep N cap w z,
      label N tau d = label N tau r := by
  have hd : d ∈ universe N cap w z := by
    by_contra hd
    exact hn (by simp [coefficient, hd])
  refine ⟨hd, ?_⟩
  by_cases hs : 0 ≤ (ArithmeticFunction.moebius d : ℝ)
  · have hi : inner keep N cap w z tau d := by
      by_contra hi
      exact hn (by simp [coefficient, hd, hs, hi])
    exact ⟨d, hi (self_mem_cell N cap w z tau hd), rfl⟩
  · have ho : outer keep N cap w z tau d := by
      by_contra ho
      exact hn (by simp [coefficient, hd, hs, ho])
    obtain ⟨r, hr⟩ := ho
    obtain ⟨hrcell, hrraw⟩ := Finset.mem_inter.mp hr
    exact ⟨r, hrraw, (Finset.mem_filter.mp hrcell).2.symm⟩

/-- Mixed fibres for the actual CapPlan are precisely fibres containing
an accepted and a rejected CANONICAL integer trace. No alternative order
or later parent choice is inserted into the raw-support test. -/
theorem mixed_actual_trace_iff {depth m : ℕ}
    (P : P2PhysicalIncomingPrefixCells.CapPlan depth m) (a b seedCap : ℝ)
    {N : ℕ} (hN : 1 < (N : ℝ)) (cap : ℕ) (z0 v tau : ℝ)
    (hmargin : 2 * v < seedCap) (d : ℕ) :
    mixed (retainEven P a b seedCap N) N cap z0 ((N : ℝ) ^ v) tau d ↔
      ∃ r ∈ cell N cap z0 ((N : ℝ) ^ v) tau d,
      ∃ s ∈ cell N cap z0 ((N : ℝ) ^ v) tau d,
        retainEven P a b seedCap N r.primeFactorsList = true ∧
        retainEven P a b seedCap N s.primeFactorsList ≠ true := by
  constructor
  · rintro ⟨⟨r, hr, hrraw⟩, s, hs, hsraw⟩
    refine ⟨r, hr, s, hs, ?_, ?_⟩
    · exact ((raw_support_iff_canonical_trace P a b seedCap hN cap z0 v
        hmargin r).mp hrraw).2
    · intro ht
      exact hsraw ((raw_support_iff_canonical_trace P a b seedCap hN cap z0 v
        hmargin s).mpr ⟨(Finset.mem_filter.mp hs).1, ht⟩)
  · rintro ⟨r, hr, s, hs, htr, hts⟩
    refine ⟨⟨r, hr, ?_⟩, ⟨s, hs, ?_⟩⟩
    · exact (raw_support_iff_canonical_trace P a b seedCap hN cap z0 v
        hmargin r).mpr ⟨(Finset.mem_filter.mp hr).1, htr⟩
    · intro hraw
      exact hts ((raw_support_iff_canonical_trace P a b seedCap hN cap z0 v
        hmargin s).mp hraw).2


def mixedMass (keep : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  ∑ d ∈ (universe N cap w z).filter (mixed keep N cap w z tau),
    1 / (Nat.totient d : ℝ)

/-- The EXACT output loss is paid only on actual mixed retained/rejected
fibres. The factor two is a safe unit-coefficient bound, with no assumption
that the signed lower coefficients are nonnegative. -/
theorem roundingLoss_le_two_mixedMass (keep : List ℕ → Bool)
    (N cap : ℕ) (w z tau : ℝ) :
    roundingLoss keep N cap w z tau ≤ 2 * mixedMass keep N cap w z tau := by
  unfold roundingLoss reciprocalTotientDensity mixedMass
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  by_cases hm : mixed keep N cap w z tau d
  · rw [if_pos hm]
    have ha : |coefficient keep N cap w z tau d - raw keep N cap w z d| ≤
        |coefficient keep N cap w z tau d| + |raw keep N cap w z d| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (coefficient keep N cap w z tau d) 0 (raw keep N cap w z d))
    have hc := coefficient_abs_le_one keep N cap w z tau d
    have hr : |raw keep N cap w z d| ≤ 1 :=
      fixedEvenRoughCoefficient_abs_le_one keep N cap w z d
    have habs : |coefficient keep N cap w z tau d - raw keep N cap w z d| ≤ 2 := by
      exact ha.trans (add_le_add hc hr)
    simpa only [mul_one_div] using
      div_le_div_of_nonneg_right habs (Nat.cast_nonneg (Nat.totient d))
  · rw [if_neg hm, mul_zero, coefficient_eq_raw_of_not_mixed keep N cap w z tau d hm]
    simp

/-- Equal rounded labels bound sums with a mesh error per coordinate.
This is applied below to the actual prime-factor coordinate words. -/
theorem same_floor_word_sum_le {tau : ℝ} (htau : 0 < tau)
    (xs ys : List ℝ)
    (h : xs.map (fun x => (⌊x / tau⌋ : ℤ)) =
      ys.map (fun y => (⌊y / tau⌋ : ℤ))) :
    xs.sum ≤ ys.sum + (xs.length : ℝ) * tau := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := by simpa using h.symm
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have hc : (⌊x / tau⌋ : ℤ) = ⌊y / tau⌋ := (List.cons.inj h).1
          have ht := (List.cons.inj h).2
          have hlo : ((⌊y / tau⌋ : ℤ) : ℝ) * tau ≤ y :=
            (le_div_iff₀ htau).mp (Int.floor_le (y / tau))
          have hhi : x < (((⌊x / tau⌋ : ℤ) : ℝ) + 1) * tau :=
            (div_lt_iff₀ htau).mp (Int.lt_floor_add_one (x / tau))
          rw [hc] at hhi
          have hxy : x ≤ y + tau := by linarith
          have hs := ih ys ht
          simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
          nlinarith

/-- Products of canonical actual prime histories equal N to their physical
logarithmic sum. Positivity comes from actual universe membership. -/
theorem universe_word_power {N : ℕ} (hN : 1 < (N : ℝ))
    (cap : ℕ) (w z : ℝ) {d : ℕ} (hd : d ∈ universe N cap w z) :
    (N : ℝ) ^ (physicalWord N d.primeFactorsList).sum = (d : ℝ) := by
  obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe N cap w z hd
  have hpos : ∀ p ∈ d.primeFactorsList, 0 < p := by
    intro p hp
    have hrev : p ∈ d.primeFactorsList.reverse := by simpa using hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset hrev)).pos
  have hprod' : d.primeFactorsList.prod = d := by
    simpa only [List.prod_reverse] using hprod
  have hp := physicalWord_power hN d.primeFactorsList hpos
  simpa only [hprod'] using hp

/-- The actual same-label raw witness controls physical modulus growth.
The exponent is R*tau with R a bound on the witness's original rank. -/
theorem same_label_modulus_le {N : ℕ} (hN : 1 < (N : ℝ))
    (cap : ℕ) (w z : ℝ) {tau : ℝ} (htau : 0 < tau)
    {d r R : ℕ} (hd : d ∈ universe N cap w z)
    (hr : r ∈ universe N cap w z)
    (hl : label N tau d = label N tau r) (hR : r.primeFactorsList.length ≤ R) :
    (d : ℝ) ≤ (r : ℝ) * (N : ℝ) ^ ((R : ℝ) * tau) := by
  have hword :
      (physicalWord N d.primeFactorsList).map (fun x => (⌊x / tau⌋ : ℤ)) =
      (physicalWord N r.primeFactorsList).map (fun x => (⌊x / tau⌋ : ℤ)) := by
    simpa only [physicalWord, coordinate, label, primeLabel, List.map_map,
      Function.comp_def] using hl
  have hlen : d.primeFactorsList.length = r.primeFactorsList.length := by
    have h := congrArg List.length hl
    simpa only [label, List.length_map, List.length_reverse] using h
  have hsum := same_floor_word_sum_le htau _ _ hword
  have hlength : ((physicalWord N d.primeFactorsList).length : ℝ) ≤ R := by
    simpa only [physicalWord, List.length_map, List.length_reverse, hlen] using
      (show (r.primeFactorsList.length : ℝ) ≤ (R : ℝ) by exact_mod_cast hR)
  have hcoord : (physicalWord N d.primeFactorsList).sum ≤
      (physicalWord N r.primeFactorsList).sum + (R : ℝ) * tau :=
    hsum.trans (add_le_add_left (mul_le_mul_of_nonneg_right hlength htau.le) _)
  calc
    (d : ℝ) = (N : ℝ) ^ (physicalWord N d.primeFactorsList).sum :=
      (universe_word_power hN cap w z hd).symm
    _ ≤ (N : ℝ) ^ ((physicalWord N r.primeFactorsList).sum + (R : ℝ) * tau) :=
      Real.rpow_le_rpow_of_exponent_le hN.le hcoord
    _ = (r : ℝ) * (N : ℝ) ^ ((R : ℝ) * tau) := by
      rw [Real.rpow_add (zero_lt_one.trans hN), universe_word_power hN cap w z hr]

/-- The caller supplies only the ORIGINAL source-form full-prefix level and
rank. The rounded level is derived from an actual same-fibre raw witness. -/
theorem rounded_full_prefix_level {N : ℕ} (hN : 1 < (N : ℝ))
    (keep : List ℕ → Bool) (cap b R : ℕ) (w z theta : ℝ)
    {tau : ℝ} (htau : 0 < tau)
    (hraw : ∀ r ∈ rawSupport keep N cap w z,
      ((b * r : ℕ) : ℝ) ≤ (N : ℝ) ^ theta ∧ r.primeFactorsList.length ≤ R)
    {d : ℕ} (hd : coefficient keep N cap w z tau d ≠ 0) :
    ((b * d : ℕ) : ℝ) ≤ (N : ℝ) ^ (theta + (R : ℝ) * tau) := by
  obtain ⟨hdU, r, hr, hl⟩ := coefficient_ne_zero_raw_fibre keep N cap w z tau hd
  have hdr := same_label_modulus_le hN cap w z htau hdU
    (rawSupport_subset_universe keep N cap w z hr) hl (hraw r hr).2
  calc
    ((b * d : ℕ) : ℝ) = (b : ℝ) * (d : ℝ) := by norm_cast
    _ ≤ (b : ℝ) * ((r : ℝ) * (N : ℝ) ^ ((R : ℝ) * tau)) :=
      mul_le_mul_of_nonneg_left hdr (Nat.cast_nonneg b)
    _ = ((b * r : ℕ) : ℝ) * (N : ℝ) ^ ((R : ℝ) * tau) := by push_cast; ring
    _ ≤ (N : ℝ) ^ theta * (N : ℝ) ^ ((R : ℝ) * tau) :=
      mul_le_mul_of_nonneg_right (hraw r hr).1 (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := (Real.rpow_add (zero_lt_one.trans hN) _ _).symm

/-- A nonzero actual small/rough output contains a nonzero rounded rough
coefficient and an actual beta divisor strictly below its small level. -/
theorem rho_nonzero_factors (keep : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) {q : ℕ} (hq : rho keep N cap w z tau L q ≠ 0) :
    ∃ e ∈ actualSmallRosserSupport N cap w, ∃ d ∈ universe N cap w z,
      q = e * d ∧ coefficient keep N cap w z tau d ≠ 0 ∧ (e : ℝ) < L := by
  have hs : q ∈ support N cap w z := by
    by_contra hs
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hs)
  obtain ⟨⟨e, d⟩, hed, heq⟩ := Finset.mem_image.mp hs
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  have hprod : rho keep N cap w z tau L (e * d) ≠ 0 := by
    simpa only [heq] using hq
  rw [rho_at_product keep N cap w z tau L he hd] at hprod
  have hc := (mul_ne_zero_iff.mp hprod).1
  have hb := (mul_ne_zero_iff.mp hprod).2
  have hel : (e : ℝ) < L := by
    by_cases hsign : 0 ≤ coefficient keep N cap w z tau d
    · rw [if_pos hsign] at hb
      exact (actualSmallRosserMinus_active hb).2.1
    · rw [if_neg hsign] at hb
      exact (actualSmallRosserPlus_active hb).2.1
  exact ⟨e, he, d, hd, heq.symm, hc, hel⟩

/-- The small beta factor is included in the SAME full physical modulus.
No unit bound on the eventual fibre-summed U6-U10-U11 sigma is inferred. -/
theorem rounded_rho_full_level {N : ℕ} (hN : 1 < (N : ℝ))
    (keep : List ℕ → Bool) (cap b R : ℕ) (w z theta ell : ℝ)
    {tau : ℝ} (htau : 0 < tau)
    (hraw : ∀ r ∈ rawSupport keep N cap w z,
      ((b * r : ℕ) : ℝ) ≤ (N : ℝ) ^ theta ∧ r.primeFactorsList.length ≤ R)
    {q : ℕ} (hq : rho keep N cap w z tau ((N : ℝ) ^ ell) q ≠ 0) :
    ((b * q : ℕ) : ℝ) ≤ (N : ℝ) ^ (theta + ell + (R : ℝ) * tau) := by
  obtain ⟨e, he, d, hd, rfl, hc, hel⟩ :=
    rho_nonzero_factors keep N cap w z tau ((N : ℝ) ^ ell) hq
  have hbd := rounded_full_prefix_level hN keep cap b R w z theta htau hraw hc
  calc
    ((b * (e * d) : ℕ) : ℝ) = (e : ℝ) * ((b * d : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (N : ℝ) ^ ell * (N : ℝ) ^ (theta + (R : ℝ) * tau) :=
      mul_le_mul hel.le hbd (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans hN)]; congr 1 <;> ring

/-- A single positive mesh is chosen from the strict exponent margin,
BEFORE N, the actual causal policy, cap, multiplier and arithmetic word. -/
theorem exists_uniform_mesh_physical_level (theta ell nu : ℝ) (R : ℕ)
    (hgap : theta + ell < nu) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ (keep : List ℕ → Bool) (cap b : ℕ) (w z : ℝ),
      (∀ r ∈ rawSupport keep N cap w z,
        ((b * r : ℕ) : ℝ) ≤ (N : ℝ) ^ theta ∧ r.primeFactorsList.length ≤ R) →
      ∀ q : ℕ, rho keep N cap w z tau ((N : ℝ) ^ ell) q ≠ 0 →
        ((b * q : ℕ) : ℝ) ≤ (N : ℝ) ^ nu := by
  let tau : ℝ := (nu - (theta + ell)) / ((R : ℝ) + 1)
  have htau : 0 < tau := by
    dsimp [tau]
    exact div_pos (sub_pos.mpr hgap) (by positivity)
  have hR : (R : ℝ) * tau ≤ nu - (theta + ell) := by
    have heq : tau * ((R : ℝ) + 1) = nu - (theta + ell) := by
      dsimp [tau]
      field_simp [show (R : ℝ) + 1 ≠ 0 by positivity]
    nlinarith
  refine ⟨tau, htau, ?_⟩
  intro N hN keep cap b w z hraw q hq
  exact (rounded_rho_full_level hN keep cap b R w z theta ell htau hraw hq).trans
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith))

/-- The full signed paired ledger from the second batch inherits ONE
physical exponent. Rounded lower and native upper fibres may overlap and
cancel; no unit bound on their signed aggregate is required. The only lower
level premise concerns ORIGINAL accepted raw histories. -/
theorem rounded_joint_sigma_physical_level
    (D : P2RoundedU6NativeJointLedger.RoundedLowerData)
    {n N : ℕ} {eta : ℚ} (hN : 1 < N) (heta : 0 < eta)
    (E : ℕ × ℕ → Prop) (theta ell nu : ℝ) (R : ℕ)
    (hnative : (153 / 256 : ℝ) ≤ nu)
    (hgates : ∀ t ∈ P2RoundedU6NativeJointLedger.lowerRows N E,
      0 < D.mesh t ∧ D.L t = (N : ℝ) ^ ell ∧
      theta + ell + (R : ℝ) * D.mesh t ≤ nu)
    (hraw : ∀ t ∈ P2RoundedU6NativeJointLedger.lowerRows N E,
      ∀ r ∈ rawSupport (D.policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
        (P5CausalRhoQuotientBridge.cutoff N),
        (((t.1 * t.2) * r : ℕ) : ℝ) ≤ (N : ℝ) ^ theta ∧
          r.primeFactorsList.length ≤ R)
    {q : ℕ} (hq : P2RoundedU6NativeJointLedger.sigma D n N eta E q ≠ 0) :
    (q : ℝ) ≤ (N : ℝ) ^ nu := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast hN
  by_cases hl : P2RoundedU6NativeJointLedger.lowerSigma D N E q = 0
  · have hu :
        P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q ≠ 0 := by
      intro hu
      exact hq (by simp [P2RoundedU6NativeJointLedger.sigma, hl, hu])
    have hp :=
      P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma_nonzero_profile
        hN heta hu
    exact hp.2.2.2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hNR.le hnative)
  · have hex : ∃ m ∈ (P2RoundedU6NativeJointLedger.lowerMarks D N E).filter
        (fun m => P2RoundedU6NativeJointLedger.lowerModulus m = q),
        P2RoundedU6NativeJointLedger.lowerRho D N m.1 m.2 ≠ 0 := by
      by_contra hn
      apply hl
      unfold P2RoundedU6NativeJointLedger.lowerSigma
      apply Finset.sum_eq_zero
      intro m hm
      by_contra hc
      exact hn ⟨m, hm, hc⟩
    obtain ⟨m, hm, hcoeff⟩ := hex
    obtain ⟨hmark, hmq⟩ := Finset.mem_filter.mp hm
    obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp hmark
    obtain ⟨htau, hL, hnu⟩ := hgates m.1 ht
    have hrho : rho (D.policy m.1) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w m.1)
        (P5CausalRhoQuotientBridge.cutoff N) (D.mesh m.1)
        ((N : ℝ) ^ ell) m.2 ≠ 0 := by
      simpa only [P2RoundedU6NativeJointLedger.lowerRho, hL] using hcoeff
    have hp := rounded_rho_full_level hNR (D.policy m.1)
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (m.1.1 * m.1.2) R
      (D.w m.1) (P5CausalRhoQuotientBridge.cutoff N) theta ell htau
      (hraw m.1 ht) hrho
    change (P2RoundedU6NativeJointLedger.lowerModulus m : ℝ) ≤ _ at hp
    rw [hmq] at hp
    exact hp.trans (Real.rpow_le_rpow_of_exponent_le hNR.le hnu)


end
end ImbalancedChen.P2RoundedCausalFibreLossAndLevel
