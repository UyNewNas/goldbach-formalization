import ImbalancedChen.P2EnhancedBadGamma5ArithmeticGeometry
import ImbalancedChen.P2FiniteMarkedGamma5LogProfileCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO ENDPOINT CREDIT.

The actual bad-Gamma5 source lies on the one plateau of an explicit smooth
logarithmic profile. Its prefix coordinate remains variable. The two ordered
prime slots, all canonical rough-tail slots, the equality-inclusive bad wall,
and the complete product are retained. The profile is evaluated on arbitrary
integer slots without a primality, coprimality, rho, or output-prime branch.

This is one geometry component, not a complete physical Licence or Family.
It does not assert equality with the sharp indicator away from source atoms,
pay a collar, supply a uniform rank bound, or estimate a PP/VM error.
The physical-log product gate gives exp(width)*N, not N^(1+width).
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5LogExtension

noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P4B
open P2SeedOmegaLiteralFibre (a0 a2)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedUnsiftedSource (pairLabels badPair)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels pair_data pair_eq pair_prod_pos)
open P2EnhancedBadGamma5ConstantCutoff (original_cutoff)
open scoped Classical BigOperators ContDiff

def fullProduct {r : ℕ} (d : ℕ) (qs : Fin 2 → ℕ) (rs : Fin r → ℕ) : ℕ :=
  d * qs 0 * qs 1 * ∏ i, rs i

def logPoint {r : ℕ} (d : ℕ) (qs : Fin 2 → ℕ) (rs : Fin r → ℕ) : Point r :=
  (log (d : ℝ), fun i => log (qs i : ℝ), fun i => log (rs i : ℝ))

/-- Pure geometric evaluation on all natural slots, including composite
ones. This definition is not the prime-only markedPhysicalWeight. -/
def integerExtension {r : ℕ} (N : ℕ) (Q width : ℝ)
    (d : ℕ) (qs : Fin 2 → ℕ) (rs : Fin r → ℕ) : ℝ :=
  profile (log Q) (log (N : ℝ)) width (logPoint d qs rs)

def raw {r : ℕ} (N : ℕ) (Q : ℝ) (d : ℕ)
    (qs : Fin 2 → ℕ) (rs : Fin r → ℕ) : Gate r → Prop
  | .lower i => (Q / d)^a0 ≤ (qs i : ℝ)
  | .upper i => (qs i : ℝ) < (Q / d)^a2
  | .pairOrder => qs 0 < qs 1
  | .badSquare => Q ≤ (d : ℝ) * (qs 0 : ℝ)^2 * (qs 1 : ℝ)
  | .rough i => (Q / d)^a0 ≤ (rs i : ℝ)
  | .tailOrder i j => rs i ≤ rs j
  | .product => fullProduct d qs rs ≤ N

theorem fullProduct_pos {r d : ℕ} {qs : Fin 2 → ℕ} {rs : Fin r → ℕ}
    (hd : 0 < d) (hq : ∀ i, 0 < qs i) (hr : ∀ i, 0 < rs i) :
    0 < fullProduct d qs rs :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd (hq 0)) (hq 1))
    (prod_pos (fun i _ => hr i))

theorem log_fullProduct {r d : ℕ} {qs : Fin 2 → ℕ} {rs : Fin r → ℕ}
    (hd : 0 < d) (hq : ∀ i, 0 < qs i) (hr : ∀ i, 0 < rs i) :
    log (fullProduct d qs rs : ℝ) =
      log (d : ℝ) + log (qs 0 : ℝ) + log (qs 1 : ℝ) + ∑ i, log (rs i : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  have hq' (i : Fin 2) : (qs i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hq i)).ne'
  have hr' (i : Fin r) : (rs i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hr i)).ne'
  have hp : (∏ i, (rs i : ℝ)) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => hr' i)
  simp only [fullProduct, Nat.cast_mul, Nat.cast_prod]
  rw [log_mul (mul_ne_zero (mul_ne_zero hd' (hq' 0)) (hq' 1)) hp,
    log_mul (mul_ne_zero hd' (hq' 0)) (hq' 1), log_mul hd' (hq' 0),
    log_prod (fun i _ => hr' i)]

/-- Exact raw/geometric dictionary. No slot is assumed prime. -/
theorem raw_iff_passed {r N d : ℕ} {Q : ℝ} {qs : Fin 2 → ℕ} {rs : Fin r → ℕ}
    (hN : 0 < N) (hd : 0 < d) (hR : 1 < Q / d)
    (hq : ∀ i, 0 < qs i) (hr : ∀ i, 0 < rs i) (g : Gate r) :
    raw N Q d qs rs g ↔ passed (log Q) (log (N : ℝ)) (logPoint d qs rs) g := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hq' (i : Fin 2) : (0 : ℝ) < qs i := Nat.cast_pos.mpr (hq i)
  have hr' (i : Fin r) : (0 : ℝ) < rs i := Nat.cast_pos.mpr (hr i)
  have hQ : 0 < Q := hd'.trans (by simpa only [one_mul] using (lt_div_iff₀ hd').mp hR)
  have hR0 : 0 < Q / (d : ℝ) := zero_lt_one.trans hR
  have hlo (p : ℕ) (hp : 0 < p) (a : ℝ) :
      (Q / d)^a ≤ (p : ℝ) ↔ 0 ≤ log (p : ℝ) - a * (log Q - log (d : ℝ)) := by
    rw [← log_le_log_iff (rpow_pos_of_pos hR0 a) (Nat.cast_pos.mpr hp),
      log_rpow hR0, log_div hQ.ne' hd'.ne', sub_nonneg]
  have hhi (p : ℕ) (hp : 0 < p) (a : ℝ) :
      (p : ℝ) < (Q / d)^a ↔ 0 < a * (log Q - log (d : ℝ)) - log (p : ℝ) := by
    rw [← log_lt_log_iff (Nat.cast_pos.mpr hp) (rpow_pos_of_pos hR0 a),
      log_rpow hR0, log_div hQ.ne' hd'.ne', sub_pos]
  cases g with
  | lower i => exact hlo (qs i) (hq i) a0
  | upper i => exact hhi (qs i) (hq i) a2
  | rough i => exact hlo (rs i) (hr i) a0
  | pairOrder =>
      change qs 0 < qs 1 ↔ 0 < log (qs 1 : ℝ) - log (qs 0 : ℝ)
      rw [sub_pos, log_lt_log_iff (hq' 0) (hq' 1)]
      exact Nat.cast_lt.symm
  | tailOrder i j =>
      change rs i ≤ rs j ↔ 0 ≤ log (rs j : ℝ) - log (rs i : ℝ)
      rw [sub_nonneg, log_le_log_iff (hr' i) (hr' j)]
      exact Nat.cast_le.symm
  | badSquare =>
      change Q ≤ (d : ℝ) * (qs 0 : ℝ)^2 * (qs 1 : ℝ) ↔
        0 ≤ log (d : ℝ) + 2 * log (qs 0 : ℝ) + log (qs 1 : ℝ) - log Q
      rw [sub_nonneg, ← log_le_log_iff hQ (mul_pos (mul_pos hd' (pow_pos (hq' 0) 2)) (hq' 1)),
        log_mul (mul_pos hd' (pow_pos (hq' 0) 2)).ne' (hq' 1).ne',
        log_mul hd'.ne' (pow_pos (hq' 0) 2).ne', log_pow]
      norm_num
  | product =>
      change fullProduct d qs rs ≤ N ↔
        0 ≤ log (N : ℝ) - (log (d : ℝ) + log (qs 0 : ℝ) + log (qs 1 : ℝ) +
          ∑ i, log (rs i : ℝ))
      rw [sub_nonneg, ← log_fullProduct hd hq hr,
        log_le_log_iff (Nat.cast_pos.mpr (fullProduct_pos hd hq hr)) (Nat.cast_pos.mpr hN)]
      exact Nat.cast_le.symm

/-- A fixed physical-log width gives a fixed multiplicative product cap.
This is the upper-support scale required by the existing Family interface. -/
theorem integerExtension_product_lt {r N d : ℕ} {Q width : ℝ}
    {qs : Fin 2 → ℕ} {rs : Fin r → ℕ}
    (hN : 0 < N) (hd : 0 < d) (hq : ∀ i, 0 < qs i) (hr : ∀ i, 0 < rs i)
    (hw : 0 < width) (hne : integerExtension N Q width d qs rs ≠ 0) :
    (fullProduct d qs rs : ℝ) < exp width * (N : ℝ) := by
  have hm := profile_nonzero_margin hw hne Gate.product (mem_program.mpr trivial)
  change -width < log (N : ℝ) -
    (log (d : ℝ) + log (qs 0 : ℝ) + log (qs 1 : ℝ) + ∑ i, log (rs i : ℝ)) at hm
  rw [← log_fullProduct hd hq hr] at hm
  have hl : log (fullProduct d qs rs : ℝ) < width + log (N : ℝ) := by linarith
  have he := exp_lt_exp.mpr hl
  simpa only [exp_log (Nat.cast_pos.mpr (fullProduct_pos hd hq hr)), exp_add,
    exp_log (Nat.cast_pos.mpr hN)] using he

def sourcePair (qs : List ℕ) : Fin 2 → ℕ := ![qs.getD 0 0, qs.getD 1 0]

def canonicalTail (m : ℕ) (i : Fin m.primeFactorsList.length) : ℕ :=
  m.primeFactorsList[i.val]

theorem canonicalTail_list (m : ℕ) : List.ofFn (canonicalTail m) = m.primeFactorsList := by
  exact List.ofFn_getElem

theorem canonicalTail_product {m : ℕ} (hm : 0 < m) : (∏ i, canonicalTail m i) = m := by
  rw [← List.prod_ofFn, canonicalTail_list, Nat.prod_primeFactorsList hm.ne']

theorem canonicalTail_mem (m : ℕ) (i : Fin m.primeFactorsList.length) :
    canonicalTail m i ∈ m.primeFactorsList := List.getElem_mem i.isLt

theorem canonicalTail_prime (m : ℕ) (i : Fin m.primeFactorsList.length) :
    (canonicalTail m i).Prime := Nat.prime_of_mem_primeFactorsList (canonicalTail_mem m i)

theorem canonicalTail_order (m : ℕ) (i j : Fin m.primeFactorsList.length) (h : i < j) :
    canonicalTail m i ≤ canonicalTail m j :=
  (List.pairwise_iff_getElem.mp (Nat.primeFactorsList_sorted m).pairwise)
    i.val j.val i.isLt j.isLt h

theorem sourcePair_mem {N d : ℕ} {Q : ℝ} {qs : List ℕ}
    (hq : qs ∈ pairLabels N Q d) (i : Fin 2) :
    sourcePair qs i ∈ primeWindow N (cutoff Q d (227/50)) (cutoff Q d (29/10)) := by
  have h : sourcePair qs i ∈ primeWindow N ((Q / d)^a0) ((Q / d)^a2) := by
    apply (pair_data hq).2.2
    rw [pair_eq hq]
    fin_cases i <;> simp [sourcePair]
  simpa only [cutoff,
    show (1 / (227/50) : ℝ) = a0 by norm_num [a0],
    show (1 / (29/10) : ℝ) = a2 by norm_num [a2]] using h

/-- The tail product is m even when m=1; equal-product old marks are not
identified or discarded by this map. -/
theorem source_fullProduct {N d m : ℕ} {Q : ℝ} {qs : List ℕ}
    (hq : qs ∈ pairLabels N Q d) (hm : 0 < m) :
    fullProduct d (sourcePair qs) (canonicalTail m) = d * qs.prod * m := by
  have hp : qs.prod = sourcePair qs 0 * sourcePair qs 1 := by
    simpa [sourcePair] using congrArg List.prod (pair_eq hq)
  unfold fullProduct
  rw [canonicalTail_product hm, hp]
  ring

theorem source_fullProduct_unit {N d : ℕ} {Q : ℝ} {qs : List ℕ}
    (hq : qs ∈ pairLabels N Q d) :
    fullProduct d (sourcePair qs) (canonicalTail 1) = d * qs.prod := by
  simpa only [mul_one] using source_fullProduct (d := d) hq (show 0 < (1 : ℕ) by decide)

theorem canonicalTail_unit_length : (1 : ℕ).primeFactorsList.length = 0 := by decide

/-- Actual Γ5 labels and inclusive rough tails supply every raw gate.
No smooth-family admission or distribution estimate is an input. -/
theorem actual_raw {N d m : ℕ} {Q : ℝ} {qs : List ℕ}
    (hd : 0 < d) (hq : qs ∈ badLabels N Q d)
    (hm : m ∈ roughNumbers ((N : ℝ) / (d * qs.prod : ℕ)) (cutoff Q d (227/50))) :
    ∀ g ∈ program m.primeFactorsList.length,
      raw N Q d (sourcePair qs) (canonicalTail m) g := by
  have hpair := (mem_filter.mp hq).1
  have hm0 := (mem_roughNumbers.mp hm).1
  have hD := Nat.mul_pos hd (pair_prod_pos hpair)
  intro g hg
  cases g with
  | lower i =>
      change (Q / d)^a0 ≤ (sourcePair qs i : ℝ)
      rw [← original_cutoff Q d]
      exact (mem_primeWindow.mp (sourcePair_mem hpair i)).2.2.1
  | upper i =>
      change (sourcePair qs i : ℝ) < (Q / d)^a2
      simpa only [cutoff, show (1 / (29/10) : ℝ) = a2 by norm_num [a2]] using
        (mem_primeWindow.mp (sourcePair_mem hpair i)).2.2.2
  | pairOrder =>
      have h := (pair_data hpair).2.1
      rw [pair_eq hpair] at h
      simpa [raw, sourcePair] using h
  | badSquare =>
      simpa only [raw, sourcePair, Matrix.cons_val_zero, Matrix.cons_val_one, badPair] using
        (mem_filter.mp hq).2
  | rough i =>
      change (Q / d)^a0 ≤ (canonicalTail m i : ℝ)
      rw [← original_cutoff Q d]
      exact (mem_roughNumbers.mp hm).2.2 (canonicalTail m i) (canonicalTail_prime m i)
        (Nat.dvd_of_mem_primeFactorsList (canonicalTail_mem m i))
  | tailOrder i j =>
      exact canonicalTail_order m i j (mem_program.mp hg)
  | product =>
      change fullProduct d (sourcePair qs) (canonicalTail m) ≤ N
      rw [source_fullProduct hpair hm0]
      have h := (le_div_iff₀ (Nat.cast_pos.mpr hD)).mp (mem_roughNumbers.mp hm).2.1
      have hn : m * (d * qs.prod) ≤ N := by exact_mod_cast h
      simpa only [Nat.mul_comm] using hn

/-- The actual source atom is on the one plateau. This does not identify
the strict sharp indicator with the outer profile on the collar. -/
theorem actual_source_one {N d m : ℕ} {Q width : ℝ} {qs : List ℕ}
    (hN : 0 < N) (hd : 0 < d) (hR : 1 < Q / d) (hw : 0 < width)
    (hq : qs ∈ badLabels N Q d)
    (hm : m ∈ roughNumbers ((N : ℝ) / (d * qs.prod : ℕ)) (cutoff Q d (227/50))) :
    integerExtension N Q width d (sourcePair qs) (canonicalTail m) = 1 := by
  unfold integerExtension
  apply profile_one hw
  intro g hg
  apply (raw_iff_passed hN hd hR
    (fun i => (mem_primeWindow.mp (sourcePair_mem (mem_filter.mp hq).1 i)).1.pos)
    (fun i => (canonicalTail_prime m i).pos) g).mp
  exact actual_raw hd hq hm g hg

/-- All original marks and tests remain outside the geometric replacement.
F may retain the additive-prime test, a congruence, or a coprimality test.
No two occurrences are merged merely because their products agree. -/
theorem marked_source_test_unchanged {α : Type*} (B : Finset α)
    (word : α → ℕ) (σ : α → ℝ) (F : α → List ℕ → ℕ → ℝ)
    {N : ℕ} {Q width : ℝ} (hN : 0 < N) (hw : 0 < width)
    (hd : ∀ a ∈ B, 0 < word a) (hR : ∀ a ∈ B, 1 < Q / word a) :
    (∑ a ∈ B, σ a * ∑ qs ∈ badLabels N Q (word a),
      ∑ m ∈ roughNumbers ((N : ℝ) / (word a * qs.prod : ℕ)) (cutoff Q (word a) (227/50)),
        F a qs m * integerExtension N Q width (word a) (sourcePair qs) (canonicalTail m)) =
      ∑ a ∈ B, σ a * ∑ qs ∈ badLabels N Q (word a),
        ∑ m ∈ roughNumbers ((N : ℝ) / (word a * qs.prod : ℕ)) (cutoff Q (word a) (227/50)),
          F a qs m := by
  apply sum_congr rfl
  intro a ha
  apply congrArg (fun x : ℝ => σ a * x)
  apply sum_congr rfl
  intro qs hqs
  apply sum_congr rfl
  intro m hm
  rw [actual_source_one hN (hd a ha) (hR a ha) hw hqs hm, mul_one]

end
end ImbalancedChen.P2FiniteMarkedGamma5LogExtension
