import ImbalancedChen.P4ACommonPolicyTaggedCompiler
import ImbalancedChen.P5ActualCommonRefinedRange
import ImbalancedChen.P4ASpliceDifferenceLowerModulus
import ImbalancedChen.P2LowerCanonicalRetainedTrace

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

This file supplies the missing rank and fine-cell support conversion for
O/P's EXISTING compiledRho. The actual raw support supplier is reused from
P5ActualCommonRefinedRange; it includes short and inherited words. Its
constructor remains the held eleven-cell-sixth / PhysicalRows-eighth
constructor. This file does not identify it with the original full87 policy,
construct finite higher caps, pay a density error, or prove a mixed-wall cover.

The small beta factor and the rounded rough factor belong to this same
compiledRho. No replacement rho, abstract support record or hSupport is used.
-/

namespace ImbalancedChen.P4AHeldTaggedCompilerSupport
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P4AUpperTaggedParityCompiler
open P5Z.ActualCommonRefinedRange

/-- Fixed before the target and before the fine atoms. -/
def J0 (omega : ℝ) : ℕ := ⌈(599 / 1000 : ℝ) / omega⌉₊ + 3

theorem J0_spec (omega : ℝ) : (599 / 1000 : ℝ) / omega + 2 < (J0 omega : ℝ) := by
  have hc := Nat.le_ceil ((599 / 1000 : ℝ) / omega)
  dsimp only [J0]
  push_cast
  linarith

/-- The genuine held raw support, not the complete divisor universe, has
one uniform rank. The original raw support theorem already covers d=1,
short words and every inherited branch. -/
theorem held_raw_rank_lt_J0 (data : OriginalData) (he : 0 ≤ data.e)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N) (z : ℝ)
    {d : ℕ}
    (hd : d ∈ rawSupport (P4ACommonPolicyTaggedCompiler.heldRetain data N)
      N cap ((N : ℝ) ^ omega) z) :
    d.primeFactorsList.length < J0 omega := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hlo := P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
    (P4ACommonPolicyTaggedCompiler.heldRetain data N) N cap
    (Real.rpow_nonneg hn0.le omega) z hd
  have hhi := actualRoughSupport_lt_theta data he N cap ((N : ℝ) ^ omega) z hN hd
  have hpow : (N : ℝ) ^ (omega * (d.primeFactors.card : ℝ)) ≤
      (N : ℝ) ^ (299 / 500 : ℝ) := by
    rw [Real.rpow_mul hn0.le, Real.rpow_natCast]
    exact hlo.trans hhi.le
  have hcard := (Real.rpow_le_rpow_left_iff hn).mp hpow
  have hsf := fixedRoughSupport_squarefree
    (P4ACommonPolicyTaggedCompiler.heldRetain data N) N cap ((N : ℝ) ^ omega) z hd
  have hlength : d.primeFactorsList.length = d.primeFactors.card := by
    change d.primeFactorsList.length = d.primeFactorsList.toFinset.card
    exact (List.toFinset_card_of_nodup hsf.nodup_primeFactorsList).symm
  have hdiv : (d.primeFactors.card : ℝ) ≤ (599 / 1000 : ℝ) / omega := by
    apply (le_div_iff₀ homega).mpr
    nlinarith
  have hlt : (d.primeFactors.card : ℝ) < (J0 omega : ℝ) := by
    linarith [J0_spec omega]
  rw [hlength]
  exact_mod_cast hlt

/-- ALL/ANY rounding cannot create a new rough rank: every outer cell
contains an actual retained modulus with exactly the same label length. -/
theorem held_outer_rank_lt_J0 (data : OriginalData) (he : 0 ≤ data.e)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N) (z tau : ℝ)
    {d : ℕ}
    (hd : outer (P4ACommonPolicyTaggedCompiler.heldRetain data N)
      (P4ACommonPolicyTaggedCompiler.historicalTag data N)
      N cap ((N : ℝ) ^ omega) z tau d) :
    d.primeFactorsList.length < J0 omega := by
  obtain ⟨e, hecell⟩ := hd
  obtain ⟨hc, hr⟩ := Finset.mem_inter.mp hecell
  rw [← cell_rank_preserved _ _ _ _ _ _ hc]
  exact held_raw_rank_lt_J0 data he omega homega N cap hN z hr

theorem held_crossing_rank_lt_J0 (data : OriginalData) (he : 0 ≤ data.e)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N) (z tau : ℝ)
    {d : ℕ}
    (hd : crossing (P4ACommonPolicyTaggedCompiler.heldRetain data N)
      (P4ACommonPolicyTaggedCompiler.historicalTag data N)
      N cap ((N : ℝ) ^ omega) z tau d) :
    d.primeFactorsList.length < J0 omega :=
  held_outer_rank_lt_J0 data he omega homega N cap hN z tau hd.1

private theorem rpow_logCoordinate (N : ℕ) (hN : 2 ≤ N) (p : ℕ) (hp : 0 < p) :
    (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ)) = (p : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hn),
    mul_div_cancel₀ _ (Real.log_pos hn).ne', Real.exp_log hpR]

private theorem same_primeLabel_product_factor (N : ℕ) (hN : 2 ≤ N)
    (tau : ℝ) (htau : 0 < tau) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hl : primeLabel N tau p = primeLabel N tau q) :
    (p : ℝ) ≤ (N : ℝ) ^ tau * (q : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hdiff := (abs_lt.mp (same_primeLabel_coordinate_distance_lt N htau hl)).2
  have hlog : Real.log (p : ℝ) / Real.log (N : ℝ) ≤
      tau + Real.log (q : ℝ) / Real.log (N : ℝ) := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hn.le hlog
  rw [rpow_logCoordinate N hN p hp,
    Real.rpow_add (zero_lt_one.trans hn), rpow_logCoordinate N hN q hq] at hpow
  exact hpow

private theorem same_label_list_product (N : ℕ) (hN : 2 ≤ N)
    (tau : ℝ) (htau : 0 < tau) (ps qs : List ℕ)
    (hp : ∀ p ∈ ps, 0 < p) (hq : ∀ q ∈ qs, 0 < q)
    (hl : ps.map (primeLabel N tau) = qs.map (primeLabel N tau)) :
    (ps.prod : ℝ) ≤ ((N : ℝ) ^ tau) ^ ps.length * (qs.prod : ℝ) := by
  induction ps generalizing qs with
  | nil =>
      have heq : qs = [] := List.map_eq_nil_iff.mp hl.symm
      subst qs
      simp
  | cons p ps ih =>
      cases qs with
      | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hl
      | cons q qs =>
          have hh := List.cons.inj hl
          have hp0 := hp p (by simp)
          have hq0 := hq q (by simp)
          have hhead := same_primeLabel_product_factor N hN tau htau p q hp0 hq0 hh.1
          have htail := ih qs (fun r hr => hp r (List.mem_cons_of_mem p hr))
            (fun r hr => hq r (List.mem_cons_of_mem q hr)) hh.2
          have h := mul_le_mul hhead htail (Nat.cast_nonneg ps.prod)
            (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg q))
          simpa only [List.prod_cons, Nat.cast_mul, List.length_cons, pow_succ,
            mul_assoc, mul_comm, mul_left_comm] using h

/-- A genuine fine labelled cell changes the complete modulus by at most
N^(tau*rank). No independent endpoint vector or hypothetical support is used. -/
theorem same_cell_product_le (tag : ℕ → List Bool) (N cap : ℕ) (hN : 2 ≤ N)
    (w z tau : ℝ) (htau : 0 < tau) {d e : ℕ}
    (hd : d ∈ universe N cap w z) (he : e ∈ cell tag N cap w z tau d) :
    (d : ℝ) ≤ (N : ℝ) ^ (tau * (d.primeFactorsList.length : ℝ)) * (e : ℝ) := by
  obtain ⟨hdsub, hdprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe
    N cap w z hd
  obtain ⟨hesub, heprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe
    N cap w z (Finset.mem_filter.mp he).1
  have hlabels : d.primeFactorsList.reverse.map (primeLabel N tau) =
      e.primeFactorsList.reverse.map (primeLabel N tau) :=
    (cell_prime_labels tag N cap w z tau he).symm
  have h := same_label_list_product N hN tau htau d.primeFactorsList.reverse
    e.primeFactorsList.reverse
    (fun p hp => (mem_roughPrimeUniverse_prime (hdsub.subset hp)).pos)
    (fun p hp => (mem_roughPrimeUniverse_prime (hesub.subset hp)).pos) hlabels
  rw [hdprod, heprod, List.length_reverse] at h
  rw [Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_natCast]
  exact h

/-- The exact existing compiler, before beta attachment, has the claimed
rank inflation bound on every active coefficient, including positive outer
rounding. A negative inner coefficient uses its own retained witness. -/
theorem held_compiled_rough_lt (data : OriginalData) (he : 0 ≤ data.e)
    (omega : ℝ) (homega : 0 < omega) (N cap : ℕ) (hN : 2 ≤ N)
    (z tau : ℝ) (htau : 0 < tau) {d : ℕ}
    (hd : P4ACommonPolicyTaggedCompiler.compiledCoefficient data N cap
      ((N : ℝ) ^ omega) z tau d ≠ 0) :
    d.primeFactorsList.length < J0 omega ∧
      (d : ℝ) < (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (J0 omega : ℝ)) := by
  obtain ⟨e, heraw, hecell, _htag, _hlabels⟩ := active_has_raw_witness
    (P4ACommonPolicyTaggedCompiler.heldRetain data N)
    (P4ACommonPolicyTaggedCompiler.historicalTag data N)
    N cap ((N : ℝ) ^ omega) z tau hd
  have hrank : d.primeFactorsList.length < J0 omega := by
    rw [← cell_rank_preserved _ _ _ _ _ _ hecell]
    exact held_raw_rank_lt_J0 data he omega homega N cap hN z heraw
  have hdU : d ∈ universe N cap ((N : ℝ) ^ omega) z := by
    by_contra hn
    exact hd (by simp only [P4ACommonPolicyTaggedCompiler.compiledCoefficient,
      coefficient, if_neg hn])
  have hprod := same_cell_product_le _ N cap hN _ z tau htau hdU hecell
  have hraw := actualRoughSupport_lt_theta data he N cap ((N : ℝ) ^ omega) z hN heraw
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  refine ⟨hrank, ?_⟩
  calc
    (d : ℝ) ≤ (N : ℝ) ^ (tau * (d.primeFactorsList.length : ℝ)) * (e : ℝ) := hprod
    _ < (N : ℝ) ^ (tau * (d.primeFactorsList.length : ℝ)) *
        (N : ℝ) ^ (299 / 500 : ℝ) :=
      mul_lt_mul_of_pos_left hraw (Real.rpow_pos_of_pos hn0 _)
    _ = (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (d.primeFactorsList.length : ℝ)) := by
      rw [Real.rpow_add hn0]
      ring
    _ ≤ (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (J0 omega : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      have hr : (d.primeFactorsList.length : ℝ) ≤ (J0 omega : ℝ) := by
        exact_mod_cast hrank.le
      exact add_le_add_left (mul_le_mul_of_nonneg_left hr htau.le) _

/-- This factorization is of the SAME O/P compiledRho. The active small
factor uses the sign chosen by its actual compiled rough coefficient. -/
theorem held_compiledRho_nonzero_factors (data : OriginalData)
    (N cap : ℕ) (w z tau L : ℝ) {q : ℕ}
    (hq : P4ACommonPolicyTaggedCompiler.compiledRho data N cap w z tau L q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w, ∃ d ∈ universe N cap w z,
      q = a * d ∧ (a : ℝ) < L ∧
        P4ACommonPolicyTaggedCompiler.compiledCoefficient data N cap w z tau d ≠ 0 := by
  have hm : q ∈ P4AUpperTaggedBetaAttachment.support N cap w z := by
    by_contra hn
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hn)
  obtain ⟨⟨a, d⟩, had, hprod⟩ := Finset.mem_image.mp hm
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  have hv := P4AUpperTaggedBetaAttachment.rho_at_product
    (P4ACommonPolicyTaggedCompiler.heldRetain data N)
    (P4ACommonPolicyTaggedCompiler.historicalTag data N) N cap w z tau L ha hd
  have hp : P4ACommonPolicyTaggedCompiler.compiledCoefficient data N cap w z tau d *
      (if 0 ≤ P4ACommonPolicyTaggedCompiler.compiledCoefficient data N cap w z tau d
       then actualSmallRosserPlus N cap w L a else actualSmallRosserMinus N cap w L a) ≠ 0 := by
    rw [← hv, hprod]
    exact hq
  obtain ⟨hc, hb⟩ := mul_ne_zero_iff.mp hp
  refine ⟨a, ha, d, hd, hprod.symm, ?_, hc⟩
  split_ifs at hb with hs
  · exact (actualSmallRosserPlus_active hb).2.1
  · exact (actualSmallRosserMinus_active hb).2.1

theorem held_compiledRho_support (data : OriginalData) (he : 0 ≤ data.e)
    (omega ell tau : ℝ) (homega : 0 < omega) (htau : 0 < tau)
    (hbudget : ell + tau * (J0 omega : ℝ) < 1 / 1000)
    (N cap : ℕ) (hN : 2 ≤ N) (z : ℝ) {q : ℕ}
    (hq : P4ACommonPolicyTaggedCompiler.compiledRho data N cap
      ((N : ℝ) ^ omega) z tau ((N : ℝ) ^ ell) q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  obtain ⟨a, _ha, d, _hd, hprod, haL, hc⟩ :=
    held_compiledRho_nonzero_factors data N cap _ z tau _ hq
  have hdR := (held_compiled_rough_lt data he omega homega N cap hN z tau htau hc).2
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  calc
    (q : ℝ) = (a : ℝ) * (d : ℝ) := by rw [hprod, Nat.cast_mul]
    _ ≤ (N : ℝ) ^ ell * (d : ℝ) :=
      mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg _)
    _ < (N : ℝ) ^ ell *
        (N : ℝ) ^ ((299 / 500 : ℝ) + tau * (J0 omega : ℝ)) :=
      mul_lt_mul_of_pos_left hdR (Real.rpow_pos_of_pos hn0 _)
    _ = (N : ℝ) ^ (ell + (299 / 500 : ℝ) + tau * (J0 omega : ℝ)) := by
      rw [add_assoc, Real.rpow_add hn0]
    _ ≤ (N : ℝ) ^ (599 / 1000 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      linarith

/-- A real pre-N support schedule: all later fine widths below tau0 work,
for every original data set, target, enumeration cap, and active coefficient
of O/P's exact compiledRho. This pays SUPPORT only, not either error reserve. -/
theorem exists_preN_held_compiled_support (omega ell : ℝ)
    (homega : 0 < omega) (hell : ell < 1 / 1000) :
    ∃ tau0 : ℝ, 0 < tau0 ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
        ell + tau * (J0 omega : ℝ) < 1 / 1000 ∧
          ∀ data : OriginalData, 0 ≤ data.e → ∀ N cap : ℕ, 2 ≤ N → ∀ z : ℝ,
            ∀ q : ℕ, P4ACommonPolicyTaggedCompiler.compiledRho data N cap
              ((N : ℝ) ^ omega) z tau ((N : ℝ) ^ ell) q ≠ 0 →
                (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  let tau0 : ℝ := (1 / 1000 - ell) / (2 * ((J0 omega : ℝ) + 1))
  have hj : 0 ≤ (J0 omega : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 2 * ((J0 omega : ℝ) + 1) := by positivity
  have ht0 : 0 < tau0 := div_pos (by linarith) hden
  have htEq : tau0 * (2 * ((J0 omega : ℝ) + 1)) = 1 / 1000 - ell :=
    div_mul_cancel₀ _ hden.ne'
  refine ⟨tau0, ht0, ?_⟩
  intro tau htau htmax
  have hcost : tau * (J0 omega : ℝ) ≤ tau0 * (J0 omega : ℝ) :=
    mul_le_mul_of_nonneg_right htmax hj
  have hbudget : ell + tau * (J0 omega : ℝ) < 1 / 1000 := by nlinarith
  refine ⟨hbudget, ?_⟩
  intro data he N cap hN z q hq
  exact held_compiledRho_support data he omega ell tau homega htau hbudget N cap hN z hq

end
end ImbalancedChen.P4AHeldTaggedCompilerSupport
