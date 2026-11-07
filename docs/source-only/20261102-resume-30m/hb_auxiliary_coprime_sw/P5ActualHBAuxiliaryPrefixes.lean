import ImbalancedChen.P5ActualHBGroupLogAbelPrefix
import ImbalancedChen.P5ActualRoughMobiusConvolution

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal HB prefixes with every auxiliary k.  The coprime mask is placed in
the coefficient only to use the already proved Abel identity; its exact
auxiliary mass is proved equal to the original k*q mean.  Arithmetic
cancellation at k=1 is NOT postulated.  Every right side is a computed
finite prefix maximum or an explicit elementary removal cost.
-/
namespace ImbalancedChen.P5Z.ActualHBAuxiliaryPrefixes
noncomputable section
open Classical Finset Set MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3
open OriginalBetaPrimeSource OriginalBetaPrimeHalfOpenSW
open ActualRoughHeathBrownWords ActualHBGroupLogAbelPrefix
open ActualHBGroupLogLine OriginalGroupLogAbelVariation
open PrimeMellinProfileVariation20261026b

def coprimeMask (c : ℕ → ℂ) (k : ℕ) (n : ℕ) : ℂ :=
  if n.Coprime k then c n else 0

/-- Count and mean keep the same coefficient.  In particular the right
side's coprime mean is exactly (n,k*q)=1, not merely (n,q)=1. -/
theorem auxiliary_eq_mask (S : Finset ℕ) (c : ℕ → ℂ) (k q b : ℕ) :
    auxiliarySWError S c k q b = auxiliarySWError S (coprimeMask c k) 1 q b := by
  unfold auxiliarySWError
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hq : Nat.ModEq q n b <;> by_cases hk : n.Coprime k <;>
      simp [coprimeMask,hq,hk]
  · congr 1
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hq : n.Coprime q <;> by_cases hk : n.Coprime k <;>
      simp [coprimeMask,Nat.coprime_mul_iff_right,hq,hk]

theorem mask_mul (f c : ℕ → ℂ) (k : ℕ) :
    coprimeMask (fun n => f n*c n) k = fun n => f n*coprimeMask c k n := by
  funext n
  by_cases h : n.Coprime k <;> simp [coprimeMask,h]

def auxiliaryPrefixNorm (c : ℕ → ℂ) (u v : ℝ) (k q b : ℕ) : ℝ :=
  prefixNorm (coprimeMask c k) u v q b

theorem prefix_mask_eq_auxiliary (c : ℕ → ℂ) (u : ℝ) (h k q b : ℕ) :
    prefix (coprimeMask c k) u q b h =
      auxiliarySWError (Finset.Ioc (Nat.floor u) h) c k q b := by
  rw [auxiliary_eq_mask,error_eq_kernel]
  rfl

theorem auxiliaryPrefixNorm_nonneg (c : ℕ → ℂ) (u v : ℝ) (k q b : ℕ) :
    0 ≤ auxiliaryPrefixNorm c u v k q b := prefixNorm_nonneg _ _ _ _ _

theorem prefixNorm_mono_upper (c : ℕ → ℂ) (u : ℝ) {v w : ℝ}
    (hvw : v ≤ w) (q b : ℕ) : prefixNorm c u v q b ≤ prefixNorm c u w q b := by
  apply Finset.sup'_le
  intro h hh
  apply Finset.le_sup'
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hh)
    (Nat.add_le_add_right (Nat.floor_mono hvw) 1))

/-- A bounded rough coefficient costs its displayed amplitude M.  The
proof counts its support; it never divides or renormalizes the coefficient. -/
theorem bounded_rough_auxiliary_removal
    (S : Finset ℕ) (c : ℕ → ℂ) (H k q b : ℕ) (z M : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hM : 0 ≤ M) (hc : ∀ n ∈ S, ‖c n‖ ≤ M)
    (hr : ∀ n ∈ S, c n ≠ 0 → ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S c k q b - auxiliarySWError S c 1 q b‖ ≤
      2*M*(k.divisors.card : ℝ)*(H : ℝ)/z := by
  let e : ℕ → ℂ := fun n => if c n ≠ 0 then 1 else 0
  have he : ∀ n ∈ S, ‖e n‖ ≤ 1 := by
    intro n hn
    dsimp [e]
    split_ifs <;> norm_num
  have her : ∀ n ∈ S, e n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ) := by
    intro n hn hne p hp hpn
    apply hr n hn _ p hp hpn
    intro hc0
    exact hne (by simp [e,hc0])
  have hmass : (∑ n ∈ S with ¬n.Coprime k, ‖c n‖) ≤
      M*(∑ n ∈ S with ¬n.Coprime k, ‖e n‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hc0 : c n = 0
    · simp [e,hc0]
    · simpa [e,hc0] using hc n (Finset.mem_filter.mp hn).1
  have hcount := sum_norm_not_coprime_le_rough S e H k z hS hz hk he her
  have hcard : (k.primeFactors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (show k.primeFactors ⊆ k.divisors by
      rw [Nat.primeFactors_eq_to_filter_divisors_prime]
      exact Finset.filter_subset _ _)
  calc
    _ ≤ 2*(∑ n ∈ S with ¬n.Coprime k, ‖c n‖) :=
      auxiliarySWError_sub_one_norm_le_bad_mass S c k q b hq
    _ ≤ 2*(M*((k.primeFactors.card : ℝ)*(H : ℝ)/z)) :=
      mul_le_mul_of_nonneg_left
        (hmass.trans (mul_le_mul_of_nonneg_left hcount hM)) (by norm_num)
    _ ≤ 2*(M*((k.divisors.card : ℝ)*(H : ℝ)/z)) := by
      gcongr
    _ = _ := by ring

def roleAmplitude (role : Role) (H : ℕ) : ℝ :=
  match role with
  | .logarithm => Real.log (max (H : ℝ) 1)
  | _ => 1

theorem roleAmplitude_nonneg (role : Role) (H : ℕ) : 0 ≤ roleAmplitude role H := by
  cases role <;> simp only [roleAmplitude]
  · norm_num
  · norm_num
  · exact Real.log_nonneg (le_max_right _ _)

theorem actual_rough_support (z y : ℝ) (role : Role) (n : ℕ)
    (hn : actual z y role n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ) := by
  cases role with
  | one => exact roughOneSlot_support z n hn
  | logarithm =>
    apply roughOneSlot_support z n
    intro hz0
    exact hn (by simp [actual,roughLog,hz0])
  | mobius =>
    apply roughMoebiusSlot_support z n
    intro hz0
    exact hn (by simp [actual,roughMuTrunc,hz0])

theorem actual_norm_le_roleAmplitude (z y : ℝ) (role : Role)
    {n H : ℕ} (hn : 0 < n) (hH : n ≤ H) :
    ‖actual z y role n‖ ≤ roleAmplitude role H := by
  cases role with
  | one => exact roughOneSlot_norm_le z n
  | mobius => exact roughMuTrunc_norm_le z y n
  | logarithm =>
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
    have hlog : Real.log (n : ℝ) ≤ Real.log (max (H : ℝ) 1) :=
      Real.log_le_log hn0 ((by exact_mod_cast hH : (n : ℝ) ≤ H).trans (le_max_left _ _))
    simp only [actual,roughLog,roleAmplitude,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn1)]
    exact (mul_le_mul_of_nonneg_left (roughOneSlot_norm_le z n)
      (Real.log_nonneg hn1)).trans (by simpa using hlog)

/-- Every original role, including its log numerator and real Mobius
cutoff, has auxiliary loss tau(k)^1 with no k-dependent threshold. -/
theorem actual_auxiliary_removal (z y : ℝ) (role : Role)
    (S : Finset ℕ) (H k q b : ℕ) (hS : S ⊆ Finset.Ioc 0 H)
    (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (actual z y role) k q b -
      auxiliarySWError S (actual z y role) 1 q b‖ ≤
      2*roleAmplitude role H*(k.divisors.card : ℝ)*(H : ℝ)/z :=
  bounded_rough_auxiliary_removal S (actual z y role) H k q b z
    (roleAmplitude role H) hS hz hk hq (roleAmplitude_nonneg role H)
    (fun n hn => actual_norm_le_roleAmplitude z y role
      (Finset.mem_Ioc.mp (hS hn)).1 (Finset.mem_Ioc.mp (hS hn)).2)
    (fun n hn hne => actual_rough_support z y role n hne)

/-- The actual unit-norm Mellin phase does not increase the auxiliary
removal error.  The frequency is unrestricted in this finite statement. -/
theorem actual_mellin_auxiliary_removal (z y t U : ℝ) (role : Role)
    (S : Finset ℕ) (H k q b : ℕ) (hS : S ⊆ Finset.Ioc 0 H)
    (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (fun n => phase t ((n : ℝ)/U)*actual z y role n) k q b -
      auxiliarySWError S (fun n => phase t ((n : ℝ)/U)*actual z y role n) 1 q b‖ ≤
      2*roleAmplitude role H*(k.divisors.card : ℝ)*(H : ℝ)/z := by
  apply bounded_rough_auxiliary_removal S _ H k q b z (roleAmplitude role H)
    hS hz hk hq (roleAmplitude_nonneg role H)
  · intro n hn
    simpa only [norm_mul,phase_norm,one_mul] using
      actual_norm_le_roleAmplitude z y role
        (Finset.mem_Ioc.mp (hS hn)).1 (Finset.mem_Ioc.mp (hS hn)).2
  · intro n hn hne
    apply actual_rough_support z y role n
    intro ha0
    exact hne (by simp only [ha0,mul_zero])

/-- This feeds the same finite maximum that K's group-log Abel proof uses.
The k=1 prefix maximum remains an explicit arithmetic quantity, not an SW
assumption.  All prefixes and all auxiliary k are covered simultaneously. -/
theorem actual_auxiliaryPrefixNorm_le (z y : ℝ) (role : Role) (u v : ℝ)
    (k q b : ℕ) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    auxiliaryPrefixNorm (actual z y role) u v k q b ≤
      prefixNorm (actual z y role) u v q b +
        2*roleAmplitude role (Nat.floor v)*(k.divisors.card : ℝ)*(Nat.floor v : ℝ)/z := by
  apply Finset.sup'_le
  intro h hh
  have hh' : h ≤ Nat.floor v := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
  have hS : Finset.Ioc (Nat.floor u) h ⊆ Finset.Ioc 0 (Nat.floor v) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hh'⟩
  rw [prefix_mask_eq_auxiliary]
  have hrem := actual_auxiliary_removal z y role _ (Nat.floor v) k q b hS hz hk hq
  have hpre : ‖auxiliarySWError (Finset.Ioc (Nat.floor u) h)
      (actual z y role) 1 q b‖ ≤ prefixNorm (actual z y role) u v q b := by
    rw [error_eq_kernel]
    exact Finset.le_sup' _ hh
  calc
    _ = ‖auxiliarySWError (Finset.Ioc (Nat.floor u) h) (actual z y role) 1 q b +
        (auxiliarySWError (Finset.Ioc (Nat.floor u) h) (actual z y role) k q b -
          auxiliarySWError (Finset.Ioc (Nat.floor u) h) (actual z y role) 1 q b)‖ := by
      congr 1
      ring
    _ ≤ ‖auxiliarySWError (Finset.Ioc (Nat.floor u) h) (actual z y role) 1 q b‖ +
        ‖auxiliarySWError (Finset.Ioc (Nat.floor u) h) (actual z y role) k q b -
          auxiliarySWError (Finset.Ioc (Nat.floor u) h) (actual z y role) 1 q b‖ := by
      exact norm_add_le _ _
    _ ≤ _ := add_le_add hpre hrem

/-- Native (u,v] prefixes of truncated mu are literally prefixes of the
same untruncated rough mu, stopped at the original REAL endpoint y. -/
theorem truncated_mobius_prefix_eq {z y : ℝ} (hy : 0 ≤ y)
    (u : ℝ) (h k q b : ℕ) :
    prefix (coprimeMask (actual z y .mobius) k) u q b h =
      prefix (coprimeMask (roughMoebiusSlot z) k) u q b (min h (Nat.floor y)) := by
  have hset : (Finset.Ioc (Nat.floor u) h).filter (fun n => (n : ℝ) ≤ y) =
      Finset.Ioc (Nat.floor u) (min h (Nat.floor y)) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Ioc,Nat.le_floor_iff hy,le_min_iff]
    tauto
  simp only [prefix]
  rw [← hset,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : n.Coprime k <;> by_cases hc : (n : ℝ) ≤ y <;>
    simp [coprimeMask,actual,roughMuTrunc,hk,hc]

theorem truncated_mobius_auxiliaryPrefixNorm_le (z y u v : ℝ) (k q b : ℕ) :
    auxiliaryPrefixNorm (actual z y .mobius) u v k q b ≤
      auxiliaryPrefixNorm (roughMoebiusSlot z) u v k q b := by
  apply Finset.sup'_le
  intro h hh
  by_cases hy : 0 ≤ y
  · rw [truncated_mobius_prefix_eq hy]
    apply Finset.le_sup'
    exact Finset.mem_range.mpr (lt_of_le_of_lt (min_le_left _ _) (Finset.mem_range.mp hh))
  · have hz : ∀ n : ℕ, actual z y .mobius n = 0 := by
      intro n
      have hc : ¬(n : ℝ) ≤ y := fun h => hy ((Nat.cast_nonneg n).trans h)
      simp [actual,roughMuTrunc,hc]
    simp only [prefix,coprimeMask,hz,ite_self,zero_mul,Finset.sum_const_zero,norm_zero]
    exact auxiliaryPrefixNorm_nonneg _ _ _ _ _ _

/-- Native unit atoms stay separate.  Their exact discrepancy is independent
of the auxiliary k, while their original Mobius real cutoff is still present. -/
theorem actual_unit_auxiliary_error (z y : ℝ) (role : Role) (k q b : ℕ) :
    auxiliarySWError {1} (actual z y role) k q b =
      actual z y role 1*exactKernel q b 1 := by
  rw [auxiliary_eq_mask,error_eq_kernel]
  simp [coprimeMask]

theorem actual_log_unit_auxiliary_error (z y : ℝ) (k q b : ℕ) :
    auxiliarySWError {1} (actual z y .logarithm) k q b = 0 := by
  rw [actual_unit_auxiliary_error,actual_log_role_unit,zero_mul]

end
end ImbalancedChen.P5Z.ActualHBAuxiliaryPrefixes
