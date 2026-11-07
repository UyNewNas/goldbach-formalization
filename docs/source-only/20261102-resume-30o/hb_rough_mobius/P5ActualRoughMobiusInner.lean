import ImbalancedChen.P5ActualRoughMobiusRankin
import ImbalancedChen.P5OriginalBetaPrimeSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact finite inner convolution at the original real endpoints.  The
mean remains the coefficient's coprime mass divided by phi(q).  Primitive
residues are constructed by the existing CRT supplier.  All supported
prime powers occur, including powers above the squarefree Brun divisor.
-/
namespace ImbalancedChen.P5Z.ActualRoughMobiusInner
noncomputable section
open Classical Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
open ImbalancedChen.Part3
open ActualRoughMobiusConvolution ActualRoughMobiusRankin OriginalBetaPrimeSource

def muCoefficient (n : ℕ) : ℂ := ((μ n : ℤ) : ℂ)

def interval (a b : ℝ) : Finset ℕ := Ioc (Nat.floor a) (Nat.floor b)

def unroughError (a b : ℝ) (q r : ℕ) : ℂ :=
  auxiliarySWError (interval a b) muCoefficient 1 q r

def coprimeMobiusError (E : ℕ) (a b : ℝ) (q r : ℕ) : ℂ :=
  auxiliarySWError (interval a b) (fun n => ((coprimeMu E n : ℤ) : ℂ)) 1 q r

def divisibleMobiusAtom (ell : ℕ) (a b : ℝ) (q r : ℕ) : ℂ :=
  ∑ n ∈ interval a b, if ell ∣ n then muCoefficient n*exactKernel q r n else 0

theorem muCoefficient_norm_le (n : ℕ) : ‖muCoefficient n‖ ≤ 1 := by
  rw [muCoefficient,Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

theorem mem_interval_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    n ∈ interval a b ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  simp only [interval,Finset.mem_Ioc,Nat.floor_lt ha,Nat.le_floor_iff hb]

/-- Divisibility and the real endpoints are transported together.  No
floor is moved across a strict endpoint by an approximation. -/
theorem sum_dvd_interval (f : ℕ → ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {w : ℕ} (hw : 0 < w) :
    (∑ n ∈ interval a b, if w ∣ n then f n else 0) =
      ∑ m ∈ interval (a/(w : ℝ)) (b/(w : ℝ)), f (w*m) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun n _ => n/w)
  · intro n hn
    obtain ⟨hnI,hwd⟩ := Finset.mem_filter.mp hn
    obtain ⟨han,hnb⟩ := (mem_interval_iff ha hb n).mp hnI
    have heq : (n : ℝ) = (w : ℝ)*((n/w : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hwd).symm
    apply (mem_interval_iff (div_nonneg ha hwR.le) (div_nonneg hb hwR.le) _).mpr
    constructor
    · apply (div_lt_iff₀ hwR).mpr
      nlinarith [heq]
    · apply (le_div_iff₀ hwR).mpr
      nlinarith [heq]
  · intro n hn m hm hnm
    have hn' := Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
    have hm' := Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2
    rw [hnm] at hn'
    exact hn'.symm.trans hm'
  · intro m hm
    obtain ⟨ham,hmb⟩ := (mem_interval_iff
      (div_nonneg ha hwR.le) (div_nonneg hb hwR.le) m).mp hm
    refine ⟨w*m,Finset.mem_filter.mpr ⟨?_,dvd_mul_right _ _⟩,
      Nat.mul_div_cancel_left m hw⟩
    apply (mem_interval_iff ha hb _).mpr
    rw [Nat.cast_mul]
    exact ⟨by have := (div_lt_iff₀ hwR).mp ham; nlinarith,
      by have := (le_div_iff₀ hwR).mp hmb; nlinarith⟩
  · intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

theorem supportedDivisors_eq {E H n : ℕ} (hn : 0 < n) (hnH : n ≤ H) :
    n.divisors.filter (PrimeSupported E) =
      (supportedCarrier E H).filter (fun w => w ∣ n) := by
  ext w
  simp only [Finset.mem_filter,supportedCarrier,Finset.mem_Icc,Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hwd,hn0⟩,hws⟩
    exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hwd hn,(Nat.le_of_dvd hn hwd).trans hnH⟩,hws⟩,hwd⟩
  · rintro ⟨⟨hw,hws⟩,hwd⟩
    exact ⟨⟨hwd,hn.ne'⟩,hws⟩

theorem coprimeMu_eq_finite_supported {E H n : ℕ} (hn : 0 < n) (hnH : n ≤ H) :
    ((coprimeMu E n : ℤ) : ℂ) =
      ∑ w ∈ supportedCarrier E H, if w ∣ n then muCoefficient (n/w) else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ))
    (coprime_moebius_eq_supported_divisor_sum E hn)
  simp only [Int.cast_sum] at h
  change ((coprimeMu E n : ℤ) : ℂ) = _ at h
  rw [supportedDivisors_eq hn hnH,Finset.sum_filter] at h
  exact h

/-- Exact finite convolution with both the primitive residue and the
SAME 1/phi(q) coprime mean.  E and every supported w are coprime to q. -/
theorem coprimeMobiusError_eq_supported (E : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {q r : ℕ}
    (hEq : E.Coprime q) (hr : r.Coprime q) :
    coprimeMobiusError E a b q r =
      ∑ w ∈ supportedCarrier E (Nat.floor b),
        unroughError (a/(w : ℝ)) (b/(w : ℝ)) q (pulledResidue w q r) := by
  rw [coprimeMobiusError,error_eq_kernel]
  have hpoint (n : ℕ) (hn : n ∈ interval a b) :
      ((coprimeMu E n : ℤ) : ℂ)*exactKernel q r n =
        ∑ w ∈ supportedCarrier E (Nat.floor b),
          if w ∣ n then muCoefficient (n/w)*exactKernel q r n else 0 := by
    have hn0 : 0 < n := (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hn).1
    rw [coprimeMu_eq_finite_supported hn0 (Finset.mem_Ioc.mp hn).2,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hpoint,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have hw1 : 0 < w := (Finset.mem_Icc.mp (Finset.mem_filter.mp hw).1).1
  have hwq : w.Coprime q := primeSupported_coprime hEq (Finset.mem_filter.mp hw).2
  rw [sum_dvd_interval _ ha hb hw1,unroughError,error_eq_kernel]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.mul_div_cancel_left m hw1,exactKernel_product hr,if_pos hwq]

theorem divisibleMobiusAtom_eq (ell : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hell : 0 < ell) {q r : ℕ}
    (hr : r.Coprime q) :
    divisibleMobiusAtom ell a b q r =
      if ell.Coprime q then
        muCoefficient ell * coprimeMobiusError ell (a/(ell : ℝ)) (b/(ell : ℝ))
          q (pulledResidue ell q r)
      else 0 := by
  rw [divisibleMobiusAtom,sum_dvd_interval _ ha hb hell]
  by_cases heq : ell.Coprime q
  · rw [if_pos heq,coprimeMobiusError,error_eq_kernel,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [exactKernel_product hr,if_pos heq]
    have hmu : muCoefficient (ell*m) = muCoefficient ell*((coprimeMu ell m : ℤ) : ℂ) := by
      rw [muCoefficient,moebius_mul_exact]
      by_cases hc : ell.Coprime m
      · simp [hc,muCoefficient,coprimeMu,Nat.coprime_comm]
      · simp [hc,muCoefficient,coprimeMu,Nat.coprime_comm]
    rw [hmu,mul_assoc]
  · rw [if_neg heq]
    apply Finset.sum_eq_zero
    intro m hm
    rw [exactKernel_product hr,if_neg heq,mul_zero]

/-- Primitive AP support permits a one-bounded centered kernel.  This
avoids a spurious extra factor two in the large-w Rankin remainder. -/
theorem primitive_kernel_norm_le {q r : ℕ} (hq : 0 < q) (hr : r.Coprime q)
    (n : ℕ) : ‖exactKernel q r n‖ ≤ 1 := by
  have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hphi0 : (0 : ℝ) < q.totient := zero_lt_one.trans_le hphi
  have hi : 0 ≤ 1/(q.totient : ℝ) := by positivity
  have hi1 : 1/(q.totient : ℝ) ≤ 1 := (div_le_one hphi0).mpr hphi
  by_cases ha : Nat.ModEq q n r
  · have hc : n.Coprime q := by
      change Nat.gcd n q = 1
      rw [ha.gcd_eq]
      exact hr
    have heq : exactKernel q r n = ((1-1/(q.totient : ℝ) : ℝ) : ℂ) := by
      simp [exactKernel,ha,hc]
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hi1)]
    linarith
  · by_cases hc : n.Coprime q
    · have heq : exactKernel q r n = ((-1/(q.totient : ℝ) : ℝ) : ℂ) := by
        simp [exactKernel,ha,hc]
      rw [heq,Complex.norm_real,Real.norm_eq_abs,neg_div,abs_neg,
        abs_of_nonneg hi]
      exact hi1
    · simp [exactKernel,ha,hc]

theorem unroughError_norm_le_endpoint {a b : ℝ} (hb : 0 ≤ b)
    {q r : ℕ} (hq : 0 < q) (hr : r.Coprime q) :
    ‖unroughError a b q r‖ ≤ b := by
  rw [unroughError,error_eq_kernel]
  calc
    _ ≤ ∑ n ∈ interval a b, ‖muCoefficient n*exactKernel q r n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ interval a b, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul (muCoefficient_norm_le n) (primitive_kernel_norm_le hq hr n)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ = ((interval a b).card : ℝ) := by simp
    _ ≤ (Nat.floor b : ℝ) := by
      have hh : (interval a b).card ≤ Nat.floor b := by
        simp only [interval,Nat.card_Ioc]
        exact Nat.sub_le _ _
      exact_mod_cast hh
    _ ≤ b := Nat.floor_le hb

def smallSupported (E : ℕ) (b V : ℝ) : Finset ℕ :=
  (supportedCarrier E (Nat.floor b)).filter (fun w => (w : ℝ) ≤ V^(1/4 : ℝ))

def largeSupported (E : ℕ) (b V : ℝ) : Finset ℕ :=
  (supportedCarrier E (Nat.floor b)).filter (fun w => V^(1/4 : ℝ) < (w : ℝ))

def smallError (E : ℕ) (a b V : ℝ) (q r : ℕ) : ℂ :=
  ∑ w ∈ smallSupported E b V,
    unroughError (a/(w : ℝ)) (b/(w : ℝ)) q (pulledResidue w q r)

def largeError (E : ℕ) (a b V : ℝ) (q r : ℕ) : ℂ :=
  ∑ w ∈ largeSupported E b V,
    unroughError (a/(w : ℝ)) (b/(w : ℝ)) q (pulledResidue w q r)

theorem coprimeMobiusError_eq_small_add_large (E : ℕ) {a b V : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {q r : ℕ}
    (hEq : E.Coprime q) (hr : r.Coprime q) :
    coprimeMobiusError E a b q r = smallError E a b V q r + largeError E a b V q r := by
  rw [coprimeMobiusError_eq_supported E ha hb hEq hr]
  unfold smallError largeError smallSupported largeSupported
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : (w : ℝ) ≤ V^(1/4 : ℝ)
  · simp [h,not_lt.mpr h]
  · simp [h,lt_of_not_ge h]

/-- Actual large-w convolution error, with the original real upper
endpoint and its exact coprime mean.  No cancellation is used here. -/
theorem largeError_norm_le (E : ℕ) (hE : E ≠ 0) {a b V : ℝ}
    (hV : 0 < V) (hb : 0 ≤ b) (hbV : b ≤ 2*V)
    {q r : ℕ} (hq : 0 < q) (hEq : E.Coprime q) (hr : r.Coprime q) :
    ‖largeError E a b V q r‖ ≤ 2*V^(7/8 : ℝ)*(E.divisors.card : ℝ)^2 := by
  unfold largeError
  calc
    _ ≤ ∑ w ∈ largeSupported E b V,
        ‖unroughError (a/(w : ℝ)) (b/(w : ℝ)) q (pulledResidue w q r)‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ largeSupported E b V, 2*V/(w : ℝ) := by
      apply Finset.sum_le_sum
      intro w hw
      have hws := (Finset.mem_filter.mp hw).1
      have hw0 : (0 : ℝ) < w := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hws).1).1
      have hwq := primeSupported_coprime hEq (Finset.mem_filter.mp hws).2
      exact (unroughError_norm_le_endpoint (div_nonneg hb hw0.le) hq
        (pulledResidue_coprime hwq hr)).trans (div_le_div_of_nonneg_right hbV hw0.le)
    _ ≤ _ := supported_large_tail_le E (Nat.floor b) hE hV

end
end ImbalancedChen.P5Z.ActualRoughMobiusInner
