import ImbalancedChen.Part3OriginalInverseShortMean

/-! All-modulus estimate for the physical U₂ in Drappeau's proof of (4.30),
and its consequence for the opened Kloosterman sums at arbitrary prefixes. -/
namespace ImbalancedChen.Part3.OriginalInverseShortMeanInitial20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalSmoothPoissonTail OriginalInverseShortSums20261113 OriginalInverseShortMean20261113
open IntervalHarmonicPairBoundSourceOnly ActualIntervalGeometricSumSourceOnly

private theorem harmonic_nonnegative (n : ℕ) : 0≤(harmonic n:ℝ) := by
  rw [←real_reciprocal_sum_eq_harmonic]
  positivity

private theorem initial_cost (X : ℕ) (U V : ℝ) (u : 0≤U) (v : 0≤V)
    (F : ℕ+ → ℝ) (dyad : ∀ L : Finset ℕ+, ∀ K : ℝ, 1≤K →
      (∀ k ∈ L, K≤(k.val:ℝ) ∧ (k.val:ℝ)≤2*K) →
      (∑ k ∈ L, F k) ≤ 6000*(1+Real.log (1+12*K))*(K*U+K^2*V)) :
    ∀ L : Finset ℕ+, (∀ k ∈ L, k.val≤X) → (∑ k ∈ L, F k) ≤
      12000*(1+Real.log (1+12*(X:ℝ)))*((X:ℝ)*U+(X:ℝ)^2*V) := by
  classical
  induction X using Nat.strong_induction_on with
  | h X ih =>
    intro L cap
    by_cases zero : X=0
    · have e : L=∅ := eq_empty_iff_forall_notMem.mpr (by
        intro k hk
        have h := cap k hk
        have t := k.property
        omega)
      simp [e,zero]
    by_cases one : X=1
    · have d := dyad L 1 le_rfl (by
        intro k hk
        have t := cap k hk
        have two : k.val≤2 := by omega
        exact ⟨by exact_mod_cast k.property,by simpa only [mul_one] using (show (k.val:ℝ)≤2 by exact_mod_cast two)⟩)
      rw [one,Nat.cast_one]
      have log0 := Real.log_nonneg (by norm_num : (1:ℝ)≤1+12*1)
      nlinarith only [d,u,v,mul_nonneg log0 u,mul_nonneg log0 v]
    let K := (X:ℝ)/2
    have hK : 1≤K := by
      have hX : (2:ℝ)≤X := by exact_mod_cast (by omega : 2≤X)
      dsimp [K]
      linarith
    let P (k : ℕ+) := k.val≤X/2
    let low := L.filter P
    let high := L.filter (fun k => ¬P k)
    have d := dyad high K hK (by
      intro k hk
      have upper := cap _ (mem_filter.mp hk).1
      have lower : ¬k.val≤X/2 := (mem_filter.mp hk).2
      have two : X≤2*k.val := by omega
      dsimp [K]
      constructor
      · have : (X:ℝ)≤2*(k.val:ℝ) := by exact_mod_cast two
        linarith
      · convert (show (k.val:ℝ)≤X by exact_mod_cast upper) using 1 <;> ring)
    have l := ih (X/2) (by omega) low (fun _ hk => (mem_filter.mp hk).2)
    let D := fun t : ℝ => 1+Real.log (1+12*t)
    let Z := fun t : ℝ => t*U+t^2*V
    have step {s t : ℝ} (hs : 0≤s) (hst : s≤t) : D s*Z s ≤ D t*Z t := by
      have logs := Real.log_le_log (by positivity : 0<1+12*s) (by linarith : 1+12*s≤1+12*t)
      have t0 : 0≤t := hs.trans hst
      have lt0 := Real.log_nonneg (by linarith only [t0] : 1≤1+12*t)
      exact mul_le_mul (by dsimp [D]; linarith) (add_le_add
        (mul_le_mul_of_nonneg_right hst u) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hst 2) v))
        (by dsimp [Z]; positivity) (by dsimp [D]; positivity)
    have x2 : (↑(X/2):ℝ)≤K := by
      have t : 2*(X/2)≤X := by omega
      have : 2*(↑(X/2):ℝ)≤X := by exact_mod_cast t
      dsimp [K]
      linarith
    have e := sum_filter_add_sum_filter_not L P F
    change (∑ k ∈ low,F k)+(∑ k ∈ high,F k)=(∑ k ∈ L,F k) at e
    have c0 := step (Nat.cast_nonneg (X/2)) x2
    have logmono : D K ≤ D X := by
      dsimp [D,K]
      exact add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith [Nat.cast_nonneg X (α := ℝ)]))
    have z0 : 0≤Z K := by dsimp [Z,K]; positivity
    have dx : 0≤D X := by
      have h := Real.log_nonneg (by linarith [Nat.cast_nonneg X (α := ℝ)] : 1≤1+12*(X:ℝ))
      dsimp [D]
      positivity
    have zcap : 2*Z K ≤ Z X := by
      dsimp [Z,K]
      nlinarith only [mul_nonneg (sq_nonneg (X:ℝ)) v]
    change (∑ k ∈ high,F k) ≤ 6000*D K*Z K at d
    change (∑ k ∈ low,F k) ≤ 12000*D (↑(X/2):ℝ)*Z (↑(X/2):ℝ) at l
    have dk : 0≤D K := by
      have h := Real.log_nonneg (by linarith only [hK] : 1≤1+12*K)
      dsimp [D]
      positivity
    change (∑ k ∈ L,F k) ≤ 12000*D X*Z X
    nlinarith only [e,d,l,c0,mul_le_mul_of_nonneg_right logmono z0,
      mul_le_mul_of_nonneg_left zcap dx,mul_nonneg dk z0]

/-- All original positive moduli up to X (or any subset), with arbitrary
fixed-for-the-sum endpoints and either sign of the common phase. -/
theorem total_mean (L : Finset ℕ+) (X M N : ℕ) (cap : ∀ k ∈ L, k.val≤X)
    (a b c d : ℕ) (hab : a≤b) (hcd : c≤d) (hm : b-a≤M) (hn : d-c≤N) (ω : ℝ) :
    (∑ k ∈ L, inverseShortMean k (Ico a b) (Ico c d) ω) ≤
      12000*(1+Real.log (1+12*(X:ℝ)))*((X:ℝ)*((M:ℝ)*N)+(X:ℝ)^2*((harmonic M:ℝ)*(harmonic N:ℝ))) := by
  refine initial_cost X _ _ (by positivity) (mul_nonneg (harmonic_nonnegative M) (harmonic_nonnegative N))
    _ ?_ L cap
  intro S K hK level
  simpa only [mul_assoc] using dyadic_mean S hK level M N (fun _ => a) (fun _ => b)
    (fun _ => c) (fun _ => d) (fun _ _ => ⟨hab,hm⟩) (fun _ _ => ⟨hcd,hn⟩) ω

private theorem log_cost {ε t : ℝ} (he : 0<ε) (ht : 1≤t) :
    1+Real.log t ≤ (1+1/ε)*t^ε := by
  have h := Real.log_le_rpow_div (zero_le_one.trans ht) he
  have p := Real.one_le_rpow ht he.le
  rw [div_eq_mul_inv] at h
  rw [one_div,add_mul,one_mul]
  nlinarith only [h,p]

/-- Original (4.30) arithmetic strength K(K+MN)(KMN)^ε, with the
constant chosen *before* every positive scale, both endpoints and ω. -/
theorem initial_mean {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (L : Finset ℕ+) (X M N : ℕ), 1≤X → 1≤M → 1≤N →
      (∀ k ∈ L, k.val≤X) → ∀ (a b c d : ℕ), a≤b → c≤d → b-a≤M → d-c≤N → ∀ ω : ℝ,
      (∑ k ∈ L, inverseShortMean k (Ico a b) (Ico c d) ω) ≤
        C*((X:ℝ)*M*N)^ε*(X:ℝ)*((X:ℝ)+(M:ℝ)*N) := by
  let A := 1+1/ε
  refine ⟨12000*13^ε*A^3,by dsimp [A]; positivity,?_⟩
  intro L X M N hX hM hN cap a b c d hab hcd hm hn ω
  have x : (1:ℝ)≤X := by exact_mod_cast hX
  have m : (1:ℝ)≤M := by exact_mod_cast hM
  have n : (1:ℝ)≤N := by exact_mod_cast hN
  have ap : 1≤A := by dsimp [A]; linarith [one_div_pos.mpr he]
  have Bm := (harmonic_le_one_add_log M).trans (log_cost he m)
  have Bn := (harmonic_le_one_add_log N).trans (log_cost he n)
  change (harmonic M:ℝ)≤ A*(M:ℝ)^ε at Bm
  change (harmonic N:ℝ)≤ A*(N:ℝ)^ε at Bn
  have P := mul_le_mul Bm Bn (harmonic_nonnegative N) (by positivity)
  have oneM := Real.one_le_rpow m he.le
  have oneN := Real.one_le_rpow n he.le
  let V := (A*(M:ℝ)^ε)*(A*(N:ℝ)^ε)
  have v : 1≤V := by
    have mu : 1≤A*(M:ℝ)^ε := by simpa only [one_mul] using mul_le_mul ap oneM zero_le_one (zero_le_one.trans ap)
    have nu : 1≤A*(N:ℝ)^ε := by simpa only [one_mul] using mul_le_mul ap oneN zero_le_one (zero_le_one.trans ap)
    simpa only [one_mul] using mul_le_mul mu nu zero_le_one (zero_le_one.trans mu)
  have vcap : (X:ℝ)*((M:ℝ)*N)+(X:ℝ)^2*((harmonic M:ℝ)*(harmonic N:ℝ)) ≤
      ((X:ℝ)*((M:ℝ)*N)+(X:ℝ)^2)*V := by
    have t := mul_le_mul_of_nonneg_left v (by positivity : 0 ≤ (X:ℝ)*((M:ℝ)*N))
    change (harmonic M:ℝ)*(harmonic N:ℝ) ≤ V at P
    nlinarith only [t,mul_le_mul_of_nonneg_left P (sq_nonneg (X:ℝ))]
  have bound := log_cost he (by linarith only [x] : (1:ℝ)≤1+12*X)
  have xcap := Real.rpow_le_rpow (by positivity : (0:ℝ)≤1+12*X)
    (by linarith only [x] : (1:ℝ)+12*X≤13*X) he.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤13) (Nat.cast_nonneg X)] at xcap
  have cost : 1+Real.log (1+12*(X:ℝ)) ≤ A*(13^ε*(X:ℝ)^ε) :=
    bound.trans (mul_le_mul_of_nonneg_left xcap (zero_le_one.trans ap))
  apply (total_mean L X M N cap a b c d hab hcd hm hn ω).trans
  calc
    _ ≤ (12000*(A*(13^ε*(X:ℝ)^ε)))*(((X:ℝ)*((M:ℝ)*N)+(X:ℝ)^2)*V) :=
      mul_le_mul (mul_le_mul_of_nonneg_left cost (by norm_num)) vcap
        (add_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (mul_nonneg
          (harmonic_nonnegative M) (harmonic_nonnegative N)))) (by positivity)
    _ = _ := by
      dsimp [V]
      rw [Real.mul_rpow (by positivity : (0:ℝ)≤(X:ℝ)*M) (Nat.cast_nonneg N),
        Real.mul_rpow (Nat.cast_nonneg X) (Nat.cast_nonneg M)]
      ring

/-- Uniform estimate at the actual two arbitrary prefixes appearing after
both partial summations, before reinserting the Mellin factors. -/
theorem initial_opened_mean {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (L : Finset ℕ+) (X M N : ℕ), 1≤X → 1≤M → 1≤N →
      (∀ k ∈ L, k.val≤X) → ∀ (a b c d : ℕ), a≤b → c≤d → b-a≤M → d-c≤N → ∀ ω : ℝ,
      (∑ k ∈ L, ‖∑ m ∈ Ico a b, ∑ n ∈ Ico c d,
        phaseAt ω m*phaseAt (-ω) n*kloosterman k.val (m:ℤ) (n:ℤ)‖) ≤
        C*((X:ℝ)*M*N)^ε*(X:ℝ)*((X:ℝ)+(M:ℝ)*N) := by
  obtain ⟨C,hC,H⟩ := initial_mean he
  refine ⟨C,hC,?_⟩
  intro L X M N hX hM hN cap a b c d hab hcd hm hn ω
  exact (sum_le_sum (fun k (_ : k ∈ L) => inverse_short_bound k (Ico a b) (Ico c d) ω)).trans
    (H L X M N hX hM hN cap a b c d hab hcd hm hn ω)

end
end ImbalancedChen.Part3.OriginalInverseShortMeanInitial20261113
