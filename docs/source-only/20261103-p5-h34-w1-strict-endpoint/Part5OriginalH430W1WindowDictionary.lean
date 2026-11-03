import ImbalancedChen.Part5OriginalH430SelectedBankGeometry
import ImbalancedChen.P2OriginalLiteralW1OldProfile
import ImbalancedChen.Part5OriginalH430BuchstabCeilingPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original W1 d*N-masked HALF-OPEN childWindow is the production strict
singleChildren plus its lower-endpoint fibre. There is no repeat payment
here: the original W1 mask has already removed old-prefix divisors.
The target/ceiling condition removes no additional primes. Natural primes
are reindexed into Fin(N+1) only after deriving the cap from Q <= N.
-/
namespace ImbalancedChen.Part5OriginalH430W1WindowDictionary

noncomputable section
open Set Classical
open scoped BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PrimeChildAdmission
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalHalfOpenProfileCarrier P2OriginalBankThetaMassLimits
open P2OriginalLiteralW1OldProfile

abbrev halfWindow (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) :=
  P2EnhancedActualBuchstabTransfer.childWindow N (parentProduct old) Q
    (W1Target i) (W1Anchor j)

def strictWindow (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) : Finset ℕ :=
  (halfWindow N Q old i j).filter (fun q => 1/W1Anchor j < relativePrime Q old q)

def endpointWindow (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) : Finset ℕ :=
  (halfWindow N Q old i j).filter (fun q => relativePrime Q old q = 1/W1Anchor j)

theorem target_ge_two (i : Fin 7) : (2:ℝ) ≤ W1Target i := by
  have hi : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
  dsimp [W1Target]
  linarith

theorem target_recip_le_half (i : Fin 7) : 1/W1Target i ≤ (1/2:ℝ) :=
  one_div_le_one_div_of_le (by norm_num) (target_ge_two i)

theorem parent_power {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) :
    Q = (parentProduct old:ℝ)*(N:ℝ)^(physicalLevel N Q old) :=
  sameQ_eq_residualExponent hw.1 hw.2.1 (zero_lt_one.trans (parentWindow_logs hw).2.1)

theorem relative_eq_normalized {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) :
    relativePrime Q old q =
      normalizedLog N (physicalLevel N Q old) (fun _ : Fin 1 => q) 0 := by
  have h := physical_log_ratio hw.1 hw.2.1 (parentWindow_logs hw).2.2
    (fun _ : Fin 1 => q) 0
  rw [← parent_power hw] at h
  exact h

/-- The d*N deletion and both endpoint conventions remain literal. -/
theorem mem_halfWindow {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10) :
    q ∈ halfWindow N Q old i j ↔
      q.Prime ∧ q.Coprime (N*parentProduct old) ∧
        1/W1Anchor j ≤ relativePrime Q old q ∧
        relativePrime Q old q < 1/W1Target i := by
  let L := physicalLevel N Q old
  have hL : 0 < L := (parentWindow_logs hw).2.2
  have hcut (s : ℝ) : P2EnhancedTwentyOneSameQWeighted.cutoff Q (parentProduct old) s =
      (N:ℝ)^(L*(1/s)) := by
    rw [cutoff_eq_physical_power hw.2.1 (parent_power hw)]
    congr 1
    ring
  have hn := relative_eq_normalized (q := q) hw
  rw [halfWindow, P2EnhancedActualBuchstabTransfer.childWindow, hcut, hcut,
    Wu2008DoubleSieve.mem_primeWindow]
  constructor
  · rintro ⟨hp,hcop,hlo,hhi⟩
    have hx := (normalizedLog_window hw.1 hL (fun _ : Fin 1 => q)
      (fun _ => hp.pos) 0 (1/W1Anchor j) (1/W1Target i)).mpr ⟨hlo,hhi⟩
    rw [← hn] at hx
    exact ⟨hp,by simpa only [Nat.mul_comm] using hcop,hx⟩
  · rintro ⟨hp,hcop,hlo,hhi⟩
    have hx := (normalizedLog_window hw.1 hL (fun _ : Fin 1 => q)
      (fun _ => hp.pos) 0 (1/W1Anchor j) (1/W1Target i)).mp
      (by simpa only [← hn] using And.intro hlo hhi)
    exact ⟨hp,by simpa only [Nat.mul_comm] using hcop,hx⟩

theorem window_product_lt {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hw : parentWindow N Q old chi)
    (hq : q ∈ halfWindow N Q old i j) : ((parentProduct old*q:ℕ):ℝ) < Q := by
  have h := (mem_halfWindow hw i j).mp hq
  have hR := (parentWindow_logs hw).2.1
  have hqR : (q:ℝ) < residualLevel Q old := by
    apply (Real.log_lt_log_iff (Nat.cast_pos.mpr h.1.pos) (zero_lt_one.trans hR)).mp
    exact (div_lt_one (Real.log_pos hR)).mp
      (h.2.2.2.trans ((target_recip_le_half i).trans_lt (by norm_num)))
  have hdR : (0:ℝ) < parentProduct old := Nat.cast_pos.mpr hw.2.1
  have he : (parentProduct old:ℝ)*residualLevel Q old = Q := by
    unfold residualLevel
    field_simp [hdR.ne'] <;> ring
  have hm := mul_lt_mul_of_pos_left hqR hdR
  rw [he] at hm
  simpa only [Nat.cast_mul] using hm

theorem window_prime_cap {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hw : parentWindow N Q old chi)
    (hq : q ∈ halfWindow N Q old i j) : q ≤ N := by
  have hprod : parentProduct old*q ≤ N := by
    exact_mod_cast (window_product_lt hw hq).le.trans hw.2.2.2.1
  have hsmall : q ≤ parentProduct old*q := by
    simpa only [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ parentProduct old by omega)
  exact hsmall.trans hprod

/-- The physical ceiling is automatic once the original target is admitted. -/
theorem mem_strictWindow_iff_child {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10)
    (hceil : physicalLevel N Q old/W1Target i ≤ chi) (q : Fin (N+1)) :
    q.val ∈ strictWindow N Q old i j ↔ q ∈ singleChildren (.w1 i j) N Q old chi := by
  rw [strictWindow, Finset.mem_filter, mem_halfWindow hw i j, mem_singleChildren]
  constructor
  · rintro ⟨⟨hp,hcop,hlo,hhi⟩,hstrict⟩
    have hL := (parentWindow_logs hw).2.2
    have hphys : physicalPrime N q.val < chi := by
      have hh := mul_lt_mul_of_pos_left hhi hL
      rw [relativePrime_physical hw] at hh
      exact hh.trans_le (by simpa only [mul_one_div] using hceil)
    have hwin : q.val ∈ halfWindow N Q old i j :=
      (mem_halfWindow hw i j).mpr ⟨hp,hcop,hlo,hhi⟩
    exact ⟨⟨hp,hcop⟩,hw,⟨hstrict,hhi⟩,hphys,window_product_lt hw hwin⟩
  · rintro ⟨⟨hp,hcop⟩,_,hdom,_,_⟩
    change 1/W1Anchor j < relativePrime Q old q.val ∧
      relativePrime Q old q.val < 1/W1Target i at hdom
    exact ⟨⟨hp,hcop,hdom.1.le,hdom.2⟩,hdom.1⟩

theorem strictWindow_sum {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10)
    (hceil : physicalLevel N Q old/W1Target i ≤ chi) (F : ℕ → ℝ) :
    (∑ q ∈ strictWindow N Q old i j, F q) =
      ∑ q ∈ singleChildren (.w1 i j) N Q old chi, F q.val := by
  symm
  apply Finset.sum_bij (fun q _ => q.val)
  · intro q hq
    exact (mem_strictWindow_iff_child hw i j hceil q).mpr hq
  · intro q _ r _ he
    exact Fin.ext he
  · intro q hq
    have hcap := window_prime_cap hw (Finset.mem_filter.mp hq).1
    let q' : Fin (N+1) := ⟨q,Nat.lt_succ_of_le hcap⟩
    exact ⟨q',(mem_strictWindow_iff_child hw i j hceil q').mp hq,rfl⟩
  · intro q _
    rfl

/-- Exact disjoint finite identity for every signed test. -/
theorem window_sum_split {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10)
    (hceil : physicalLevel N Q old/W1Target i ≤ chi) (F : ℕ → ℝ) :
    (∑ q ∈ halfWindow N Q old i j, F q) =
      (∑ q ∈ singleChildren (.w1 i j) N Q old chi, F q.val) +
      ∑ q ∈ endpointWindow N Q old i j, F q := by
  rw [← strictWindow_sum hw i j hceil]
  simp only [strictWindow,endpointWindow,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hlo := ((mem_halfWindow hw i j).mp hq).2.2.1
  by_cases he : relativePrime Q old q = 1/W1Anchor j
  · simp [he]
  · have hs : 1/W1Anchor j < relativePrime Q old q := lt_of_le_of_ne hlo (Ne.symm he)
    simp [he,hs]

theorem endpoint_card_le_one {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (i : Fin 7) (j : Fin 10) :
    (endpointWindow N Q old i j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq r hr
  obtain ⟨hq,hqe⟩ := Finset.mem_filter.mp hq
  obtain ⟨hr,hre⟩ := Finset.mem_filter.mp hr
  have hp := ((mem_halfWindow hw i j).mp hq).1
  have hp' := ((mem_halfWindow hw i j).mp hr).1
  have hlogR := (Real.log_pos (parentWindow_logs hw).2.1).ne'
  have he : Real.log (q:ℝ) = Real.log (r:ℝ) := by
    apply (div_left_inj' hlogR).mp
    exact hqe.trans hre.symm
  have hreal := Real.log_injOn_pos (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hp'.pos) he
  exact_mod_cast hreal

theorem window_primeFloor_le {N q : ℕ} {Q chi : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hw : parentWindow N Q old chi)
    (hq : q ∈ halfWindow N Q old i j) :
    Part5OriginalH430BuchstabCeilingDictionary.primeFloor N Q old ≤ (q:ℝ) := by
  have hlo := (Wu2008DoubleSieve.mem_primeWindow.mp hq).2.2.1
  rw [cutoff_eq_physical_power hw.2.1 (parent_power hw)] at hlo
  have hanchor := (P2OriginalBankOldProfilePassage.W1_endpoints i j).1
  have hL := (parentWindow_logs hw).2.2
  have hexp : physicalLevel N Q old/6 ≤ physicalLevel N Q old/W1Anchor j := by
    have hh := mul_le_mul_of_nonneg_left
      ((by norm_num : (1/6:ℝ) ≤ 1/5).trans hanchor) hL.le
    simpa only [mul_one_div] using hh
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hw.1.le) hexp).trans hlo

/-- This is the query used in W1ChildAtom, not a fresh independently chosen query. -/
def childQuery (Q : ℝ) (old : List ℕ) (j : Fin 10) (q : ℕ) : ℝ :=
  W1Anchor j*(1-relativePrime Q old q)

theorem childQuery_is_physical {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : PhysicalNode} (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (i : Fin 7) (j : Fin 10) (q : Fin (N+1)) :
    (perform p (.w1Singleton i j) (singleCoordinates N q.val)).argument =
      childQuery Q old j q.val := by
  change W1Anchor j*(1-normalized p (singleCoordinates N q.val) 0) = _
  rw [actual_normalized_single hw hL]
  rfl

end
end ImbalancedChen.Part5OriginalH430W1WindowDictionary
