import ImbalancedChen.P4AOriginalFull87StoppedCentreExceptionFibre
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Continue the exact N%4=0 exceptional centre fibre q0=(N-2)/2 of the
SAME receiverTest-generated, sharedRankFour fifth/sixth stopped ledger.

Unlike a physical-rho <=1 argument, we keep occurrence multiplicity.
For each fixed actual (fifth history, sixth p), the original PLUS-beta
sum has AT MOST ONE index a=q0/(p*history.prod). Further, p must
divide q0. Hence the original ordered sixth list can be filtered by
p|q0, with a genuine absolute cost charged PER surviving occurrence.
No independent bound on the total stopped coefficient is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedQ0QuotientDivisor
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87StoppedCentreExceptionFibre
  (exceptionalCentreFibre exceptionalFifthPlusFibre
   large_fifth_exceptional_fibre_eq_plus_sum
   common_sixth_exceptional_fibre_eq_original_weights)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthRosserIndices largeFifthPlusAttachment)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)

/-- A positive integer q can be factored as a*b with fixed b
for at most one natural a, namely q/b. This lemma keeps the
original Finset and coefficient; no Rosser weight is changed. -/
private theorem positive_mul_fibre_sum
    (S : Finset ℕ) (beta : ℕ → ℝ) (b q : ℕ) (hq : 0 < q) :
    (∑ a ∈ S, if a * b = q then beta a else 0) =
      if q / b ∈ S ∧ (q / b) * b = q then beta (q / b) else 0 := by
  classical
  by_cases hb : b = 0
  · simp [hb, Nat.ne_of_gt hq]
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hiff (a : ℕ) :
      (a * b = q) ↔ (a = q / b ∧ (q / b) * b = q) := by
    constructor
    · intro heq
      have hdiv : q / b = a := by
        rw [← heq]
        exact Nat.mul_div_cancel a hbpos
      exact ⟨hdiv.symm, by simpa [hdiv] using heq⟩
    · rintro ⟨rfl, heq⟩
      exact heq
  have hsum :
      (∑ a ∈ S, if a * b = q then beta a else 0) =
      (∑ a ∈ S, if a = q / b ∧ (q / b) * b = q then beta a else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hiff a]
  rw [hsum]
  by_cases hqmul : (q / b) * b = q
  · simp [hqmul, Finset.sum_ite_eq']
  · simp [hqmul]

/-- The strict original high-q condition may be evaluated ONCE at q.
The surviving Rosser index is the actual quotient, not an abstract
witness or a second physical coefficient. -/
private theorem positive_mul_fibre_with_strict_gate
    (S : Finset ℕ) (beta : ℕ → ℝ) (b q X : ℕ) (hq : 0 < q) :
    (∑ a ∈ S, if X < a * b ∧ a * b = q then beta a else 0) =
      if X < q ∧ q / b ∈ S ∧ (q / b) * b = q
      then beta (q / b) else 0 := by
  classical
  have hsum :
      (∑ a ∈ S, if X < a * b ∧ a * b = q then beta a else 0) =
      (∑ a ∈ S, if a * b = q then
          (if X < q then beta a else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases heq : a * b = q
    · simp [heq]
    · simp [heq]
  rw [hsum, positive_mul_fibre_sum S
    (fun a => if X < q then beta a else 0) b q hq]
  by_cases hX : X < q <;> simp [hX]

/-- The former full Rosser Finset sum is exactly a SINGLE quotient
coefficient per actual (fifth history, sixth p). The displayed
membership is the real fifth-power-filtered Rosser support.
The second equation checks exact divisibility, not only divisibility
up to floor rounding. -/
theorem exceptional_fifth_plus_fibre_single_quotient
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (hN : 8 ≤ N) :
    exceptionalFifthPlusFibre N cap w L X pre p =
      if X < (N - 2) / 2 ∧
          ((N - 2) / 2) / (p :: pre).prod ∈
            largeFifthRosserIndices N cap w X pre ∧
          (((N - 2) / 2) / (p :: pre).prod) *
            (p :: pre).prod = (N - 2) / 2
      then actualSmallRosserPlus N cap w L
        (((N - 2) / 2) / (p :: pre).prod)
      else 0 := by
  have hq : 0 < (N - 2) / 2 := by omega
  unfold exceptionalFifthPlusFibre
  exact positive_mul_fibre_with_strict_gate
    (largeFifthRosserIndices N cap w X pre)
    (actualSmallRosserPlus N cap w L) (p :: pre).prod
    ((N - 2) / 2) X hq

/-- One fixed (fifth history, sixth candidate p) cannot create more
than one nonzero Rosser a. The pointwise original PLUS-beta bound
therefore gives a genuine <=1 cost ONLY for this one occurrence.
The number of stopped occurrences is NOT dropped. -/
theorem exceptional_fifth_plus_fibre_abs_le_one
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (hN : 8 ≤ N) :
    |exceptionalFifthPlusFibre N cap w L X pre p| ≤ 1 := by
  rw [exceptional_fifth_plus_fibre_single_quotient
    N cap w L X pre p hN]
  split_ifs
  · exact actualSmallRosserPlus_abs_le_one N cap w L
      (((N - 2) / 2) / (p :: pre).prod)
  · simp

/-- A contributing post-fifth sixth prime MUST divide the exact q0
modulus. Uses the original complete a*(p::pre).prod, not a mask on an
inherited branch. -/
theorem exceptional_fifth_plus_zero_of_not_dvd
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hp : ¬ p ∣ (N - 2) / 2) :
    exceptionalFifthPlusFibre N cap w L X pre p = 0 := by
  unfold exceptionalFifthPlusFibre
  apply Finset.sum_eq_zero
  intro a ha
  have hneq : a * (p :: pre).prod ≠ (N - 2) / 2 := by
    intro heq
    apply hp
    refine ⟨a * pre.prod, ?_⟩
    simpa [List.prod_cons, mul_assoc, mul_comm, mul_left_comm] using heq.symm
  simp [hneq]

/-- Restrict the EXISTING ordered sixth occurrence list to the actual
divisors of q0. List.filter, unlike Finset, retains duplicates. -/
private theorem weighted_sixth_filter_eq_original
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (mass : ℝ) (ps : List ℕ) :
    (ps.map (fun p => mass *
      exceptionalFifthPlusFibre N cap w L X pre p)).sum =
    ((ps.filter (fun p => p ∣ (N - 2) / 2)).map (fun p => mass *
      exceptionalFifthPlusFibre N cap w L X pre p)).sum := by
  classical
  induction ps with
  | nil => simp
  | cons p ps ih =>
      by_cases hp : p ∣ (N - 2) / 2
      · simp [hp, ih]
      · have hz := exceptional_fifth_plus_zero_of_not_dvd
          N cap w L X pre p hp
        simp [hp, hz, ih]

/-- One ORIGINAL fifth event: the q0 centre correction can only be
carried by actual sixth occurrences dividing q0. No event is
deduplicated and no signed coefficient is replaced by fixed rho. -/
theorem common_sixth_exceptional_only_q0_divisor_occurrences
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    commonLargeSixthKernel N cap w L X
        (exceptionalCentreFibre N) fifth =
      (((fifth.remainingAfter.filter (fun p => p ∣ (N - 2) / 2)).map
        (fun p => signedTreeCoefficient true fifth.massAfter *
          exceptionalFifthPlusFibre N cap w L X
            fifth.selectedAfter p))).sum := by
  rw [common_sixth_exceptional_fibre_eq_original_weights]
  exact weighted_sixth_filter_eq_original
    N cap w L X fifth.selectedAfter
    (signedTreeCoefficient true fifth.massAfter) fifth.remainingAfter

/-- Elementary, explicit occurrence-sensitive envelope. -/
private theorem abs_weighted_sum_le_count
    (ps : List ℕ) (mass : ℝ) (f : ℕ → ℝ) :
    (∀ p ∈ ps, |f p| ≤ 1) →
    |(ps.map (fun p => mass * f p)).sum| ≤
      |mass| * (ps.length : ℝ) := by
  induction ps with
  | nil =>
      intro _
      simp
  | cons p ps ih =>
      intro hf
      have hfp : |f p| ≤ 1 := hf p (by simp)
      have hrest : ∀ p ∈ ps, |f p| ≤ 1 := by
        intro x hx
        exact hf x (by simp [hx])
      have hterm : |mass * f p| ≤ |mass| := by
        rw [abs_mul]
        calc
          |mass| * |f p| ≤ |mass| * 1 :=
            mul_le_mul_of_nonneg_left hfp (abs_nonneg mass)
          _ = |mass| := mul_one _
      have htail := ih hrest
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      calc
        |mass * f p + (ps.map (fun p => mass * f p)).sum| ≤
            |mass * f p| + |(ps.map (fun p => mass * f p)).sum| :=
              abs_add _ _
        _ ≤ |mass| + |mass| * (ps.length : ℝ) :=
              add_le_add hterm htail
        _ = |mass| * ((ps.length : ℝ) + 1) := by ring

/-- Quantitative, but honest: each remaining p|q0 costs at most
the absolute ORIGINAL signed fifth mass. This is a REAL per-event bound,
not a claim that the global stopped coefficient is <=1 or o(H_N). -/
theorem abs_common_sixth_q0_le_actual_divisor_occurrence_mass
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) (hN : 8 ≤ N) :
    |commonLargeSixthKernel N cap w L X
        (exceptionalCentreFibre N) fifth| ≤
      |signedTreeCoefficient true fifth.massAfter| *
        ((fifth.remainingAfter.filter (fun p => p ∣ (N - 2) / 2)).length : ℝ) := by
  rw [common_sixth_exceptional_only_q0_divisor_occurrences]
  exact abs_weighted_sum_le_count
    (fifth.remainingAfter.filter (fun p => p ∣ (N - 2) / 2))
    (signedTreeCoefficient true fifth.massAfter)
    (exceptionalFifthPlusFibre N cap w L X fifth.selectedAfter)
    (fun p hp => exceptional_fifth_plus_fibre_abs_le_one
      N cap w L X fifth.selectedAfter p hN)

end
end ImbalancedChen.P4AOriginalFull87StoppedQ0QuotientDivisor
