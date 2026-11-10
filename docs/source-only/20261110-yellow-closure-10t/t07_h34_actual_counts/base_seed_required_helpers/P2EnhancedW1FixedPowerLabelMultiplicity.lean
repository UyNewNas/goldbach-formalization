import ImbalancedChen.P2EnhancedW1SelectedBadLabelFibres
import Mathlib.Data.Nat.Factorization.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual multiplicity of the eligible W1 quotient prime labels at one
old marked B. Distinct eligible labels belong to the prime-factor
Finset of n=(N-ell)/B. Their product divides n, and each label is at
least the graph-derived fixed power N^eta. Thus the real fibre cardinal
is at most 1/eta, independently of N, B, ell and the old predicate E.
The selected graph action is retained as StepShape.w1Singleton(i,j).

This closes the fixed-power multiplicity *estimate*. It does not yet
bind integer prime q to the graph's real action coordinate or prove
History.step acceptance and the exact K-positive source theorem.

Original: manuscript-body.tex 790--817, 819--875;
same-new-level-double-sieve-route.tex 93--105, 147--165.
-/

namespace ImbalancedChen.P2EnhancedW1FixedPowerLabelMultiplicity

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition (StepShape LocalDomain)
open P2EnhancedLowerFinitePhysicalGraph (TypedNode Program Coordinates Member realize)
open P2EnhancedW1R2ActualCarrierBranch (eligiblePrimes eligiblePrime_data)
open P2EnhancedW1SelectedBadLabelFibres
  (badLaterLabels selected_bad_label_sum_le_square_fibre_sum)
open P2EnhancedW1SquareExceptionPower (squareEvent)
open P2EnhancedW1RepeatedLabelClassification
  (physical_level_eq_parent_residual graph_w1_fixed_power)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2LargerSActualPositiveCounts (historyCarrier)
open P5OriginalActionMassBound (W1Anchor)

/-- Elementary nonnegative real product bound; it avoids applying a
monotone-multiplication lemma to unrestricted real factors. -/
private theorem real_power_card_le_prime_product
    (P : Finset ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hP : ∀ q ∈ P, z ≤ (q : ℝ)) :
    z^P.card ≤ ∏ q ∈ P, (q : ℝ) := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | @insert q P hqP ih =>
      intro hP
      have hq : z ≤ (q : ℝ) := hP q (by simp)
      have hrest : ∀ r ∈ P, z ≤ (r : ℝ) := by
        intro r hr
        exact hP r (by simp [hr])
      have hih := ih hrest
      have hqnonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      calc
        z^(insert q P).card = z * z^P.card := by
          rw [Finset.card_insert_of_not_mem hqP, pow_succ]
          ring
        _ ≤ (q : ℝ) * z^P.card :=
          mul_le_mul_of_nonneg_right hq (pow_nonneg hz _)
        _ ≤ (q : ℝ) * (∏ r ∈ P, (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hih hqnonneg
        _ = ∏ r ∈ insert q P, (r : ℝ) := by
          rw [Finset.prod_insert hqP]

/-- Prime-factor product lemma at the exact quotient, without any
arithmetic label counting assumption. -/
theorem prime_factor_fibre_card_le_inv_power
    (N n : ℕ) (P : Finset ℕ) (eta : ℝ)
    (hN : 1 < N) (hn : 0 < n) (hnN : n ≤ N)
    (hP : P ⊆ n.primeFactors)
    (heta : 0 < eta)
    (hcut : ∀ q ∈ P, (N : ℝ)^eta ≤ (q : ℝ)) :
    (P.card : ℝ) ≤ 1/eta := by
  have hprodDvd : (∏ q ∈ P, q) ∣ n :=
    (Finset.prod_dvd_prod_of_subset P n.primeFactors id hP).trans
      (Nat.prod_primeFactors_dvd n)
  have hprodLe : (∏ q ∈ P, q) ≤ N :=
    (Nat.le_of_dvd hn hprodDvd).trans hnN
  have hprodReal : (∏ q ∈ P, (q : ℝ)) =
      ((∏ q ∈ P, q) : ℝ) := by norm_cast
  have hprodRealLe : (∏ q ∈ P, (q : ℝ)) ≤ (N : ℝ) := by
    rw [hprodReal]
    exact_mod_cast hprodLe
  have hpow : ((N : ℝ)^eta)^P.card ≤ ∏ q ∈ P, (q : ℝ) :=
    real_power_card_le_prime_product P _
      (Real.rpow_nonneg (Nat.cast_nonneg N) eta) hcut
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hpowEq : (N : ℝ)^(eta*(P.card : ℝ)) =
      ((N : ℝ)^eta)^P.card := by
    rw [Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_natCast]
  have hpowLe : (N : ℝ)^(eta*(P.card : ℝ)) ≤ (N : ℝ)^1 := by
    rw [hpowEq, Real.rpow_one]
    exact hpow.trans hprodRealLe
  have hEtaCard : eta*(P.card : ℝ) ≤ 1 :=
    (Real.rpow_le_rpow_left_iff hNreal).mp hpowLe
  apply (le_div_iff₀ heta).mpr
  nlinarith only [hEtaCard]

/-- The actual eligible quotient primes of one W1 receiver have a
uniform fibre cap whenever the actual unchanged-Q cutoff is >= N^eta.
The parent old-mask historyCarrier supplies the true positive quotient. -/
theorem eligiblePrimes_card_le_inv_fixed_power
    {N ell : ℕ} {Q chi eta : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {E : ℕ → ℕ → Prop}
    (hw : parentWindow N Q old chi)
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (heta : 0 < eta)
    (hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j)) :
    ((eligiblePrimes N ell Q old i j).card : ℝ) ≤ 1/eta := by
  let n := (N-ell)/old.prod
  have hB : 0 < old.prod := hw.2.1
  obtain ⟨hsource,_⟩ := Finset.mem_filter.mp hell
  have hdiv : old.prod ∣ N-ell := (Finset.mem_filter.mp hsource).2.2.1
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hcomp hdiv) hB
  have hnN : n ≤ N :=
    (Nat.div_le_self (N-ell) old.prod).trans (Nat.sub_le N ell)
  have hP : eligiblePrimes N ell Q old i j ⊆ n.primeFactors := by
    intro q hq
    have hd := eligiblePrime_data hq
    exact Nat.mem_primeFactors.mpr ⟨hd.1,hd.2.1,hn.ne'⟩
  have hPcut : ∀ q ∈ eligiblePrimes N ell Q old i j,
      (N : ℝ)^eta ≤ (q : ℝ) := by
    intro q hq
    exact hcut.trans (eligiblePrime_data hq).2.2.1
  exact prime_factor_fibre_card_le_inv_power N n
    (eligiblePrimes N ell Q old i j) eta hw.1 hn hnN hP heta hPcut

/-- The selected finite physical graph supplies eta from its own
residual contraction. The integer old word and Q are aligned at the
realized parent; this theorem does not posit an opaque cutoff bound. -/
theorem graph_selected_eligible_fibre_fixed_power
    {N mesh depth ell : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop}
    {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth} {action : Program mesh 1}
    {actionZ : Coordinates 1}
    (hprev : Member lo hi depth root code z)
    (hshape : (action 0).1 = StepShape.w1Singleton i j)
    (haction : Member lo hi 1
      ⟨true,(realize depth root code z).physical⟩ action actionZ)
    (hgamma : 0 < gamma)
    (hroot : gamma ≤ residual root.physical)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word (realize depth root code z).physical =
      old.map (physicalPrime N))
    (htotal : (realize depth root code z).physical.total =
      Real.log Q / Real.log (N : ℝ))
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j))) :
    LocalDomain (realize depth root code z).physical
      (.w1Singleton i j) (actionZ 0) ∧
    ((eligiblePrimes N ell Q old i j).card : ℝ) ≤
      1 / ((gamma/(101:ℝ)^depth)/5) := by
  have hlocal : LocalDomain (realize depth root code z).physical
      (.w1Singleton i j) (actionZ 0) := by
    simpa only [hshape] using haction.2.2.1
  have hcoord : physicalLevel N Q old =
      residual (realize depth root code z).physical :=
    physical_level_eq_parent_residual hw hprime hword htotal
  have hcut := graph_w1_fixed_power hprev hroot hgamma hw hcoord j
  have hden : (0 : ℝ) < (101:ℝ)^depth := pow_pos (by norm_num) _
  have heta : 0 < ((gamma/(101:ℝ)^depth)/5) := by
    exact div_pos (div_pos hgamma hden) (by norm_num)
  exact ⟨hlocal, eligiblePrimes_card_le_inv_fixed_power hw hcomp
    hell heta hcut⟩

/-- The exact selected bad-q sum is now paid by ONE physical square
event count, with its fixed graph-derived multiplicity 1/eta and the
unchanged sigma(B). This is a one-B finite payment, not a K theorem. -/
theorem graph_selected_bad_label_sum_le_squareEvent
    {N mesh depth : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {sigma : ℕ → ℝ} {C : Finset ℕ}
    {a b : ℕ → ℕ}
    {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth} {action : Program mesh 1}
    {actionZ : Coordinates 1}
    (hprev : Member lo hi depth root code z)
    (hshape : (action 0).1 = StepShape.w1Singleton i j)
    (haction : Member lo hi 1
      ⟨true,(realize depth root code z).physical⟩ action actionZ)
    (hgamma : 0 < gamma)
    (hroot : gamma ≤ residual root.physical)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word (realize depth root code z).physical =
      old.map (physicalPrime N))
    (htotal : (realize depth root code z).physical.total =
      Real.log Q / Real.log (N : ℝ))
    (hsigma : 0 ≤ sigma old.prod)
    (hC : C ⊆ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (hfirst : ∀ ell ∈ C,
      0 < N-ell ∧
      a ell ∈ eligiblePrimes N ell Q old i j ∧
      b ell ∈ eligiblePrimes N ell Q old i j ∧
      a ell < b ell ∧
      (∀ r ∈ eligiblePrimes N ell Q old i j,
        r ≠ a ell → b ell ≤ r)) :
    (∑ ell ∈ C, sigma old.prod *
      ((badLaterLabels N ell Q old i j E (a ell) (b ell)).card : ℝ)) ≤
    (sigma old.prod / ((gamma/(101:ℝ)^depth)/5)) *
      ((squareEvent N old.prod E
        (cutoff Q old.prod (W1Anchor j))
        ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))).card : ℝ) := by
  let eta : ℝ := (gamma/(101:ℝ)^depth)/5
  let event := squareEvent N old.prod E
    (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^eta)
  have hden : (0 : ℝ) < (101:ℝ)^depth := pow_pos (by norm_num) _
  have heta : 0 < eta := div_pos (div_pos hgamma hden) (by norm_num)
  have hbase := selected_bad_label_sum_le_square_fibre_sum
    hprev hshape haction hgamma hroot hw hprime hword htotal
    hsigma hC hfirst
  have hcap (ell : ℕ) (hc : ell ∈ C) :
      ((eligiblePrimes N ell Q old i j).card : ℝ) ≤ 1/eta := by
    have hdata := hfirst ell hc
    exact (graph_selected_eligible_fibre_fixed_power hprev hshape
      haction hgamma hroot hw hprime hword htotal hdata.1
      (hC hc)).2
  have hfilter : C.filter (fun ell => ell ∈ event) ⊆ event := by
    intro ell h
    exact (Finset.mem_filter.mp h).2
  have hcard : ((C.filter (fun ell => ell ∈ event)).card : ℝ) ≤
      (event.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hfilter
  calc
    _ ≤ ∑ ell ∈ C, sigma old.prod *
        (if ell ∈ event then
          ((eligiblePrimes N ell Q old i j).card : ℝ) else 0) := hbase
    _ ≤ ∑ ell ∈ C, sigma old.prod *
        (if ell ∈ event then (1/eta : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro ell hc
      by_cases he : ell ∈ event
      · simpa [he] using mul_le_mul_of_nonneg_left (hcap ell hc) hsigma
      · simp [he]
    _ = (sigma old.prod / eta) *
        ((C.filter (fun ell => ell ∈ event)).card : ℝ) := by
      calc
        (∑ ell ∈ C, sigma old.prod *
          (if ell ∈ event then (1/eta : ℝ) else 0)) =
            ∑ ell ∈ C, if ell ∈ event then sigma old.prod / eta else 0 := by
          apply Finset.sum_congr rfl
          intro ell _
          by_cases he : ell ∈ event <;> simp [he, div_eq_mul_inv]
        _ = ∑ ell ∈ C.filter (fun ell => ell ∈ event),
              sigma old.prod / eta := by
          rw [Finset.sum_filter]
        _ = (sigma old.prod / eta) *
              ((C.filter (fun ell => ell ∈ event)).card : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]
    _ ≤ (sigma old.prod / eta) * (event.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hcard (div_nonneg hsigma heta.le)
    _ = _ := rfl

end
end ImbalancedChen.P2EnhancedW1FixedPowerLabelMultiplicity
