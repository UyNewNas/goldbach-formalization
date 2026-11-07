import ImbalancedChen.RealHalfProductSource
import ImbalancedChen.PowerErrorBudget
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Sqrt

/-!
# Prime-square diagonal count budget (P4B, source-only)

YELLOW / UNCOMPILED. The actual real source retains prime squares. Their
unweighted count is bounded by sqrt N and is negligible in the actual
singularNormalization. This does not bound a signed distribution term or
a divisor-weighted diagonal by its cardinality.
-/

namespace ImbalancedChen.P4BDiagonalSquareBudget

noncomputable section

open Filter Topology

/-- A property of the integer itself, independent of a chosen factor pair. -/
def IsPrimeSquare (m : ℕ) : Prop := ∃ p : ℕ, Nat.Prime p ∧ m = p * p

def primeSquareDiagonal (S : Finset ℕ) : Finset ℕ := by
  classical
  exact S.filter IsPrimeSquare

def offDiagonal (S : Finset ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun m => ¬IsPrimeSquare m)

/-- Each prime root occurs once, including the upper square endpoint. -/
def primeSquareRoots (S : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.sqrt N + 1)).filter
    (fun p => Nat.Prime p ∧ p * p ∈ S)

def sourceDiagonal (b : ℝ) (N : ℕ) (T : ℝ) : Finset ℕ :=
  primeSquareDiagonal (realHalfProductSource b N T)

def actualBadDiagonal (b : ℝ) (N : ℕ) : Finset ℕ :=
  primeSquareDiagonal (realBadReceivers b N)

@[simp] theorem mem_primeSquareDiagonal {S : Finset ℕ} {m : ℕ} :
    m ∈ primeSquareDiagonal S ↔ m ∈ S ∧ IsPrimeSquare m := by
  classical
  simp only [primeSquareDiagonal, Finset.mem_filter]

@[simp] theorem mem_offDiagonal {S : Finset ℕ} {m : ℕ} :
    m ∈ offDiagonal S ↔ m ∈ S ∧ ¬IsPrimeSquare m := by
  classical
  simp only [offDiagonal, Finset.mem_filter]

@[simp] theorem mem_primeSquareRoots {S : Finset ℕ} {N p : ℕ} :
    p ∈ primeSquareRoots S N ↔ p ≤ Nat.sqrt N ∧ Nat.Prime p ∧ p * p ∈ S := by
  classical
  simp only [primeSquareRoots, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- No factor of two is needed for the diagonal map. -/
theorem prime_square_map_injective : Function.Injective (fun p : ℕ => p * p) := by
  intro p q hpq
  exact Nat.mul_self_inj.mp hpq

theorem primeSquareRoots_card_eq_diagonal (S : Finset ℕ) (N : ℕ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (primeSquareRoots S N).card = (primeSquareDiagonal S).card := by
  classical
  refine Finset.card_bij (fun p _ => p * p) ?_ ?_ ?_
  · intro p hp
    obtain ⟨_, hprime, hmem⟩ := mem_primeSquareRoots.mp hp
    exact mem_primeSquareDiagonal.mpr ⟨hmem, p, hprime, rfl⟩
  · intro p hp q hq hpq
    exact prime_square_map_injective hpq
  · intro m hm
    obtain ⟨hmS, p, hp, hsq⟩ := mem_primeSquareDiagonal.mp hm
    have hsqN : p * p ≤ N := hsq ▸ hSN m hmS
    refine ⟨p, mem_primeSquareRoots.mpr ⟨Nat.le_sqrt.mpr hsqN, hp, ?_⟩,
      hsq.symm⟩
    simpa only [hsq] using hmS

/-- The map p ↦ p-1 places the positive roots in [0,sqrt N), including
the case sqrt N=0. Prime roots give a stronger bound than sqrt N+1. -/
theorem primeSquareRoots_card_le_sqrt (S : Finset ℕ) (N : ℕ) :
    (primeSquareRoots S N).card ≤ Nat.sqrt N := by
  classical
  calc
    (primeSquareRoots S N).card ≤ (Finset.range (Nat.sqrt N)).card := by
      apply Finset.card_le_card_of_injOn (fun p : ℕ => p - 1)
      · intro p hp
        obtain ⟨hpN, hpPrime, _⟩ := mem_primeSquareRoots.mp hp
        have hp0 := hpPrime.pos
        exact Finset.mem_range.mpr (by omega)
      · intro p hp q hq hpq
        have hp0 := (mem_primeSquareRoots.mp hp).2.1.pos
        have hq0 := (mem_primeSquareRoots.mp hq).2.1.pos
        change p - 1 = q - 1 at hpq
        omega
    _ = Nat.sqrt N := Finset.card_range _

theorem primeSquareDiagonal_card_le_sqrt (S : Finset ℕ) (N : ℕ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (primeSquareDiagonal S).card ≤ Nat.sqrt N := by
  rw [← primeSquareRoots_card_eq_diagonal S N hSN]
  exact primeSquareRoots_card_le_sqrt S N

theorem sourceDiagonal_card_le_sqrt (b : ℝ) (N : ℕ) (T : ℝ) :
    (sourceDiagonal b N T).card ≤ Nat.sqrt N := by
  apply primeSquareDiagonal_card_le_sqrt
  intro m hm
  exact (mem_realHalfProductSource.mp hm).1

theorem actualBadDiagonal_card_le_sqrt (b : ℝ) (N : ℕ) :
    (actualBadDiagonal b N).card ≤ Nat.sqrt N := by
  apply primeSquareDiagonal_card_le_sqrt
  intro m hm
  exact (mem_realBadReceivers.mp hm).1.le

/-- The actual receiver diagonal is exactly the uncut source diagonal
with the original strict endpoint and additive-prime filter. -/
theorem actualBadDiagonal_eq_sourceDiagonal_filter (b : ℝ) (N : ℕ) :
    actualBadDiagonal b N = (sourceDiagonal b N 0).filter
      (fun m => m < N ∧ Nat.Prime (N - m)) := by
  classical
  ext m
  simp only [actualBadDiagonal, sourceDiagonal, mem_primeSquareDiagonal,
    Finset.mem_filter]
  constructor
  · rintro ⟨hm, hsq⟩
    obtain ⟨hmN, _, hp, hbad⟩ := mem_realBadReceivers.mp hm
    exact ⟨⟨mem_realHalfProductSource.mpr
      ⟨hmN.le, Nat.cast_nonneg m, hbad⟩, hsq⟩, hmN, hp⟩
  · rintro ⟨⟨hsource, hsq⟩, hmN, hp⟩
    exact ⟨mem_realBadReceivers.mpr ⟨hmN, realHalfProductSource_pos hsource,
      hp, (mem_realHalfProductSource.mp hsource).2.2⟩, hsq⟩

/-- The diagonal r=q of the actual ordered pair source has exactly the
same cardinality as the prime-square integers. It is counted once. -/
theorem diagonalPairs_card_eq_sourceDiagonal (b : ℝ) (N : ℕ) (T : ℝ) :
    ((realHalfProductPairs b N T).filter (fun a => a.1 = a.2)).card =
      (sourceDiagonal b N T).card := by
  classical
  refine Finset.card_bij (fun a _ => a.1 * a.2) ?_ ?_ ?_
  · intro a ha
    obtain ⟨haPair, hdiag⟩ := Finset.mem_filter.mp ha
    have hprime := (mem_realHalfProductPairs.mp haPair).1
    apply mem_primeSquareDiagonal.mpr
    exact ⟨mul_mem_realHalfProductSource haPair, a.1, hprime, by rw [hdiag]⟩
  · intro a ha c hc hmul
    exact realHalfProductPairs_mul_injective
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hc).1 hmul
  · intro m hm
    obtain ⟨hsource, p, hp, hsq⟩ := mem_primeSquareDiagonal.mp hm
    obtain ⟨hmN, hcut, r, q, hr, hq, hmul, hrq, hpow⟩ :=
      mem_realHalfProductSource.mp hsource
    have hfac : r = p ∧ q = p :=
      ordered_prime_factors_unique hr hq hp hp hrq le_rfl (hmul.symm.trans hsq)
    have hpowP : (p : ℝ) ^ b < (p : ℝ) := by
      simpa only [hfac.1, hfac.2] using hpow
    have hpPair : (p, p) ∈ realHalfProductPairs b N T :=
      mem_realHalfProductPairs.mpr
        ⟨hp, hp, le_rfl, hpowP, hsq ▸ hcut, hsq ▸ hmN⟩
    exact ⟨(p, p), Finset.mem_filter.mpr ⟨hpPair, rfl⟩, hsq.symm⟩

theorem card_eq_offDiagonal_add_diagonal (S : Finset ℕ) :
    S.card = (offDiagonal S).card + (primeSquareDiagonal S).card := by
  classical
  simpa only [offDiagonal, primeSquareDiagonal, not_not] using
    (Finset.card_filter_add_card_filter_not (s := S)
      (fun m => ¬IsPrimeSquare m)).symm

theorem offDiagonal_disjoint_diagonal (S : Finset ℕ) :
    Disjoint (offDiagonal S) (primeSquareDiagonal S) := by
  classical
  apply Finset.disjoint_left.mpr
  intro m hoff hdiag
  exact (mem_offDiagonal.mp hoff).2 (mem_primeSquareDiagonal.mp hdiag).2

theorem RealB_eq_offDiagonal_add_diagonal {b : ℝ} (hb : b < 1) (N : ℕ) :
    RealB b N = (offDiagonal (realBadReceivers b N)).card +
      (actualBadDiagonal b N).card := by
  rw [RealB_eq_realBadReceivers_card hb]
  exact card_eq_offDiagonal_add_diagonal _

theorem sourceDiagonal_cast_le_half_power (b : ℝ) (N : ℕ) (T : ℝ) :
    ((sourceDiagonal b N T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  calc
    ((sourceDiagonal b N T).card : ℝ) ≤ (Nat.sqrt N : ℝ) :=
      Nat.cast_le.mpr (sourceDiagonal_card_le_sqrt b N T)
    _ ≤ Real.sqrt (N : ℝ) := Real.nat_sqrt_le_real_sqrt
    _ = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _

theorem actualBadDiagonal_cast_le_half_power (b : ℝ) (N : ℕ) :
    ((actualBadDiagonal b N).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  calc
    ((actualBadDiagonal b N).card : ℝ) ≤ (Nat.sqrt N : ℝ) :=
      Nat.cast_le.mpr (actualBadDiagonal_card_le_sqrt b N)
    _ ≤ Real.sqrt (N : ℝ) := Real.nat_sqrt_le_real_sqrt
    _ = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _

/-- The existing proved power budget, at exponent 1/2, handles every
source cutoff and every real b uniformly. No evenness restriction is needed. -/
theorem eventually_diagonal_counts_le_normalization (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ b T : ℝ,
      ((sourceDiagonal b N T).card : ℝ) ≤ eta * singularNormalization N ∧
      ((actualBadDiagonal b N).card : ℝ) ≤ eta * singularNormalization N := by
  have hbudget : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 / 2 : ℝ) ≤ eta * singularNormalization N := by
    simpa only [one_mul, pow_zero, mul_one] using
      eventually_powerLog_le_singularNormalization 1 (1 / 2) 0
        (by norm_num) eta heta
  filter_upwards [hbudget] with N hN
  intro b T
  exact ⟨(sourceDiagonal_cast_le_half_power b N T).trans hN,
    (actualBadDiagonal_cast_le_half_power b N).trans hN⟩

/-- A supplier that counts only actual nonsquare bad receivers may pay
the square diagonal once as an unweighted count on the genuine scale. -/
theorem eventually_RealB_le_offDiagonal_add_budget (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℝ, b < 1 →
      (RealB b N : ℝ) ≤ ((offDiagonal (realBadReceivers b N)).card : ℝ) +
        eta * singularNormalization N := by
  filter_upwards [eventually_diagonal_counts_le_normalization eta heta] with N hN
  intro b hb
  rw [RealB_eq_offDiagonal_add_diagonal hb N, Nat.cast_add]
  exact add_le_add_left (hN b 0).2 _

end

end ImbalancedChen.P4BDiagonalSquareBudget
