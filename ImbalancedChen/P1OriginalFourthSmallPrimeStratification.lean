import ImbalancedChen.P1OriginalCoarseFourthArithmeticWall
import ImbalancedChen.P1OriginalCoarseFourthCellLimit
import ImbalancedChen.P1HistoricalUpperFourthPhysicalGates

/-!
# Exact arithmetic stratification of the original small-prime remainder

The source is the original coarse-policy admitted fourth carrier, with its
actual cell ownership and last logarithmic coordinate below a.  Strict
prime order identifies this condition with the original existential small
coordinate predicate.  The original normalized old/new PLUS residuals and
signed reciprocal-prime weights are retained in every bin.

The owner consists of floor(a/tlast), floor(s_old), floor(s_new).  The first
floor is natural; the two s floors are integers, so finite partitioning does
not presuppose a cap4 legality license.  Indices are the actual finite
source.image of this owner, rather than an invented bounded range.

This is exact finite arithmetic, not a small-a estimate.  Large-s residual
decay and the eventual sum of bin payments remain separate supplier work.
Source-only/uncompiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set
open P1OriginalCoarseContinuation P1OriginalCoarseFourthArithmeticWall

namespace P1OriginalFourthSmallPrimeStratification

abbrev PrimeTuple := Fin 4 → ℕ
abbrev Bin := ℕ × ℤ × ℤ

/-- Actual original admitted tuples, retaining the original outer rough cutoff. -/
def admitted (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) : Finset PrimeTuple :=
  firstExitAdmittedTuples 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))

theorem admitted_log_data (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N) (p : PrimeTuple) (hp : p ∈ admitted e chi m omega N cap) :
    StrictAnti (actualPrimeTupleLog N p) ∧ (∀ i, Nat.Prime (p i)) ∧
      (∀ i, 0 < actualPrimeTupleLog N p i) := by
  have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) p).mp hp
  have hprime : ∀ i, Nat.Prime (p i) := fun i => mem_roughPrimeUniverse_prime (hd.2.1 i)
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  refine ⟨(actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hprime i).pos)).mpr hd.1,
    hprime, ?_⟩
  intro i
  have hpi : (1 : ℝ) < p i := by exact_mod_cast (hprime i).one_lt
  exact div_pos (Real.log_pos hpi) (Real.log_pos hn)

theorem exists_small_iff_last {t : Fin 4 → ℝ} (ht : StrictAnti t) (a : ℝ) :
    (∃ i, t i < a) ↔ t (Fin.last 3) < a := by
  constructor
  · rintro ⟨i, hi⟩
    exact (ht.antitone (Fin.le_last i)).trans_lt hi
  · intro h
    exact ⟨Fin.last 3, h⟩

/-- The original active third prime is coordinate 2, not the fourth prime.
Whole-active selected cells bound all first THREE log coordinates below. -/
theorem selected_first_three_ge_omega
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J4 : Finset (FourthCell m))
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (t : Fin 4 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hanti : StrictAnti t) :
    ∀ i : Fin 3, omega ≤ t ⟨i.val, by omega⟩ := by
  have hlic := (mem_selectedFourthCells e chi m omega J4 j).mp hj
  have hproj := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht
  have hcast : (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 4) j)) 2
  have hthird : omega ≤ t 2 := by
    have hrough := hlic.2.2
    rw [hcast] at hrough
    exact hrough.trans (mem_logPrimeMeshCell.mp hproj 2).1
  intro i
  have hi : (⟨i.val, by omega⟩ : Fin 4) ≤ 2 := by omega
  exact hthird.trans (hanti.antitone hi)

/-- In particular the original selected source has its actual third-prime
rough activation, including equality at N^omega. -/
theorem selected_third_prime_rough
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J4 : Finset (FourthCell m))
    (N cap : ℕ) (hN : 1 < N) (p : PrimeTuple) (hp : p ∈ admitted e chi m omega N cap)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (N : ℝ) ^ omega ≤ (p 2 : ℝ) := by
  have hd := admitted_log_data e chi m omega N cap hN p hp
  have hrough := selected_first_three_ge_omega e chi m omega J4 j hj _ ht hd.1 (2 : Fin 3)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h := Real.rpow_le_rpow_of_exponent_le hn hrough
  rw [actualPrimeTupleLog_rpow hN p (fun i => (hd.2.1 i).pos) (2 : Fin 4)] at h
  exact h

/-- The exact actual source omitted by a positive-cube truncation, on one owner. -/
def smallCellTuples (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (j : FourthCell m) : Finset PrimeTuple :=
  (admitted e chi m omega N cap).filter fun p =>
    actualPrimeTupleLog N p (Fin.last 3) < a ∧
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j

theorem smallCellTuples_eq_original_filter
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (j : FourthCell m) :
    smallCellTuples e chi m omega a N cap j =
      (admitted e chi m omega N cap).filter (fun p =>
        (∃ i, actualPrimeTupleLog N p i < a) ∧
          actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) := by
  ext p
  simp only [smallCellTuples, Finset.mem_filter]
  apply and_congr_right
  intro hp
  exact and_congr (exists_small_iff_last (admitted_log_data e chi m omega N cap hN p hp).1 a).symm
    Iff.rfl

theorem smallCellTuple_first_three_large
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (haomega : a ≤ omega)
    (J4 : Finset (FourthCell m)) (N cap : ℕ) (hN : 1 < N)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (p : PrimeTuple) (hp : p ∈ smallCellTuples e chi m omega a N cap j) :
    (∀ i : Fin 3, a ≤ actualPrimeTupleLog N p ⟨i.val, by omega⟩) ∧
      actualPrimeTupleLog N p (Fin.last 3) < a := by
  obtain ⟨had, hlast, ht⟩ := Finset.mem_filter.mp hp
  have hanti := (admitted_log_data e chi m omega N cap hN p had).1
  exact ⟨fun i => haomega.trans
    (selected_first_three_ge_omega e chi m omega J4 j hj _ ht hanti i), hlast⟩

def residualS (lambda : ℝ) (N : ℕ) (p : PrimeTuple) : ℝ :=
  (lambda - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p (Fin.last 3)

def binOwner (a old new : ℝ) (N : ℕ) (p : PrimeTuple) : Bin :=
  (⌊a / actualPrimeTupleLog N p (Fin.last 3)⌋₊,
    ⌊residualS old N p⌋, ⌊residualS new N p⌋)

/-- This is a finite image of the ACTUAL source, with no artificial tail cap. -/
def sourceBins (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ) : Finset Bin :=
  S.image (binOwner a old new N)

def sourceBin (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ) (k : Bin) :
    Finset PrimeTuple := S.filter fun p => binOwner a old new N p = k

theorem unique_sourceBin (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ)
    (p : PrimeTuple) (hp : p ∈ S) :
    ∃! k, k ∈ sourceBins S a old new N ∧ p ∈ sourceBin S a old new N k := by
  refine ⟨binOwner a old new N p, ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
    Finset.mem_filter.mpr ⟨hp, rfl⟩⟩, ?_⟩
  intro k hk
  exact (Finset.mem_filter.mp hk.2).2.symm

theorem sourceBins_disjoint (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ)
    (k l : Bin) (hne : k ≠ l) :
    Disjoint (sourceBin S a old new N k) (sourceBin S a old new N l) := by
  rw [Finset.disjoint_left]
  intro p hk hl
  exact hne ((Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hl).2)

theorem source_eq_biUnion_bins (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ) :
    S = (sourceBins S a old new N).biUnion (sourceBin S a old new N) := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨binOwner a old new N p,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  · intro hp
    obtain ⟨k, _hk, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hp).1

theorem sum_source_eq_bins (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ)
    (f : PrimeTuple → ℝ) :
    (∑ p ∈ S, f p) =
      ∑ k ∈ sourceBins S a old new N, ∑ p ∈ sourceBin S a old new N k, f p := by
  calc
    _ = ∑ p ∈ (sourceBins S a old new N).biUnion (sourceBin S a old new N), f p :=
      congrArg (fun T : Finset PrimeTuple => ∑ p ∈ T, f p) (source_eq_biUnion_bins S a old new N)
    _ = _ := by
      apply Finset.sum_biUnion
      intro k _hk l _hl hne
      exact sourceBins_disjoint S a old new N k l hne

/-- Every s-floor bin has its literal closed/open bounds without a positivity
or cap-order premise. Integer floors preserve the full source in this step. -/
theorem sourceBin_s_bounds (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ)
    (k : Bin) (p : PrimeTuple) (hp : p ∈ sourceBin S a old new N k) :
    (k.2.1 : ℝ) ≤ residualS old N p ∧ residualS old N p < (k.2.1 : ℝ) + 1 ∧
      (k.2.2 : ℝ) ≤ residualS new N p ∧ residualS new N p < (k.2.2 : ℝ) + 1 := by
  have hk := (Finset.mem_filter.mp hp).2
  have hold : ⌊residualS old N p⌋ = k.2.1 := congrArg (fun q : Bin => q.2.1) hk
  have hnew : ⌊residualS new N p⌋ = k.2.2 := congrArg (fun q : Bin => q.2.2) hk
  exact ⟨by simpa only [hold] using Int.floor_le (residualS old N p),
    by simpa only [hold] using Int.lt_floor_add_one (residualS old N p),
    by simpa only [hnew] using Int.floor_le (residualS new N p),
    by simpa only [hnew] using Int.lt_floor_add_one (residualS new N p)⟩

theorem sourceBin_common_parameter (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ)
    (k : Bin) (p : PrimeTuple) (hp : p ∈ sourceBin S a old new N k)
    (t : ℝ) (hold : t ≤ (k.2.1 : ℝ)) (hnew : t ≤ (k.2.2 : ℝ)) :
    t ≤ residualS old N p ∧ t ≤ residualS new N p := by
  have h := sourceBin_s_bounds S a old new N k p hp
  exact ⟨hold.trans h.1, hnew.trans h.2.2.1⟩

/-- The reciprocal-cutoff floor provides genuine natural-prime band bounds.
Its bands are a/(k+1)<tlast<=a/k; endpoints have one unique owner. -/
theorem smallBin_cutoffs
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ) (ha : 0 < a)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) (k : Bin) (p : PrimeTuple)
    (hp : p ∈ sourceBin (smallCellTuples e chi m omega a N cap j) a old new N k) :
    1 ≤ k.1 ∧ a / ((k.1 : ℝ) + 1) < actualPrimeTupleLog N p (Fin.last 3) ∧
      actualPrimeTupleLog N p (Fin.last 3) ≤ a / (k.1 : ℝ) ∧
      (N : ℝ) ^ (a / ((k.1 : ℝ) + 1)) < (p (Fin.last 3) : ℝ) ∧
      (p (Fin.last 3) : ℝ) ≤ (N : ℝ) ^ (a / (k.1 : ℝ)) := by
  obtain ⟨hpS, howner⟩ := Finset.mem_filter.mp hp
  obtain ⟨had, hlast, _ht⟩ := Finset.mem_filter.mp hpS
  have hd := admitted_log_data e chi m omega N cap hN p had
  have hpos := hd.2.2 (Fin.last 3)
  have hk : ⌊a / actualPrimeTupleLog N p (Fin.last 3)⌋₊ = k.1 := congrArg Prod.fst howner
  have hratio : (1 : ℝ) ≤ a / actualPrimeTupleLog N p (Fin.last 3) :=
    (one_le_div hpos).mpr hlast.le
  have hk1 : 1 ≤ k.1 := by
    rw [← hk]
    exact (Nat.one_le_floor_iff _).mpr hratio
  have hkpos : (0 : ℝ) < k.1 := by exact_mod_cast (show 0 < k.1 by omega)
  have hfloor : (k.1 : ℝ) ≤ a / actualPrimeTupleLog N p (Fin.last 3) := by
    rw [← hk]
    exact Nat.floor_le (div_nonneg ha.le hpos.le)
  have hnext : a / actualPrimeTupleLog N p (Fin.last 3) < (k.1 : ℝ) + 1 := by
    simpa only [hk] using Nat.lt_floor_add_one (a / actualPrimeTupleLog N p (Fin.last 3))
  have hlo : a / ((k.1 : ℝ) + 1) < actualPrimeTupleLog N p (Fin.last 3) := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (k.1 : ℝ) + 1)).mpr
    nlinarith [(div_lt_iff₀ hpos).mp hnext]
  have hhi : actualPrimeTupleLog N p (Fin.last 3) ≤ a / (k.1 : ℝ) := by
    apply (le_div_iff₀ hkpos).mpr
    nlinarith [(le_div_iff₀ hpos).mp hfloor]
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hrpow := actualPrimeTupleLog_rpow hN p (fun i => (hd.2.1 i).pos) (Fin.last 3)
  refine ⟨hk1, hlo, hhi, ?_, ?_⟩
  · rw [← hrpow, Real.rpow_lt_rpow_left_iff hn]
    exact hlo
  · rw [← hrpow, Real.rpow_le_rpow_left_iff hn]
    exact hhi

theorem smallBin_s_numerator_bounds
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) (k : Bin) (p : PrimeTuple)
    (hp : p ∈ sourceBin (smallCellTuples e chi m omega a N cap j) a old new N k) :
    (k.2.1 : ℝ) * actualPrimeTupleLog N p (Fin.last 3) ≤ old - ∑ i, actualPrimeTupleLog N p i ∧
      old - (∑ i, actualPrimeTupleLog N p i) <
        ((k.2.1 : ℝ) + 1) * actualPrimeTupleLog N p (Fin.last 3) ∧
      (k.2.2 : ℝ) * actualPrimeTupleLog N p (Fin.last 3) ≤ new - ∑ i, actualPrimeTupleLog N p i ∧
      new - (∑ i, actualPrimeTupleLog N p i) <
        ((k.2.2 : ℝ) + 1) * actualPrimeTupleLog N p (Fin.last 3) := by
  have had := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have ht := (admitted_log_data e chi m omega N cap hN p had).2.2 (Fin.last 3)
  have h := sourceBin_s_bounds _ a old new N k p hp
  exact ⟨(le_div_iff₀ ht).mp h.1, (div_lt_iff₀ ht).mp h.2.1,
    (le_div_iff₀ ht).mp h.2.2.1, (div_lt_iff₀ ht).mp h.2.2.2⟩

/-- A common tail parameter below both integer s floors satisfies the two
LITERAL cutoff inequalities needed by the actual large-s residual supplier. -/
theorem smallBin_common_parameter_physical_levels
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) (k : Bin) (p : PrimeTuple)
    (hp : p ∈ sourceBin (smallCellTuples e chi m omega a N cap j) a old new N k)
    (t : ℝ) (hold : t ≤ (k.2.1 : ℝ)) (hnew : t ≤ (k.2.2 : ℝ)) :
    (p (Fin.last 3) : ℝ) ^ t ≤ (N : ℝ) ^ old / (∏ i, p i : ℕ) ∧
      (p (Fin.last 3) : ℝ) ^ t ≤ (N : ℝ) ^ new / (∏ i, p i : ℕ) := by
  have had := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hd := admitted_log_data e chi m omega N cap hN p had
  have ht := hd.2.2 (Fin.last 3)
  have hcommon := sourceBin_common_parameter _ a old new N k p hp t hold hnew
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow : ∀ lambda : ℝ, t ≤ residualS lambda N p →
      (p (Fin.last 3) : ℝ) ^ t ≤ (N : ℝ) ^ lambda / (∏ i, p i : ℕ) := by
    intro lambda hs
    have hmul : t * actualPrimeTupleLog N p (Fin.last 3) ≤
        lambda - ∑ i, actualPrimeTupleLog N p i := (le_div_iff₀ ht).mp hs
    rw [p1_fourth_quotient_rpow hN p (fun i => (hd.2.1 i).pos) lambda]
    have heq : (p (Fin.last 3) : ℝ) ^ t =
        (N : ℝ) ^ (t * actualPrimeTupleLog N p (Fin.last 3)) := by
      rw [← actualPrimeTupleLog_rpow hN p (fun i => (hd.2.1 i).pos) (Fin.last 3),
        ← Real.rpow_mul (zero_lt_one.trans hn).le]
      congr 1
      ring
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hmul
  exact ⟨hpow old hcommon.1, hpow new hcommon.2⟩

/-- Literal old/new residual difference; no continuous profile replaces it. -/
def binCorrection (S : Finset PrimeTuple) (a old new : ℝ) (N cap : ℕ) (k : Bin) : ℝ :=
  ∑ p ∈ sourceBin S a old new N k, signedTupleWeight p *
    (fourthTuplePlusResidualP1 N cap old p - fourthTuplePlusResidualP1 N cap new p)

def binSignedMass (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ) (k : Bin) : ℝ :=
  ∑ p ∈ sourceBin S a old new N k, signedTupleWeight p

theorem binSignedMass_eq_reciprocal_sum (S : Finset PrimeTuple) (a old new : ℝ)
    (N : ℕ) (k : Bin) :
    binSignedMass S a old new N k =
      ∑ p ∈ sourceBin S a old new N k, ∏ i, 1 / ((p i : ℝ) - 1) := by
  simp only [binSignedMass, signedTupleWeight_eq]

def binAbsPayment (S : Finset PrimeTuple) (a old new : ℝ) (N cap : ℕ) (k : Bin) : ℝ :=
  ∑ p ∈ sourceBin S a old new N k, |signedTupleWeight p| *
    (|fourthTuplePlusResidualP1 N cap old p| + |fourthTuplePlusResidualP1 N cap new p|)

/-- This sharper payment preserves actual old/new cancellation at the SAME cutoff. -/
def binDifferenceAbsPayment (S : Finset PrimeTuple) (a old new : ℝ)
    (N cap : ℕ) (k : Bin) : ℝ :=
  ∑ p ∈ sourceBin S a old new N k, |signedTupleWeight p| *
    |fourthTuplePlusResidualP1 N cap old p - fourthTuplePlusResidualP1 N cap new p|

theorem binCorrection_eq_old_sub_new (S : Finset PrimeTuple) (a old new : ℝ)
    (N cap : ℕ) (k : Bin) :
    binCorrection S a old new N cap k =
      (∑ p ∈ sourceBin S a old new N k,
        signedTupleWeight p * fourthTuplePlusResidualP1 N cap old p) -
      (∑ p ∈ sourceBin S a old new N k,
        signedTupleWeight p * fourthTuplePlusResidualP1 N cap new p) := by
  unfold binCorrection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

theorem abs_binCorrection_le_payment (S : Finset PrimeTuple) (a old new : ℝ)
    (N cap : ℕ) (k : Bin) :
    |binCorrection S a old new N cap k| ≤ binAbsPayment S a old new N cap k := by
  unfold binCorrection binAbsPayment
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p _hp
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [sub_zero, zero_sub, abs_neg] using
    abs_sub_le (fourthTuplePlusResidualP1 N cap old p) 0 (fourthTuplePlusResidualP1 N cap new p)

theorem abs_binCorrection_le_differencePayment (S : Finset PrimeTuple) (a old new : ℝ)
    (N cap : ℕ) (k : Bin) :
    |binCorrection S a old new N cap k| ≤ binDifferenceAbsPayment S a old new N cap k := by
  unfold binCorrection binDifferenceAbsPayment
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun p => signedTupleWeight p *
      (fourthTuplePlusResidualP1 N cap old p - fourthTuplePlusResidualP1 N cap new p))
    (sourceBin S a old new N k)

theorem binDifferencePayment_le_pairPayment (S : Finset PrimeTuple) (a old new : ℝ)
    (N cap : ℕ) (k : Bin) :
    binDifferenceAbsPayment S a old new N cap k ≤ binAbsPayment S a old new N cap k := by
  unfold binDifferenceAbsPayment binAbsPayment
  apply Finset.sum_le_sum
  intro p _hp
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [sub_zero, zero_sub, abs_neg] using
    abs_sub_le (fourthTuplePlusResidualP1 N cap old p) 0 (fourthTuplePlusResidualP1 N cap new p)

/-- The original smallCellRemainder has this exact signed reciprocal-prime source. -/
theorem smallCellRemainder_eq_signed_source
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) :
    P1OriginalFourthLimit.smallCellRemainder e chi m omega a J4 cap4 N cap j =
      ∑ p ∈ smallCellTuples e chi m omega a N cap j, signedTupleWeight p *
        (fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
          fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p) := by
  unfold P1OriginalFourthLimit.smallCellRemainder smallCellTuples
  simp only [signedTupleWeight_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have heq := exists_small_iff_last (admitted_log_data e chi m omega N cap hN p hp).1 a
  by_cases hs : actualPrimeTupleLog N p (Fin.last 3) < a <;>
    by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j <;>
    simp [heq, hs, ht]

/-- Exact finite bin sum, with all original SS/log normalization inside each residual. -/
theorem smallCellRemainder_eq_bins
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) :
    P1OriginalFourthLimit.smallCellRemainder e chi m omega a J4 cap4 N cap j =
      ∑ k ∈ sourceBins (smallCellTuples e chi m omega a N cap j)
          a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N,
        binCorrection (smallCellTuples e chi m omega a N cap j)
          a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N cap k := by
  rw [smallCellRemainder_eq_signed_source e chi m omega a J4 cap4 N cap hN j]
  exact sum_source_eq_bins _ a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N _

theorem smallCellRemainder_abs_le_binPayments
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) :
    |P1OriginalFourthLimit.smallCellRemainder e chi m omega a J4 cap4 N cap j| ≤
      ∑ k ∈ sourceBins (smallCellTuples e chi m omega a N cap j)
          a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N,
        binAbsPayment (smallCellTuples e chi m omega a N cap j)
          a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N cap k := by
  rw [smallCellRemainder_eq_bins e chi m omega a J4 cap4 N cap hN j]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun k _hk => abs_binCorrection_le_payment _ _ _ _ _ _ _)

theorem smallCellRemainder_abs_le_binDifferencePayments
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) :
    |P1OriginalFourthLimit.smallCellRemainder e chi m omega a J4 cap4 N cap j| ≤
      ∑ k ∈ sourceBins (smallCellTuples e chi m omega a N cap j)
          a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N,
        binDifferenceAbsPayment (smallCellTuples e chi m omega a N cap j)
          a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N cap k := by
  rw [smallCellRemainder_eq_bins e chi m omega a J4 cap4 N cap hN j]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun k _hk => abs_binCorrection_le_differencePayment _ _ _ _ _ _ _)

/-- The signed prime mass itself has the identical exact bin partition. -/
theorem signed_mass_eq_bins (S : Finset PrimeTuple) (a old new : ℝ) (N : ℕ) :
    (∑ p ∈ S, signedTupleWeight p) =
      ∑ k ∈ sourceBins S a old new N, binSignedMass S a old new N k := by
  exact sum_source_eq_bins S a old new N signedTupleWeight

/-- Direct total-remainder endpoint on the original selected fourth family. -/
theorem smallRemainder_eq_all_bins
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) :
    P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N cap =
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        ∑ k ∈ sourceBins (smallCellTuples e chi m omega a N cap j)
            a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N,
          binCorrection (smallCellTuples e chi m omega a N cap j)
            a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N cap k := by
  unfold P1OriginalFourthLimit.smallRemainder
  exact Finset.sum_congr rfl (fun j _hj =>
    smallCellRemainder_eq_bins e chi m omega a J4 cap4 N cap hN j)

theorem smallRemainder_abs_le_all_binPayments
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) :
    |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N cap| ≤
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        ∑ k ∈ sourceBins (smallCellTuples e chi m omega a N cap j)
            a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N,
          binAbsPayment (smallCellTuples e chi m omega a N cap j)
            a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N cap k := by
  unfold P1OriginalFourthLimit.smallRemainder
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun j _hj =>
    smallCellRemainder_abs_le_binPayments e chi m omega a J4 cap4 N cap hN j)

theorem smallRemainder_abs_le_all_binDifferencePayments
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) :
    |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N cap| ≤
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        ∑ k ∈ sourceBins (smallCellTuples e chi m omega a N cap j)
            a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N,
          binDifferenceAbsPayment (smallCellTuples e chi m omega a N cap j)
            a (thirdCellExponent e m j : ℝ) (cap4 j : ℝ) N cap k := by
  unfold P1OriginalFourthLimit.smallRemainder
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun j _hj =>
    smallCellRemainder_abs_le_binDifferencePayments e chi m omega a J4 cap4 N cap hN j)

end P1OriginalFourthSmallPrimeStratification

end

end ImbalancedChen
