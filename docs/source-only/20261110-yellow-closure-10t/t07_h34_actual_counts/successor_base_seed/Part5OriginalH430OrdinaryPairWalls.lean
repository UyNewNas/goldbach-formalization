import ImbalancedChen.Part5OriginalH430StrictSeedCeiling
import ImbalancedChen.Part5OriginalH430W2UpperPolygons
import ImbalancedChen.P2OriginalW2CountTupleReindex
import ImbalancedChen.P2OriginalPositiveSameQMassLift

/-! At the frozen root Q each normalized exponent of an actual prime is
irrational. Hence all the rational constant lower walls in the four mother
windows are empty in the prime sum; the strict affine square test persists. -/
namespace ImbalancedChen.Part5OriginalH430OrdinaryPairWalls
noncomputable section
open Real Finset Set
open P5OriginalActionMassBound P2OriginalHalfOpenProfileCarrier
open P2OriginalW2CountTupleReindex P2OriginalPositiveSameQMassLift
open P2OriginalChildPhysicalNormalization (thetaAtom)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430StrictSeedCeiling Part5OriginalH430W2UpperPolygons
open scoped Classical BigOperators

theorem prime_coordinate_ne_rat {N n p d m : ℕ} {k : Root} {t L : ℝ}
    (hN : 1<N) (hL : 0<L) (hQ : rootQ N n k t p=(d:ℝ)*(N:ℝ)^L)
    (x : Fin m → ℕ) (hx : ∀ i, (x i).Prime ∧ ¬x i ∣ N) (i : Fin m) (r : ℚ) :
    normalizedLog N L x i ≠ (r:ℝ) := by
  intro he
  have hp := (hx i).1
  have hpow := normalizedLog_rpow hN hL x (fun i => (hx i).1.pos) i
  have hrpos : (0:ℝ)<r := by
    by_contra! hr
    rw [he] at hpow
    have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
    have hle := rpow_le_one_of_one_le_of_nonpos hNr (mul_nonpos_of_nonneg_of_nonpos hL.le hr)
    rw [hpow] at hle
    exact (not_le_of_gt (by exact_mod_cast hp.one_lt : (1:ℝ)<x i)) hle
  have hr : (0:ℚ)<r := by exact_mod_cast hrpos
  have hnum : 0<r.num := Rat.num_pos.mpr hr
  have hn : (r.num.toNat:ℝ)=(r.num:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hrat : (r:ℝ)=(r.num.toNat:ℝ)/r.den := by
    simp only [Rat.cast_def,Int.cast_natCast,hn]
  have hden : (r.den:ℝ)≠0 := by exact_mod_cast r.den_nz
  have he' : normalizedLog N L x i*(r.den:ℝ)=(r.num.toNat:ℝ) := by
    rw [he,hrat,div_mul_cancel₀ _ hden]
  have heq : ((N:ℝ)^L)^r.num.toNat = (x i:ℝ)^r.den := by
    calc
      _ = (N:ℝ)^(L*(r.num.toNat:ℝ)) := by
        rw [rpow_mul (Nat.cast_nonneg N),rpow_natCast]
      _ = (N:ℝ)^((L*normalizedLog N L x i)*(r.den:ℝ)) := by rw [mul_assoc,he']
      _ = _ := by rw [rpow_mul (Nat.cast_nonneg N),rpow_natCast,hpow]
  have hm : rootQ N n k t p ^ r.num.toNat = ((d^r.num.toNat*(x i)^r.den : ℕ):ℝ) := by
    rw [hQ,mul_pow,heq,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow]
  have hdiv : x i ∣ (x i)^r.den := by
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero r.den_nz
    rw [ha,pow_succ]
    exact dvd_mul_left _ _
  exact root_power_ne_coprime_multiple n r.num.toNat k t hp
    (hp.coprime_iff_not_dvd.mpr (hx i).2) (dvd_mul_of_dvd_right hdiv _) hm

theorem actual_half_iff_open {N n p d : ℕ} {root : Root} {t L : ℝ}
    (hN : 1<N) (hL : 0<L) (hQ : rootQ N n root t p=(d:ℝ)*(N:ℝ)^L)
    (j : Fin 36) (k : Fin 4) (x : Fin 2 → ℕ)
    (hx : ∀ i, (x i).Prime ∧ ¬ x i ∣ N) :
    normalizedLog N L x ∈ pairHalf (originalW2At j) k ↔
      normalizedLog N L x ∈ W2PairDomain (originalW2At j) k := by
  have hw (i : Fin 2) (q : Fin 5) :
      normalizedLog N L x i ≠ (1/(parameterQ j q:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_one] using
      prime_coordinate_ne_rat hN hL hQ x hx i (1/parameterQ j q)
  have hh : normalizedLog N L x ∉ pairLowerWall (originalW2At j) k := by
    rw [← original_parameters j]
    fin_cases k
    · exact hw 0 1
    · exact fun h => h.elim (hw 0 1) (hw 1 3)
    · exact hw 0 1
    · exact fun h => h.elim (hw 0 1) (hw 1 2)
  rw [pairHalf_partition]
  simp only [hh,and_false,or_false]

def ordinaryPairWindow (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4) : ℝ :=
  windowOccurrence N Q L d (originalW2At j) k (fun a b => thetaAtom N Q (d*a*b))

theorem ordinaryPairWindow_eq_children {N n p d : ℕ} {root : Root} {t L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hQ : rootQ N n root t p=(d:ℝ)*(N:ℝ)^L)
    (j : Fin 36) (k : Fin 4) :
    ordinaryPairWindow N (rootQ N n root t p) L d j k =
      pairChildTheta N (rootQ N n root t p) L d (originalW2At j) k := by
  unfold ordinaryPairWindow pairChildTheta
  rw [all_four_window_occurrences_reindex hN hd hL hQ
    (originalRepairedW2Bank_geometry _ (originalW2At_mem j))]
  apply sum_congr rfl
  intro x hx
  have hh := actual_half_iff_open hN hL hQ j k x (fun i =>
    ⟨(mem_actualPrimeBoxTuples_iff.mp hx i).1,(mem_actualPrimeBoxTuples_iff.mp hx i).2.1⟩)
  change (if normalizedLog N L x ∈ pairHalf (originalW2At j) k then _ else 0) =
    (if normalizedLog N L x ∈ W2PairDomain (originalW2At j) k then _ else 0)
  rw [hh]

end
end ImbalancedChen.Part5OriginalH430OrdinaryPairWalls
