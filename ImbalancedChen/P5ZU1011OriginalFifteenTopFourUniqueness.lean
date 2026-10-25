import ImbalancedChen.P5ZU1011OriginalFifteenModulusConvolution
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.Squarefree.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The active native physical modulus determines its ACTUAL ordered four-prime
prefix and its residual divisor uniquely. Native residual prime factors are
strictly below their OWN cell's cutoff Z<=p1. The cutoffs may vary between
cells: no common small/rough threshold is assumed. Prime factorization and
the decreasing top-four order recover the original tuple first; division
then recovers d. The dispatcher already fixes one policy/owner for that
tuple. Thus the literal sigma fibre has at most one mark, and its unit bound
is derived from the actual Rosser coefficient rather than supplied.

Squarefreeness and deleted-target coprimality are also genuine arithmetic
conclusions. H248 density meaning, PP/physical distribution licenses and
the original analytic mean remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenTopFourUniqueness

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells U1011OriginalFifteenNativeGridDispatch
open U1011OriginalFifteenModulusConvolution P5U1011JointOverlap

/-- An ordered initial block is determined by a permutation of the full
list when every tail entry is smaller than every initial entry. Tail order
is irrelevant; this lemma does not assume common factor-size cutoffs. -/
private theorem ordered_prefix_unique : ∀ ps qs rs ss : List ℕ,
    ps.Pairwise (· ≥ ·) → qs.Pairwise (· ≥ ·) → ps.length = qs.length →
    (∀ r ∈ rs, ∀ p ∈ ps, r < p) → (∀ s ∈ ss, ∀ q ∈ qs, s < q) →
    (ps ++ rs).Perm (qs ++ ss) → ps = qs := by
  intro ps
  induction ps with
  | nil =>
    intro qs rs ss hps hqs hlen hrs hss hperm
    have hq : qs = [] := List.length_eq_zero.mp hlen.symm
    exact hq.symm
  | cons p ps ih =>
    intro qs rs ss hps hqs hlen hrs hss hperm
    cases qs with
    | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
    | cons q qs =>
      have hp := List.pairwise_cons.mp hps
      have hq := List.pairwise_cons.mp hqs
      have hpmem : p ∈ (q :: qs) ++ ss := hperm.mem_iff.mp (by simp)
      have hqmem : q ∈ (p :: ps) ++ rs := hperm.mem_iff.mpr (by simp)
      have hpq : p ≤ q := by
        rcases List.mem_append.mp hpmem with hh | hh
        · rcases List.mem_cons.mp hh with hh | hh
          · exact le_of_eq hh
          · exact hq.1 p hh
        · exact (hss p hh q (by simp)).le
      have hqp : q ≤ p := by
        rcases List.mem_append.mp hqmem with hh | hh
        · rcases List.mem_cons.mp hh with hh | hh
          · exact le_of_eq hh
          · exact hp.1 q hh
        · exact (hrs q hh p (by simp)).le
      have heq : p = q := le_antisymm hpq hqp
      subst q
      have htail : (ps ++ rs).Perm (qs ++ ss) := hperm.cons_inv
      have hlen' : ps.length = qs.length := Nat.succ.inj hlen
      have hprefix := ih qs rs ss hp.2 hq.2 hlen'
        (fun r hr a ha => hrs r hr a (List.mem_cons_of_mem p ha))
        (fun s hs a ha => hss s hs a (List.mem_cons_of_mem p ha)) htail
      exact congrArg (List.cons p) hprefix

def prefix (t : Four) : List ℕ := [t.2.2,t.2.1,t.1.2,t.1.1]

theorem prefix_prod (t : Four) : (prefix t).prod = fullPrefix t := by
  simp [prefix,fullPrefix,slots,Fin.prod_univ_succ]

theorem prefix_injective : Function.Injective prefix := by
  intro t s heq
  have h : t.2.2 = s.2.2 ∧ t.2.1 = s.2.1 ∧ t.1.2 = s.1.2 ∧ t.1.1 = s.1.1 := by
    simpa only [prefix,List.cons.injEq,and_true] using heq
  exact Prod.ext (Prod.ext h.2.2.2 h.2.2.1) (Prod.ext h.2.1 h.1)

private theorem prefix_data {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) :
    (prefix t).Pairwise (· ≥ ·) ∧ (∀ p ∈ prefix t, Nat.Prime p) ∧
      ∀ p ∈ prefix t, t.1.1 ≤ p := by
  obtain ⟨h1,h2,h3,h4,h12,h23,h34⟩ := joint_carrier_order ht
  refine ⟨?_,?_,?_⟩
  · simp [prefix,List.pairwise_cons] <;> omega
  · intro p hp
    simp only [prefix,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (mem_chenAdditivePrimeCarrier.mp h4).2.1
    · exact (mem_chenAdditivePrimeCarrier.mp h3).2.1
    · exact (mem_chenAdditivePrimeCarrier.mp h2).2.1
    · exact (mem_chenAdditivePrimeCarrier.mp h1).2.1
  · intro p hp
    simp only [prefix,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> omega

/-- Native support actually puts every residual prime strictly below
every one of the same tuple's four prefix primes. -/
theorem mark_top_four_data {n N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {m : Mark}
    (hm : m ∈ marks n N E) :
    (prefix m.1).Pairwise (· ≥ ·) ∧ (∀ p ∈ prefix m.1, Nat.Prime p) ∧
      m.2 ≠ 0 ∧ ∀ r ∈ m.2.primeFactorsList, ∀ p ∈ prefix m.1, r < p := by
  obtain ⟨i,hi,ht,hd,_,_⟩ := mark_cell_data hN hm
  have hcell := (Finset.mem_filter.mp ht).1
  obtain ⟨hsource,hgeom⟩ := Finset.mem_filter.mp hcell
  have hjoint := originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) hsource
  have hpref := prefix_data hjoint
  have hleg := U1011OriginalFifteenFixedCellNative.native_legality hN hsource
    (policy i) (policy_lt_fifteen i) (gridBox n i.2) (gridBox_valid n i.2)
    (gridBox_lower_positive n i.2 3) ((mem_activeCells i).mp hi) (cell_subset_closed_box n i.2 hgeom)
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hd
  refine ⟨hpref.1,hpref.2.1,hsmall.1,?_⟩
  intro r hr p hp
  have hrprime := Nat.prime_of_mem_primeFactorsList hr
  have hrmem : r ∈ m.2.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hrprime,Nat.dvd_of_mem_primeFactorsList hr,hsmall.1⟩
  have hrsmall := hsmall.2 r hrmem
  have hlast : m.1.1.1 ≤ p := hpref.2.2 p hp
  have hlastR : (m.1.1.1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlast
  have hrR : (r : ℝ) < (p : ℝ) := (hrsmall.trans_le hleg.2.2.1).trans_le hlastR
  exact_mod_cast hrR

/-- Physical full-modulus injectivity is PROVED on actual active native
marks. Four ordered prefix primes, even across differing native cells,
are recovered before the residual quotient and action can be recovered. -/
theorem modulus_injective_on_marks {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    Set.InjOn modulus (marks n N E : Set Mark) := by
  intro m hm k hk hmod
  have hmd := mark_top_four_data hN hm
  have hkd := mark_top_four_data hN hk
  have hprimeM : ∀ p ∈ prefix m.1 ++ m.2.primeFactorsList, Nat.Prime p := by
    intro p hp
    exact (List.mem_append.mp hp).elim (hmd.2.1 p) (fun h => Nat.prime_of_mem_primeFactorsList h)
  have hprimeK : ∀ p ∈ prefix k.1 ++ k.2.primeFactorsList, Nat.Prime p := by
    intro p hp
    exact (List.mem_append.mp hp).elim (hkd.2.1 p) (fun h => Nat.prime_of_mem_primeFactorsList h)
  have hprod : (prefix m.1 ++ m.2.primeFactorsList).prod =
      (prefix k.1 ++ k.2.primeFactorsList).prod := by
    rw [List.prod_append,List.prod_append,prefix_prod,prefix_prod,
      Nat.prod_primeFactorsList hmd.2.2.1,Nat.prod_primeFactorsList hkd.2.2.1]
    exact hmod
  have hperm := (Nat.primeFactorsList_unique hprod hprimeM).trans
    (Nat.primeFactorsList_unique (rfl : (prefix k.1 ++ k.2.primeFactorsList).prod =
      (prefix k.1 ++ k.2.primeFactorsList).prod) hprimeK).symm
  have hpref := ordered_prefix_unique (prefix m.1) (prefix k.1) m.2.primeFactorsList k.2.primeFactorsList
    hmd.1 hkd.1 (by simp [prefix]) hmd.2.2.2 hkd.2.2.2 hperm
  have htuple : m.1 = k.1 := prefix_injective hpref
  have hmpos := (mark_modulus_positive_coprime hN hm).1
  have hbpos : 0 < fullPrefix m.1 := Nat.pos_of_mul_pos_right hmpos
  have hmod' : fullPrefix m.1 * m.2 = fullPrefix k.1 * k.2 := hmod
  rw [← htuple] at hmod'
  have hd : m.2 = k.2 := Nat.eq_of_mul_eq_mul_left hbpos hmod'
  exact Sigma.ext htuple (heq_of_eq hd)

theorem unique_mark_of_modulus {n N q : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop}
    (hq : q ∈ modulusSupport n N E) : ∃! m : Mark, m ∈ marks n N E ∧ modulus m = q := by
  obtain ⟨m,hm,hq⟩ := Finset.mem_image.mp hq
  refine ⟨m,⟨hm,hq⟩,?_⟩
  intro k hk
  exact modulus_injective_on_marks hN E hk.1 hm (hk.2.trans hq.symm)

theorem fibre_card_le_one {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) (q : ℕ) :
    (fibre n N E q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro m hm k hk
  have hm' := Finset.mem_filter.mp hm
  have hk' := Finset.mem_filter.mp hk
  exact modulus_injective_on_marks hN E hm'.1 hk'.1 (hm'.2.trans hk'.2.symm)

/-- The literal convolution has unit amplitude because its physical
fibre has at most one native mark, not by an assumed aggregate bound. -/
theorem sigma_abs_le_one {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) (q : ℕ) :
    |sigma n N E q| ≤ 1 :=
  (sigma_abs_le_fibre_card hN E q).trans (by exact_mod_cast fibre_card_le_one hN E q)

theorem fullPrefix_squarefree {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : Squarefree (fullPrefix t) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (slots_prime ht i) (slots_prime ht j)).mpr
      (fun h => hij ((slots_strictAnti ht).injective h))
  · intro i hi
    exact (slots_prime ht i).squarefree

theorem mark_modulus_squarefree {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {m : Mark} (hm : m ∈ marks n N E) : Squarefree (modulus m) := by
  obtain ⟨i,hi,ht,hd,_,_⟩ := mark_cell_data hN hm
  have hcell := (Finset.mem_filter.mp ht).1
  obtain ⟨hsource,hgeom⟩ := Finset.mem_filter.mp hcell
  have hjoint := originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) hsource
  have hleg := U1011OriginalFifteenFixedCellNative.native_legality hN hsource
    (policy i) (policy_lt_fifteen i) (gridBox n i.2) (gridBox_valid n i.2)
    (gridBox_lower_positive n i.2 3) ((mem_activeCells i).mp hi) (cell_subset_closed_box n i.2 hgeom)
  have hZ : U1011OriginalFifteenFixedCellNative.Z (policy i) (gridBox n i.2) N ≤ (slots m.1 3 : ℝ) := by
    simpa only [slots,Matrix.cons_val_three] using hleg.2.2.1
  have hdvd : m.2 ∣ sieveProduct N (Nat.ceil (U1011OriginalFifteenFixedCellNative.Z (policy i) (gridBox n i.2) N)) := by
    have h := (Nat.mem_divisors.mp hd).1
    rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N _ _ (Nat.le_ceil _)] at h
  have hcop := chenQuotient_allowed_coprime (fullPrefix_coprime_lowered_sieve hjoint hZ) hdvd
  exact (Nat.squarefree_mul hcop).mpr ⟨fullPrefix_squarefree hjoint,actualSmallRosserSupport_squarefree _ _ _ hd⟩

theorem sigma_nonzero_arithmetic_data {n N q : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} (hq : sigma n N E q ≠ 0) :
    0 < q ∧ Squarefree q ∧ Nat.Coprime q N ∧ |sigma n N E q| ≤ 1 := by
  have hmem : q ∈ modulusSupport n N E := by
    by_contra hn
    exact hq (sigma_zero_off_support hn)
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hmem
  have hdata := mark_modulus_positive_coprime hN hm
  exact ⟨hdata.1,mark_modulus_squarefree hN hm,hdata.2,sigma_abs_le_one hN E _⟩

end
end ImbalancedChen.P5Z.U1011OriginalFifteenTopFourUniqueness
