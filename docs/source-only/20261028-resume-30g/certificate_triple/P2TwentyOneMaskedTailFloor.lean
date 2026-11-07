import ImbalancedChen.P2TwentyOneUnsiftedArithmeticSource

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original high-arity quotient carrier is Sifted(d*N), which exempts
divisors of d*N. It is not absolute roughness. A low tail prime is either
an old d divisor or equals the additive-prime partner. Thus, after keeping
the real small-partner remainder, the independent good source has a true
prime-factor floor. No arithmetic error is erased or declared negligible.
-/
namespace ImbalancedChen.P2TwentyOneMaskedTailFloor
noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2TwentyOneUnsiftedArithmeticSource

def GoodTail (z : ℕ) (x : Label) : Prop := ∀ p : ℕ,p.Prime → p ∣ x.2 → z≤p

def goodLabels (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) (z : ℕ) : Finset Label :=
  (arithmeticLabels N d M a b c e f cs).filter (GoodTail z)

/-- Independent larger costing source: the old Sifted(d*N) predicate
is dropped by positivity. Its tail restrictions are only a true prime
floor, positive n and the original complete product bound. -/
def absoluteGoodLabels (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) (z : ℕ) : Finset Label :=
  ((words M a b c e f cs).product (Finset.range (N+1))).filter
    (fun x => 0<x.2 ∧ GoodTail z x ∧ product d x<N)

theorem good_subset_absolute {N d M z : ℕ} {a b c e f : ℝ} {cs : List ℕ} :
    goodLabels N d M a b c e f cs z ⊆ absoluteGoodLabels N d M a b c e f cs z := by
  intro x hx
  obtain ⟨hs,hg⟩ := Finset.mem_filter.mp hx
  obtain ⟨ha,hgeo⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨ha,hgeo.1,hg,hgeo.2.2⟩

theorem good_primeMass_le_absolute {N d M z : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (sigma : ℝ) (hsigma : 0≤sigma) :
    p5z_labelledPrimeMass (goodLabels N d M a b c e f cs z) (product d)
      (fun _ => sigma) N ≤
    p5z_labelledPrimeMass (absoluteGoodLabels N d M a b c e f cs z) (product d)
      (fun _ => sigma) N := by
  unfold p5z_labelledPrimeMass
  apply Finset.sum_le_sum_of_subset_of_nonneg good_subset_absolute
  intro x hx hnot
  split_ifs
  · exact hsigma
  · exact le_rfl

theorem threshold_window_lower {M : ℕ} {a b c e f : ℝ} {cs l : List ℕ}
    (hl : l ∈ words M a b c e f cs) (hlen : 2≤cs.length) : a≤threshold l := by
  have ht := (secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hl).1
  have hk : l.length-2<l.length := by omega
  have hm : l.getD (l.length-2) 0 ∈ primeWindow M a f := by
    rw [List.getD_eq_getElem _ _ hk]
    exact ht.2.2 _ (List.getElem_mem hk)
  exact (mem_primeWindow.mp hm).2.2.1

/-- Low prime factors cannot simply be deleted from a masked quotient.
The additive-prime exception is identified with its exact integer value. -/
theorem tail_prime_alternatives {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    {x : Label} (hx : x ∈ arithmeticLabels N d M a b c e f cs)
    (hell : Nat.Prime (N-product d x)) {p : ℕ} (hp : p.Prime) (hpn : p ∣ x.2) :
    threshold x.1≤(p : ℝ) ∨ p ∣ d ∨ p=N-product d x := by
  have hs := (Finset.mem_filter.mp hx).2.2.1
  by_cases hge : threshold x.1≤(p : ℝ)
  · exact Or.inl hge
  have hlt : (p : ℝ)<threshold x.1 := lt_of_not_ge hge
  have hmask : p ∣ d*N := by
    by_contra hnot
    exact hs p hp (hp.coprime_iff_not_dvd.mpr hnot) hlt hpn
  rcases hp.dvd_mul.mp hmask with hpd | hpN
  · exact Or.inr (Or.inl hpd)
  · have hpm : p ∣ product d x := dvd_mul_of_dvd_right hpn (d*x.1.prod)
    have hpell : p ∣ N-product d x := Nat.dvd_sub' hpN hpm
    exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hell).mp hpell))

theorem large_partner_goodTail {N d M z : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    {x : Label} (hx : x ∈ arithmeticLabels N d M a b c e f cs)
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p)
    (hcut : (z : ℝ)≤threshold x.1) (hell : Nat.Prime (N-product d x))
    (hlarge : z≤N-product d x) : GoodTail z x := by
  intro p hp hpn
  rcases tail_prime_alternatives hx hell hp hpn with hcutp | hpd | hpartner
  · exact_mod_cast hcut.trans hcutp
  · exact hold p hp hpd
  · simpa only [hpartner] using hlarge

/-- An actual positive count is bounded by a genuinely independent
tail-floor source plus its ORIGINAL small additive-prime remainder.
No primality test is put into goodLabels or its constant source weight. -/
theorem primeMass_le_good_add_small {N d M z : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p)
    (hcut : ∀ x ∈ arithmeticLabels N d M a b c e f cs,(z : ℝ)≤threshold x.1)
    (sigma : ℝ) (hsigma : 0≤sigma) :
    p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N ≤
    p5z_labelledPrimeMass (goodLabels N d M a b c e f cs z) (product d)
      (fun _ => sigma) N +
    p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N z := by
  unfold p5z_labelledPrimeMass p5z_labelledSmallPrimeMass goodLabels
  rw [Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hmain : product d x<N ∧ Nat.Prime (N-product d x)
  · by_cases hg : GoodTail z x
    · by_cases hz : N-product d x<z
      · simp only [if_pos hmain,if_pos hg,if_pos ⟨hmain.1,hmain.2,hz⟩]
        linarith only [hsigma]
      · simp only [if_pos hmain,if_pos hg,
          if_neg (show ¬(product d x<N ∧ Nat.Prime (N-product d x) ∧ N-product d x<z)
            from fun h => hz h.2.2),add_zero,le_refl]
    · have hz : N-product d x<z := by
        by_contra hn
        exact hg (large_partner_goodTail hx hold (hcut x hx) hmain.2 (Nat.le_of_not_gt hn))
      simp only [if_pos hmain,if_neg hg,if_pos ⟨hmain.1,hmain.2,hz⟩,zero_add,le_refl]
  · have hn : ¬(product d x<N ∧ Nat.Prime (N-product d x) ∧ N-product d x<z) :=
      fun h => hmain ⟨h.1,h.2.1⟩
    simp only [if_neg hmain,if_neg hn,add_zero,ite_self,le_refl]

/-- The tail cutoff premise is discharged by the REAL original window
and actual prefix arity, not supplied as an arbitrary source licence. -/
theorem prefix_primeMass_le_good_add_small {N d M z : ℕ} {a b c e f : ℝ}
    {cs : List ℕ} (hlen : 2≤cs.length) (hza : (z : ℝ)≤a)
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p) (sigma : ℝ) (hsigma : 0≤sigma) :
    p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N ≤
    p5z_labelledPrimeMass (goodLabels N d M a b c e f cs z) (product d)
      (fun _ => sigma) N +
    p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N z := by
  apply primeMass_le_good_add_small hold _ sigma hsigma
  intro x hx
  have hw := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  exact hza.trans (threshold_window_lower hw hlen)

theorem prefix_primeMass_le_absolute_add_small {N d M z : ℕ} {a b c e f : ℝ}
    {cs : List ℕ} (hlen : 2≤cs.length) (hza : (z : ℝ)≤a)
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p) (sigma : ℝ) (hsigma : 0≤sigma) :
    p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N ≤
    p5z_labelledPrimeMass (absoluteGoodLabels N d M a b c e f cs z) (product d)
      (fun _ => sigma) N +
    p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N z :=
  (prefix_primeMass_le_good_add_small hlen hza hold sigma hsigma).trans
    (add_le_add_right (good_primeMass_le_absolute sigma hsigma) _)

/-- Complete prime word for any original high-arity prefix. No three-slot
restriction, squarefree truncation, tail-prime ordering change or unit
deletion occurs. The canonical old d factors remain in the word. -/
def completeWord (d : ℕ) (x : Label) : List ℕ :=
  d.primeFactorsList++x.1++x.2.primeFactorsList

theorem completeWord_product {N d : ℕ} {x : Label} (hd : 0<d) (hx : Geometry N d x) :
    (completeWord d x).prod=product d x := by
  simp only [completeWord,List.prod_append,Nat.prod_primeFactorsList hd.ne',
    Nat.prod_primeFactorsList hx.1.ne',product]

theorem completeWord_primes {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    {x : Label} (hx : x ∈ arithmeticLabels N d M a b c e f cs) :
    ∀ p ∈ completeWord d x,p.Prime := by
  have hw := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  have hl := ((secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hw).1).2.2
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactorsList hp
    · exact (mem_primeWindow.mp (hl p hp)).1
  · exact Nat.prime_of_mem_primeFactorsList hp

/-- The independent good source has a full prime-factor floor when the
old d and original window floors are supplied. Masked-tail arithmetic
does not justify omitting either of these genuine source conditions. -/
theorem completeWord_floor {N d M z : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    {x : Label} (hx : x ∈ goodLabels N d M a b c e f cs z)
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p) (ha : (z : ℝ)≤a) :
    ∀ p ∈ completeWord d x,z≤p := by
  obtain ⟨hsource,hgood⟩ := Finset.mem_filter.mp hx
  have hw := (Finset.mem_product.mp (Finset.mem_filter.mp hsource).1).1
  have hl := ((secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hw).1).2.2
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hold p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
    · have hg := (mem_primeWindow.mp (hl p hp)).2.2.1
      exact_mod_cast ha.trans hg
  · exact hgood p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)

theorem absoluteGood_completeWord_floor {N d M z : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    {x : Label} (hx : x ∈ absoluteGoodLabels N d M a b c e f cs z)
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p) (ha : (z : ℝ)≤a) :
    ∀ p ∈ completeWord d x,z≤p := by
  obtain ⟨hamb,hpos,hgood,hprod⟩ := Finset.mem_filter.mp hx
  have hw := (Finset.mem_product.mp hamb).1
  have hl := ((secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hw).1).2.2
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hold p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
    · have hg := (mem_primeWindow.mp (hl p hp)).2.2.1
      exact_mod_cast ha.trans hg
  · exact hgood p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)

theorem absoluteGood_completeWord_data {N d M z : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    {x : Label} (hd : 0<d) (hx : x ∈ absoluteGoodLabels N d M a b c e f cs z)
    (hold : ∀ p : ℕ,p.Prime → p ∣ d → z≤p) (ha : (z : ℝ)≤a) :
    (completeWord d x).prod=product d x ∧
      ∀ p ∈ completeWord d x,p.Prime ∧ z≤p := by
  obtain ⟨hamb,hpos,hgood,hprod⟩ := Finset.mem_filter.mp hx
  have hw := (Finset.mem_product.mp hamb).1
  have hl := ((secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hw).1).2.2
  refine ⟨?_,?_⟩
  · simp only [completeWord,List.prod_append,Nat.prod_primeFactorsList hd.ne',
      Nat.prod_primeFactorsList hpos.ne',product]
  · intro p hp
    refine ⟨?_,absoluteGood_completeWord_floor hx hold ha p hp⟩
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactorsList hp
      · exact (mem_primeWindow.mp (hl p hp)).1
    · exact Nat.prime_of_mem_primeFactorsList hp

end
end ImbalancedChen.P2TwentyOneMaskedTailFloor
