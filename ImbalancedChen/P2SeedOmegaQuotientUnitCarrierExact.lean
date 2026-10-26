import ImbalancedChen.P2EnhancedPrefixMaskDefect
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitPrimeOutput

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact finite carrier equality for the Gamma20/21 quotient-one branch.
The enhanced same-Q comparison uses quotientCarrier with old mask d*N;
the pinned unit count receiver uses the original exempt-prefix carrier.
For positive marks and the actual last two ordered primes, their UNIT
carriers agree exactly. This is not an asymptotic or weighted-sum wrapper.
Since the natural receiver ell is identical, any retained mark-history,
full-square, selected-square or physical predicate can be applied to this
same carrier without changing its truth value. No sorted merge is used.
-/

namespace ImbalancedChen.P2SeedOmegaQuotientUnitCarrierExact
noncomputable section
open Finset Wu2008DoubleSieve Classical
open P2EnhancedPrefixMaskDefect

/-- The actual quotient-one part of the unchanged enhanced quotient carrier. -/
def quotientUnitCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  (quotientCarrier N d l).filter (fun ell => N-ell=d*l.prod)

theorem specified_product_pos {d p q : ℕ} {pre : List ℕ}
    (hd : 0<d) (hpre : 0<pre.prod) (hp : p.Prime) (hq : q.Prime) :
    0<d*(pre++[p,q]).prod := by
  simp only [List.prod_append,List.prod_cons,List.prod_nil,mul_one]
  exact mul_pos hd (mul_pos hpre (mul_pos hp.pos hq.pos))

/-- Removing the exempt-prefix mask loses NO unit atom. All specified
prime labels and the original next-to-last cutoff are identical. -/
theorem quotientUnit_eq_originalUnit {N d p q : ℕ} (pre : List ℕ)
    (hd : 0<d) (hpre : 0<pre.prod) (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) :
    quotientUnitCarrier N d (pre++[p,q])=
      secondFunctionalFourPrimeUnitCarrier N d (pre++[p,q]) := by
  have hprod := specified_product_pos hd hpre hp hq
  ext ell
  rw [quotientUnitCarrier,mem_filter,HighUnitPrimeOutput.unit_mem_iff pre hp hq hpq]
  constructor
  · rintro ⟨hcarrier,heq⟩
    change ell ∈ (range (N+1)).filter (fun ell =>
      ell.Prime ∧ d*(pre++[p,q]).prod ∣ N-ell ∧
        Sifted (d*N) ((N-ell)/(d*(pre++[p,q]).prod))
          ((pre++[p,q]).getD ((pre++[p,q]).length-2) 0)) at hcarrier
    have hm := mem_filter.mp hcarrier
    have hle : ell≤N := by have hlt := mem_range.mp hm.1; omega
    exact ⟨hm.2.1,by omega⟩
  · rintro ⟨hell,hsum⟩
    have heq : N-ell=d*(pre++[p,q]).prod := by omega
    refine ⟨?_,heq⟩
    change ell ∈ (range (N+1)).filter (fun ell =>
      ell.Prime ∧ d*(pre++[p,q]).prod ∣ N-ell ∧
        Sifted (d*N) ((N-ell)/(d*(pre++[p,q]).prod))
          ((pre++[p,q]).getD ((pre++[p,q]).length-2) 0))
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega),hell,?_,?_⟩
    · simpa only [heq] using (dvd_rfl : d*(pre++[p,q]).prod ∣ d*(pre++[p,q]).prod)
    · rw [heq,Nat.div_self (Nat.ne_of_gt hprod)]
      intro r hr _ _ hrd
      exact hr.not_dvd_one hrd

/-- Actual finite unit output is the same singleton-or-empty prime test;
there is no cutoff enlargement and no lost or newly charged unit term. -/
theorem quotientUnit_card {N d p q : ℕ} (pre : List ℕ)
    (hd : 0<d) (hpre : 0<pre.prod) (hp : p.Prime) (hq : q.Prime) (hpq : p≤q) :
    (quotientUnitCarrier N d (pre++[p,q])).card=
      if (N-d*(pre++[p,q]).prod).Prime then 1 else 0 := by
  rw [quotientUnit_eq_originalUnit pre hd hpre hp hq hpq]
  exact HighUnitPrimeOutput.unit_card pre hp hq hpq

/-- The selected-square defect cost is disjoint from this EXACT unit
carrier, before averaging and before any density estimate. -/
theorem quotientUnit_disjoint_collision {N d p q : ℕ} (pre : List ℕ)
    (hd : 0<d) (hpre : 0<pre.prod) (hp : p.Prime) (hq : q.Prime) :
    Disjoint (quotientUnitCarrier N d (pre++[p,q]))
      (collisionCarrier N d (pre++[p,q])) := by
  apply Finset.disjoint_left.mpr
  intro ell hu hc
  have heq := (mem_filter.mp hu).2
  apply collision_quotient_ne_one hc
  rw [heq,Nat.div_self (Nat.ne_of_gt (specified_product_pos hd hpre hp hq))]

end
end ImbalancedChen.P2SeedOmegaQuotientUnitCarrierExact
