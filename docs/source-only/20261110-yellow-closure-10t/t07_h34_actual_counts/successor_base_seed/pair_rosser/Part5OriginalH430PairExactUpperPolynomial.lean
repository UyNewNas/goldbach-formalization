import ImbalancedChen.Part5OriginalH430SeedChildRosserDictionary
import ImbalancedChen.ActualRosserCubeReduction

/-! The actual upper sieve polynomial is unchanged between its physical
cutoff and its first-cube cutoff on the original ordered pair. This holds
coefficientwise and for every signed test of the physical modulus. -/
namespace ImbalancedChen.Part5OriginalH430PairExactUpperPolynomial
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2ActualMarkedCountState (rootLevel)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SeedChildRosserDictionary (true_child_ceil)
open Part5OriginalH430SameQCanonicalMains (model)
open scoped Classical BigOperators

private theorem prime_product {M cap : ℕ} {z : ℝ} (hc : z≤(cap:ℝ)) :
    actualSmallPrimeProduct M cap z=ordinarySievePrimeProduct M z := by
  have hs : actualSmallPrimeFinset M cap z=primeWindow M 0 z := by
    ext q
    rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hc,mem_primeWindow]
    constructor
    · rintro ⟨hp,hn,hz⟩
      exact ⟨hp,hp.coprime_iff_not_dvd.mpr hn,Nat.cast_nonneg _,hz⟩
    · rintro ⟨hp,hn,_,hz⟩
      exact ⟨hp,hp.coprime_iff_not_dvd.mp hn,hz⟩
  unfold actualSmallPrimeProduct ordinarySievePrimeProduct
  rw [hs] <;> rfl

def weightedUpper (N : ℕ) (Q : ℝ) (b : ℕ) (z : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ e∈(ordinarySievePrimeProduct (b*N) z).divisors,ordinaryRosserWeight true N b (rootLevel Q b) z e*f e

private theorem plus_eq {N cap b : ℕ} {Q z : ℝ} (hc : z≤(cap:ℝ))
    (hlev : ⌈Q/(b:ℝ)⌉₊=rootLevel Q b) :
    actualSmallRosserPlus (b*N) cap z (Q/(b:ℝ)) =
      ordinaryRosserWeight true N b (rootLevel Q b) z := by
  unfold actualSmallRosserPlus ActualSmallRosserProvider.upperWeight ordinaryRosserWeight
  rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_eq_producer,prime_product hc,hlev] <;> rfl

theorem upper_polynomial_exact {N n p d q : ℕ} (k : Root) (t : ℝ) (hd : 0<d)
    (hq : q.Prime) (hcop : q.Coprime N) (hQ : 0≤rootQ N n k t p) {z : ℝ}
    (hz : cutoff (rootQ N n k t p) (d*q) 3≤z) :
    let Q := rootQ N n k t p; let b := d*q
    ordinaryRosserWeight true N b (rootLevel Q b) z =
        ordinaryRosserWeight true N b (rootLevel Q b) (cutoff Q b 3) ∧
      ∀ f : ℕ → ℝ, weightedUpper N Q b z f=weightedUpper N Q b (cutoff Q b 3) f := by
  let Q := rootQ N n k t p
  let b := d*q
  let R := Q/(b:ℝ)
  have hR : 0≤R := div_nonneg hQ (Nat.cast_nonneg _)
  have hlev : ⌈R⌉₊=rootLevel Q b := true_child_ceil k t hq hcop hd hQ
  have hmin : min z (R^(1/3:ℝ))=cutoff Q b 3 := min_eq_right hz
  have hzcap := Nat.le_ceil z
  have hc := hz.trans hzcap
  have full := plus_eq (N:=N) hzcap hlev
  have cut := plus_eq (N:=N) hc hlev
  constructor
  · have h := actualSmallRosserPlus_eq_cubeCutoff (b*N) ⌈z⌉₊ z R hR
    rw [hmin,full,cut] at h
    exact h
  · intro f
    have h := actualSmallRosserPlus_weighted_sum_eq_cubeCutoff (b*N) ⌈z⌉₊ z R hR f
    rw [hmin] at h
    simp only [actualSmallRosserSupport,prime_product hzcap,prime_product hc,full,cut] at h
    exact h

theorem original_model_and_AP {N n p d q : ℕ} (k : Root) (t : ℝ) (hd : 0<d)
    (hq : q.Prime) (hcop : q.Coprime N) (hQ : 0≤rootQ N n k t p) {z : ℝ}
    (hz : cutoff (rootQ N n k t p) (d*q) 3≤z) :
    let Q := rootQ N n k t p; let b := d*q
    model true N Q b z=model true N Q b (cutoff Q b 3) ∧
      ordinaryRosserRemainder true N b (rootLevel Q b) z=
        ordinaryRosserRemainder true N b (rootLevel Q b) (cutoff Q b 3) := by
  have hh := (upper_polynomial_exact k t hd hq hcop hQ hz).2
  constructor
  · unfold model
    congr 1
    simpa only [weightedUpper,ordinaryRosserMainSum,div_eq_mul_inv,one_mul] using
      hh (fun e => 1/(Nat.totient e:ℝ))
  · exact hh (sourceSequenceRemainder N (d*q))

end
end ImbalancedChen.Part5OriginalH430PairExactUpperPolynomial
