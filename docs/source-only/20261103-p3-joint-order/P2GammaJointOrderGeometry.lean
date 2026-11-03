import ImbalancedChen.P2GammaJointLabels
import ImbalancedChen.P2GammaOrderingStripPayment

/-!
Source-only continuation of P3.6. UNCOMPILED / KERNEL-UNVERIFIED.
The two old prime slots are retained in the remainder factor list.
The close pair is the first TWO primes of the original mother word,
not the old marked pair. Equal products retain all their labels.
No causal common-Q identification or relative-Theta estimate is asserted.
-/

namespace ImbalancedChen.P2GammaJointOrderGeometry
noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2GammaCompleteProductTrimPayment P2GammaUpperStripPayment
open P2GammaRetainedInteriorGeometry
open P2GammaOrderingStripPayment P2GammaJointLabels
open P5OriginalU5CausalFinite (pairSupport)

def jointOrderLabels (N : ℕ) (cs : List ℕ) (e : ℝ) : Finset JointLabel :=
  (jointLabels N cs).filter (fun z => z.2 ∈ orderLabels N z.1 cs e)

/-- The old pair is encoded as TWO separate factors. -/
def jointOrderCode (z : JointLabel) : (ℕ × ℕ) × List ℕ :=
  ((orderCode z.2).1,z.1.1 :: z.1.2 :: (orderCode z.2).2)

private theorem root_word_ordered {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {x : Label} (hx : x ∈ rootLabels N t cs) : x.1.Pairwise (· < ·) := by
  exact ((secondFunctionalMother_tuple_mem _ _ _).mp
    (Finset.mem_filter.mp (rootLabels_data hx).1).1).2.1

/-- The complete product, INCLUDING both old primes, pays the close-pair
count. This is not a fixed-pair count multiplied by pairSupport.card. -/
theorem jointOrderCode_mem_envelope {N : ℕ} {cs : List ℕ}
    (hlen : 2 ≤ cs.length) {e : ℝ} {z : JointLabel}
    (hz : z ∈ jointOrderLabels N cs e) :
    jointOrderCode z ∈ orderEnvelope N (cs.length+2) e := by
  obtain ⟨hzjoint,hzorder⟩ := Finset.mem_filter.mp hz
  obtain ⟨ht,hxroot⟩ := (mem_jointLabels N cs z).mp hzjoint
  have hclose := (Finset.mem_filter.mp hzorder).2
  have hlength := root_word_length hxroot
  rcases z with ⟨t,w,n⟩
  cases w with
  | nil => simp at hlength; omega
  | cons p w =>
    cases w with
    | nil => simp at hlength; omega
    | cons q v =>
      let R := t.1 :: t.2 :: (v++[n])
      let r := R.prod
      have hd : 0 < t.1*t.2 :=
        P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht
      have hdata := rootLabels_data hxroot
      have hn : 0 < n := hdata.2.1
      have hp : 0 < p := by
        simpa only [labelHead,List.headD_cons] using
          (original_label_head_prime (by omega) hxroot).pos
      have hord := List.pairwise_cons.mp (root_word_ordered hxroot)
      have hpq : p < q := hord.1 q (List.mem_cons_self q v)
      have hq : 0 < q := hp.trans hpq
      have hv : 0 < v.prod := by
        have hwp := word_prod_pos hdata.1
        simp only [List.prod_cons] at hwp
        exact (Nat.mul_pos_iff.mp ((Nat.mul_pos_iff.mp hwp).2)).2
      have hr : 0 < r := by
        have ht1 := (Nat.mul_pos_iff.mp hd).1
        have ht2 := (Nat.mul_pos_iff.mp hd).2
        dsimp [r,R]
        simp only [List.prod_cons,List.prod_append,List.prod_singleton]
        positivity
      have hprod : p*q*r < N := by
        have hh := hdata.2.2.2
        have heq : product (t.1*t.2) (p::q::v,n)=p*q*r := by
          simp only [product,List.prod_cons,r,R,List.prod_append,List.prod_singleton]
          ring
        rwa [heq] at hh
      have hrN : r ≤ N := by
        have hfactor : 1 ≤ p*q := Nat.mul_pos hp hq
        have hle : r ≤ p*q*r := by
          simpa only [one_mul] using Nat.mul_le_mul_right r hfactor
        exact hle.trans hprod.le
      have hqN : q ≤ N := by
        have hfactor : 1 ≤ p*r := Nat.mul_pos hp hr
        have hle : q ≤ p*q*r := by
          calc
            q = 1*q := by simp
            _ ≤ (p*r)*q := Nat.mul_le_mul_right q hfactor
            _ = p*q*r := by ring
        exact hle.trans hprod.le
      obtain ⟨s,hs,hps⟩ := hclose
      have hqs : q ≤ s := by
        rcases List.mem_cons.mp hs with h|h
        · subst s; rfl
        · exact ((List.pairwise_cons.mp hord.2).1 s h).le
      have hqclose : (q : ℝ) < (1+e)*(p : ℝ) :=
        (by exact_mod_cast hqs : (q : ℝ) ≤ s).trans hps
      have hpp : p*p*r ≤ N :=
        (Nat.mul_le_mul_right r (Nat.mul_le_mul_left p hpq.le)).trans hprod.le
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      have hX : 0 ≤ (N : ℝ)/(r : ℝ) := by positivity
      have hp2 : (p : ℝ)^2 ≤ (N : ℝ)/(r : ℝ) := by
        apply (le_div_iff₀ hrR).mpr
        have hpp' : p^2*r ≤ N := by simpa only [pow_two] using hpp
        exact_mod_cast hpp'
      have hpsqrt : (p : ℝ) ≤ Real.sqrt ((N : ℝ)/(r : ℝ)) := by
        have hs0 := Real.sqrt_nonneg ((N : ℝ)/(r : ℝ))
        have hs2 := Real.sq_sqrt hX
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        nlinarith
      have hpI : p ∈ Finset.Icc 1 ⌊Real.sqrt ((N : ℝ)/(r : ℝ))⌋₊ :=
        Finset.mem_Icc.mpr ⟨hp,(Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr hpsqrt⟩
      have hqI : q ∈ closeFollowers N p e :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpq,hqN⟩,hqclose⟩
      have hpair : (p,q) ∈ closePairs N ((N : ℝ)/(r : ℝ)) e :=
        Finset.mem_biUnion.mpr ⟨p,hpI,Finset.mem_image.mpr ⟨q,hqI,rfl⟩⟩
      have hR : R ∈ orderedFactors (cs.length+2-1) r := by
        apply (mem_orderedFactors _ _ _).mpr
        refine ⟨?_,rfl,hr⟩
        simp only [R,List.length_cons,List.length_append,List.length_singleton]
        simp only [List.length_cons] at hlength
        omega
      change ((p,q),R) ∈ orderEnvelope N (cs.length+2) e
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_Ioc.mpr ⟨hr,hrN⟩,
        Finset.mem_product.mpr ⟨hpair,hR⟩⟩

theorem jointOrderCode_inj {N : ℕ} {cs : List ℕ}
    (hlen : 2 ≤ cs.length) (e : ℝ) :
    Set.InjOn jointOrderCode (jointOrderLabels N cs e) := by
  rintro ⟨t,x⟩ hz ⟨u,y⟩ hv heq
  have hx := (Finset.mem_filter.mp hz).2
  have hy := (Finset.mem_filter.mp hv).2
  change ((orderCode x).1,t.1::t.2::(orderCode x).2) =
    ((orderCode y).1,u.1::u.2::(orderCode y).2) at heq
  obtain ⟨hhead,hrest⟩ := Prod.mk.inj heq
  obtain ⟨ht1,htail⟩ := List.cons.inj hrest
  obtain ⟨ht2,hrest⟩ := List.cons.inj htail
  have htu : t=u := Prod.ext ht1 ht2
  subst u
  have hxy : x=y := orderCode_inj hlen e hx hy (Prod.ext hhead hrest)
  exact Prod.ext rfl hxy

/-- The joint thin-label count costs k+1 logarithms, rather than the
fixed-pair k-1. The extra two slots are explicitly charged. -/
theorem jointOrderLabels_card_le (N : ℕ) (cs : List ℕ)
    (hlen : 2 ≤ cs.length) {e : ℝ} (he : 0 ≤ e) :
    ((jointOrderLabels N cs e).card : ℝ) ≤
      e*(N : ℝ)*(1+Real.log (N : ℝ))^(cs.length+1) := by
  have hc : (jointOrderLabels N cs e).card ≤
      (orderEnvelope N (cs.length+2) e).card :=
    Finset.card_le_card_of_injOn jointOrderCode
      (fun z hz => jointOrderCode_mem_envelope hlen hz) (jointOrderCode_inj hlen e)
  have hcast : ((jointOrderLabels N cs e).card : ℝ) ≤
      (orderEnvelope N (cs.length+2) e).card := by exact_mod_cast hc
  have hexp : cs.length+2-1=cs.length+1 := by omega
  exact hcast.trans (by simpa only [hexp] using orderEnvelope_card_le N (cs.length+2) he)

theorem jointOrderLabels_empty_of_short {N : ℕ} {cs : List ℕ}
    (hcs : cs.length ≤ 1) (e : ℝ) : jointOrderLabels N cs e=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  have hx := (Finset.mem_filter.mp hz).2
  rw [orderLabels_empty_of_short hcs e] at hx
  exact Finset.not_mem_empty _ hx

end
end ImbalancedChen.P2GammaJointOrderGeometry
