import ImbalancedChen.P2GammaUpperStripPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Strict-order rejection on the ORIGINAL Gamma labels. The count is
constructed, rather than assumed: two leading primes are encoded with
the ordered remaining factors and the exact quotient, including 1.
Strict integer followers have no additive lattice error. The existing
native reciprocal divisor mean then supplies the thin-label count.
-/

namespace ImbalancedChen.P2GammaOrderingStripPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open Wu2008DoubleSieve
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2GammaCompleteProductTrimPayment P2GammaRetainedInteriorGeometry
open P2GammaLowerRejectedPayment P2GammaUpperStripPayment
open P5OriginalU5CausalFinite (pairSupport)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def closeFollowers (N p : ℕ) (e : ℝ) : Finset ℕ :=
  (Finset.Ioc p N).filter (fun q => (q : ℝ) < (1+e)*(p : ℝ))

/-- Strict p<q removes the diagonal. The positive integer q-p is at
most floor(e*p); no +1 term and no subpower divisor bound is used. -/
theorem closeFollowers_card_le (N p : ℕ) {e : ℝ} (he : 0 ≤ e) :
    ((closeFollowers N p e).card : ℝ) ≤ e*(p : ℝ) := by
  have hY : 0 ≤ e*(p : ℝ) := mul_nonneg he (Nat.cast_nonneg p)
  have hmap : ∀ q ∈ closeFollowers N p e,
      q-p ∈ Finset.Ioc 0 ⌊e*(p : ℝ)⌋₊ := by
    intro q hq
    obtain ⟨hqI,hclose⟩ := Finset.mem_filter.mp hq
    have hpq := (Finset.mem_Ioc.mp hqI).1
    refine Finset.mem_Ioc.mpr ⟨Nat.sub_pos_of_lt hpq,?_⟩
    apply (Nat.le_floor_iff hY).mpr
    rw [Nat.cast_sub hpq.le]
    nlinarith
  have hinj : Set.InjOn (fun q => q-p) (closeFollowers N p e) := by
    intro q hq r hr heq
    have hpq := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
    have hpr := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
    omega
  have hc := Finset.card_le_card_of_injOn (fun q => q-p) hmap hinj
  have hc' : ((closeFollowers N p e).card : ℝ) ≤ (⌊e*(p : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (by simpa using hc : (closeFollowers N p e).card ≤ ⌊e*(p : ℝ)⌋₊)
  exact hc'.trans (Nat.floor_le hY)

/-- For an actual pair p<q with pq≤X, p≤sqrt(X). The envelope deliberately
keeps every close follower once that first-coordinate test holds. -/
def closePairs (N : ℕ) (X e : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 ⌊Real.sqrt X⌋₊).biUnion
    (fun p => (closeFollowers N p e).image (fun q => (p,q)))

theorem closePairs_card_le (N : ℕ) {X e : ℝ} (hX : 0 ≤ X) (he : 0 ≤ e) :
    ((closePairs N X e).card : ℝ) ≤ e*X := by
  let P := ⌊Real.sqrt X⌋₊
  have hP : (P : ℝ)^2 ≤ X := by
    have hp := Nat.floor_le (Real.sqrt_nonneg X)
    have hps := Real.sq_sqrt hX
    have hp0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    dsimp [P] at hp0 ⊢
    nlinarith
  have hcount : ((closePairs N X e).card : ℝ) ≤
      ∑ p ∈ Finset.Icc 1 P, ((closeFollowers N p e).card : ℝ) := by
    have hc : (closePairs N X e).card ≤
        ∑ p ∈ Finset.Icc 1 P, (closeFollowers N p e).card := by
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum
        (fun p hp => Finset.card_image_le))
    exact_mod_cast hc
  calc
    _ ≤ ∑ p ∈ Finset.Icc 1 P, ((closeFollowers N p e).card : ℝ) := hcount
    _ ≤ ∑ p ∈ Finset.Icc 1 P, e*(p : ℝ) :=
      Finset.sum_le_sum (fun p hp => closeFollowers_card_le N p he)
    _ ≤ ∑ _p ∈ Finset.Icc 1 P, e*(P : ℝ) :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Finset.mem_Icc.mp hp).2) he)
    _ = e*(P : ℝ)^2 := by simp; ring
    _ ≤ e*X := mul_le_mul_of_nonneg_left hP he

def orderEnvelope (N k : ℕ) (e : ℝ) : Finset ((ℕ × ℕ) × List ℕ) :=
  (Finset.Ioc 0 N).biUnion (fun r =>
    (closePairs N ((N : ℝ)/(r : ℝ)) e).product (orderedFactors (k-1) r))

/-- Exact ordered-factor multiplicities, not a divisor norm assumed for
an abstract sequence. The last factor is the original quotient. -/
theorem orderEnvelope_card_le (N k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    ((orderEnvelope N k e).card : ℝ) ≤
      e*(N : ℝ)*(1+Real.log (N : ℝ))^(k-1) := by
  have hcount : ((orderEnvelope N k e).card : ℝ) ≤
      ∑ r ∈ Finset.Ioc 0 N,
        ((closePairs N ((N : ℝ)/(r : ℝ)) e).card : ℝ) *
          (fouvryTau (k-1) r : ℝ) := by
    have hc : (orderEnvelope N k e).card ≤
        ∑ r ∈ Finset.Ioc 0 N,
          (closePairs N ((N : ℝ)/(r : ℝ)) e).card * fouvryTau (k-1) r := by
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun r hr => by
        rw [Finset.card_product,card_orderedFactors]))
    exact_mod_cast hc
  calc
    _ ≤ ∑ r ∈ Finset.Ioc 0 N,
        ((closePairs N ((N : ℝ)/(r : ℝ)) e).card : ℝ) *
          (fouvryTau (k-1) r : ℝ) := hcount
    _ ≤ ∑ r ∈ Finset.Ioc 0 N,
        (e*((N : ℝ)/(r : ℝ))) * (fouvryTau (k-1) r : ℝ) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right
        (closePairs_card_le N (by positivity) he) (Nat.cast_nonneg _))
    _ = e*(N : ℝ)*∑ r ∈ Finset.Ioc 0 N, (fouvryTau (k-1) r : ℝ)/(r : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_fouvryTau_div_le (k-1) N)
      (mul_nonneg he (Nat.cast_nonneg N))

def orderLabels (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ) (e : ℝ) : Finset Label :=
  (rootLabels N t cs).filter (fun x => ∃ r ∈ x.1.tail,
    (r : ℝ) < (1+e)*(labelHead x : ℝ))

def orderCode (x : Label) : (ℕ × ℕ) × List ℕ :=
  ((x.1.headD 0,x.1.tail.headD 0),x.1.drop 2++[x.2])

private theorem root_word_ordered {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {x : Label} (hx : x ∈ rootLabels N t cs) : x.1.Pairwise (· < ·) := by
  exact ((secondFunctionalMother_tuple_mem _ _ _).mp
    (Finset.mem_filter.mp (rootLabels_data hx).1).1).2.1

/-- A close later prime forces the SECOND original prime to be close.
The injection retains the two labelled leading slots, every remaining
slot in its original order, and the unit quotient when present. -/
theorem orderCode_mem_envelope {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {cs : List ℕ} (hlen : 2 ≤ cs.length)
    {e : ℝ} {x : Label} (hx : x ∈ orderLabels N t cs e) :
    orderCode x ∈ orderEnvelope N cs.length e := by
  obtain ⟨hxroot,hclose⟩ := Finset.mem_filter.mp hx
  have hlength := root_word_length hxroot
  rcases x with ⟨w,n⟩
  cases w with
  | nil => simp at hlength; omega
  | cons p w =>
    cases w with
    | nil => simp at hlength; omega
    | cons q v =>
      let R := v++[n]
      let r := R.prod
      let d := t.1*t.2
      have hd : 0 < d := P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht
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
      have hr : 0 < r := by dsimp [r,R]; simp only [List.prod_append,List.prod_singleton]; positivity
      have hprod : d*p*q*r < N := by
        have hh := hdata.2.2.2
        have heq : product (t.1*t.2) (p::q::v,n)=d*p*q*r := by
          simp only [product,List.prod_cons,r,R,List.prod_append,List.prod_singleton,d]
          ring
        rwa [heq] at hh
      have hrN : r ≤ N := by
        have hfactor : 1 ≤ d*p*q := Nat.mul_pos (Nat.mul_pos hd hp) hq
        have hle : r ≤ d*p*q*r := by
          simpa only [one_mul] using Nat.mul_le_mul_right r hfactor
        exact hle.trans hprod.le
      have hqN : q ≤ N := by
        have hfactor : 1 ≤ d*p*r := Nat.mul_pos (Nat.mul_pos hd hp) hr
        have hle : q ≤ d*p*q*r := by
          calc
            q = 1*q := by simp
            _ ≤ (d*p*r)*q := Nat.mul_le_mul_right q hfactor
            _ = d*p*q*r := by ring
        exact hle.trans hprod.le
      obtain ⟨s,hs,hps⟩ := hclose
      have hqs : q ≤ s := by
        rcases List.mem_cons.mp hs with h|h
        · subst s; rfl
        · exact ((List.pairwise_cons.mp hord.2).1 s h).le
      have hqclose : (q : ℝ) < (1+e)*(p : ℝ) := by
        exact (by exact_mod_cast hqs : (q : ℝ) ≤ s).trans hps
      have hpp : p*p*r ≤ N := by
        have hpq' : p*p ≤ d*p*q := by
          have hd1 : 1 ≤ d := hd
          calc
            p*p ≤ p*q := Nat.mul_le_mul_left p hpq.le
            _ ≤ d*(p*q) := by simpa only [one_mul] using Nat.mul_le_mul_right (p*q) hd1
            _ = d*p*q := by ring
        exact (Nat.mul_le_mul_right r hpq').trans hprod.le
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
      have hR : R ∈ orderedFactors (cs.length-1) r := by
        apply (mem_orderedFactors _ _ _).mpr
        refine ⟨?_,rfl,hr⟩
        simp only [R,List.length_append,List.length_singleton]
        simp only [List.length_cons] at hlength
        omega
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_Ioc.mpr ⟨hr,hrN⟩,
        Finset.mem_product.mpr ⟨hpair,hR⟩⟩

theorem orderCode_inj {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hlen : 2 ≤ cs.length) (e : ℝ) :
    Set.InjOn orderCode (orderLabels N t cs e) := by
  intro x hx y hy heq
  have hxroot := (Finset.mem_filter.mp hx).1
  have hyroot := (Finset.mem_filter.mp hy).1
  have hxlen := root_word_length hxroot
  have hylen := root_word_length hyroot
  rcases x with ⟨w,n⟩
  rcases y with ⟨u,m⟩
  cases w with
  | nil => simp at hxlen; omega
  | cons p w =>
    cases w with
    | nil => simp at hxlen; omega
    | cons q v =>
      cases u with
      | nil => simp at hylen; omega
      | cons a u =>
        cases u with
        | nil => simp at hylen; omega
        | cons b z =>
          change ((p,q),v++[n])=((a,b),z++[m]) at heq
          obtain ⟨hpq,hrest⟩ := Prod.mk.inj heq
          obtain ⟨hp,hq⟩ := Prod.mk.inj hpq
          have hvz : v.length=z.length := by
            simp only [List.length_cons] at hxlen hylen
            omega
          obtain ⟨hv,hn⟩ := List.append_inj hrest hvz
          have hnm : n=m := by simpa using hn
          subst a; subst b; subst z; subst m
          rfl

/-- The actual strict-order label count. This is a derived bound with
all source multiplicities retained, rather than a cardinality premise. -/
theorem orderLabels_card_le {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (cs : List ℕ) (hlen : 2 ≤ cs.length) {e : ℝ} (he : 0 ≤ e) :
    ((orderLabels N t cs e).card : ℝ) ≤
      e*(N : ℝ)*(1+Real.log (N : ℝ))^(cs.length-1) := by
  have hc : (orderLabels N t cs e).card ≤ (orderEnvelope N cs.length e).card :=
    Finset.card_le_card_of_injOn orderCode
      (fun x hx => orderCode_mem_envelope ht hlen hx) (orderCode_inj hlen e)
  exact (by exact_mod_cast hc : ((orderLabels N t cs e).card : ℝ) ≤
    (orderEnvelope N cs.length e).card).trans (orderEnvelope_card_le N cs.length he)

theorem orderLabels_empty_of_short {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hcs : cs.length ≤ 1) (e : ℝ) : orderLabels N t cs e = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨hx,hclose⟩ := Finset.mem_filter.mp hx
  have hlen := root_word_length hx
  rcases x with ⟨w,n⟩
  cases w with
  | nil => simpa using hclose
  | cons p w =>
    cases w with
    | nil => simpa using hclose
    | cons q v => simp only [List.length_cons] at hlen; omega

def kernelMomentExponent (J : ℕ) : ℕ := max (J+2) 15

private theorem cast_card_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith

/-- The complete actual-label kernel energy is supplied by two native
UNSHIFTED moments. The positive reflection m↦N-m handles tau^4, and
Young's inequality handles its product with actual source multiplicity.
There is no shifted-correlation estimate or energy assumption. -/
theorem original_label_kernel_energy_le {N : ℕ} (hN : 1 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (cs : List ℕ) (J : ℕ)
    (hJ : (cs.length+2)^2-1 ≤ J) :
    (∑ x ∈ rootLabels N t cs,
      (((N-product (t.1*t.2) x).divisors.card : ℝ)+
        4*(1+Real.log (N : ℝ)))^2) ≤
      34*(N : ℝ)*(1+Real.log (N : ℝ))^(kernelMomentExponent J) := by
  let S := upperProducts N (N : ℝ)
  let L := 1+Real.log (N : ℝ)
  let a := fun m => ((rootProductFiber N t cs m).card : ℝ)
  let b := fun m => ((N-m).divisors.card : ℝ)+4*L
  let E := kernelMomentExponent J
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hNr]
  have hS : S ⊆ Finset.Ioc 0 N := Finset.filter_subset _ _
  have hS' : S ⊆ Finset.Ioc 0 ⌊(N : ℝ)⌋₊ := by simpa only [Nat.floor_natCast] using hS
  have ha : (∑ m ∈ S, a m^2) ≤ (N : ℝ)*L^J :=
    (original_Gamma_word_square_sum_le ht cs hNr S hS').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJ) (Nat.cast_nonneg N))
  have h4 : (∑ m ∈ S, ((N-m).divisors.card : ℝ)^4) ≤ (N : ℝ)*L^15 := by
    let T := S.image (fun m => N-m)
    have hT : T ⊆ Finset.Ioc 0 N := by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      simpa only [Nat.floor_natCast] using
        upperProducts_difference_maps (Nat.cast_nonneg N) m hm
    calc
      _ = ∑ n ∈ T, (n.divisors.card : ℝ)^4 :=
        (Finset.sum_image (upperProducts_difference_inj N (N : ℝ))).symm
      _ ≤ ∑ n ∈ Finset.Ioc 0 N, (n.divisors.card : ℝ)^4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hT (fun n hn hnot => by positivity)
      _ ≤ _ := by
        simpa only [Nat.floor_natCast,fouvryTau_two] using
          sum_fouvryTau_pow_le_real (k := 2) (by norm_num) 4 hNr
  have hproducts : rootProducts N t cs ⊆ S := by
    intro m hm
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨root_product_positive ht hx,(rootLabels_data hx).2.2.2.le⟩,
        (rootLabels_data hx).2.2.2,by exact_mod_cast Nat.sub_le N (product (t.1*t.2) x)⟩
  have hpoint (m : ℕ) : a m*b m^2 ≤
      a m^2+((N-m).divisors.card : ℝ)^4+32*L^2*a m^2 := by
    have ha0 : 0 ≤ a m := Nat.cast_nonneg _
    have hnat : a m ≤ a m^2 := cast_card_le_sq _
    have hb : b m^2 ≤ 2*((N-m).divisors.card : ℝ)^2+32*L^2 := by
      dsimp [b]
      nlinarith [sq_nonneg (((N-m).divisors.card : ℝ)-4*L)]
    have hmul := mul_le_mul_of_nonneg_left hb ha0
    have hyoung := sq_nonneg (a m-((N-m).divisors.card : ℝ)^2)
    have hmean := mul_le_mul_of_nonneg_left hnat (show 0 ≤ 32*L^2 by positivity)
    nlinarith
  have hJE : J ≤ E := (show J ≤ J+2 by omega).trans (le_max_left _ _)
  have hJ2E : J+2 ≤ E := le_max_left _ _
  have h15E : 15 ≤ E := le_max_right _ _
  have hpa : (N : ℝ)*L^J ≤ (N : ℝ)*L^E :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJE) (Nat.cast_nonneg N)
  have hp4 : (N : ℝ)*L^15 ≤ (N : ℝ)*L^E :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL h15E) (Nat.cast_nonneg N)
  have hpmean : 32*L^2*((N : ℝ)*L^J) ≤ 32*(N : ℝ)*L^E := by
    calc
      _ = 32*(N : ℝ)*L^(J+2) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hJ2E) (by positivity)
  calc
    _ = ∑ m ∈ rootProducts N t cs, a m*b m^2 :=
      root_word_real_test_eq_grouped N t cs (fun m => b m^2)
    _ ≤ ∑ m ∈ S, a m*b m^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hproducts (fun m hm hnot => by dsimp [a]; positivity)
    _ ≤ ∑ m ∈ S, a m^2+((N-m).divisors.card : ℝ)^4+32*L^2*a m^2 :=
      Finset.sum_le_sum (fun m hm => hpoint m)
    _ = (∑ m ∈ S, a m^2)+(∑ m ∈ S, ((N-m).divisors.card : ℝ)^4)+
        32*L^2*(∑ m ∈ S, a m^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ (N : ℝ)*L^J+(N : ℝ)*L^15+32*L^2*((N : ℝ)*L^J) := by gcongr
    _ ≤ 34*(N : ℝ)*L^E := by nlinarith

/-- Actual strict-order error after the full signed modulus sum. Both
the thin-label count and the kernel moment are derived above. -/
theorem wordError_order_strip_le {N : ℕ} (hN : 1 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (cs : List ℕ)
    (hlen : 2 ≤ cs.length) (J : ℕ) (hJ : (cs.length+2)^2-1 ≤ J)
    {e u : ℝ} (he : 0 ≤ e) (hu : 0 < u)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (w : Label → ℝ)
    (hQ : Q ⊆ Finset.Icc 1 N) (hrho : ∀ q ∈ Q, |rho q| ≤ 1)
    (hw : ∀ x ∈ rootLabels N t cs, |w x| ≤ 1)
    (hzero : ∀ x ∈ rootLabels N t cs, x ∉ orderLabels N t cs e → w x=0) :
    |wordError N t cs Q rho w| ≤
      u*e*(N : ℝ)*(1+Real.log (N : ℝ))^(cs.length-1)+
        34*(N : ℝ)*(1+Real.log (N : ℝ))^(kernelMomentExponent J)/u := by
  let S := orderLabels N t cs e
  let L := 1+Real.log (N : ℝ)
  let b := fun x : Label => ((N-product (t.1*t.2) x).divisors.card : ℝ)+4*L
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsub : S ⊆ rootLabels N t cs := Finset.filter_subset _ _
  have hlabel : |wordError N t cs Q rho w| ≤ ∑ x ∈ S, b x := by
    have heq : wordError N t cs Q rho w =
        ∑ x ∈ rootLabels N t cs, w x *
          ∑ q ∈ Q, rho q*gammaKernel N q (product (t.1*t.2) x) := by
      simp only [wordError,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro q hq
      ring
    rw [heq]
    calc
      _ ≤ ∑ x ∈ rootLabels N t cs,
          |w x*∑ q ∈ Q, rho q*gammaKernel N q (product (t.1*t.2) x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ rootLabels N t cs, if x ∈ S then b x else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hs : x ∈ S
        · rw [if_pos hs,abs_mul]
          have hk := kernel_absolute_modulus_sum_le (rootLabels_data hx).2.2.2 Q rho hQ hrho
          rw [max_eq_right hNr] at hk
          exact (mul_le_mul (hw x hx) (Finset.abs_sum_le_sum_abs _ _)
            (abs_nonneg _) zero_le_one).trans (by simpa only [one_mul] using hk)
        · simp only [if_neg hs,hzero x hx hs,zero_mul,abs_zero]
      _ = ∑ x ∈ S, b x := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp [S,orderLabels]
  have henergy : (∑ x ∈ S, b x^2) ≤
      34*(N : ℝ)*L^(kernelMomentExponent J) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx hnot => sq_nonneg _)).trans
      (original_label_kernel_energy_le hN ht cs J hJ)
  have hcard := orderLabels_card_le ht cs hlen he
  calc
    _ ≤ ∑ x ∈ S, b x := hlabel
    _ ≤ ∑ x ∈ S, u+b x^2/u :=
      Finset.sum_le_sum (fun x hx => by simpa using young_scaled 1 (b x) u hu)
    _ = u*(S.card : ℝ)+(∑ x ∈ S, b x^2)/u := by
      rw [Finset.sum_add_distrib,Finset.sum_div]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ u*(e*(N : ℝ)*L^(cs.length-1))+
        (34*(N : ℝ)*L^(kernelMomentExponent J))/u := by gcongr
    _ = _ := by ring

def wordOrderRejectedWeight (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (x : Label) : ℝ :=
  if cs=[] then 0 else smoothTrim T (product (t.1*t.2) x) *
    rawOrderRejectedWeight N t H δ K x

theorem wordOrderRejectedWeight_abs_le_one (N : ℕ) (t : ℕ × ℕ)
    (cs : List ℕ) (T H δ : ℝ) (K : ℕ) (x : Label) :
    |wordOrderRejectedWeight N t cs T H δ K x| ≤ 1 := by
  have hr := rejectedRealWeight_range N t H δ K x
  have h0 : 0 ≤ smoothTrim T (product (t.1*t.2) x) :=
    Real.smoothTransition.nonneg _
  have h1 : smoothTrim T (product (t.1*t.2) x) ≤ 1 :=
    Real.smoothTransition.le_one _
  unfold wordOrderRejectedWeight rawOrderRejectedWeight rawRemainingRejectedWeight
  split_ifs <;> simp only [mul_zero,abs_zero,zero_le_one]
  rw [abs_of_nonneg (mul_nonneg h0 hr.1)]
  exact (mul_le_mul h1 hr.2 hr.1 zero_le_one).trans_eq (by norm_num)

theorem wordOrderRejectedWeight_mem {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {cs : List ℕ} {T H δ : ℝ} (hδ : 0 < δ)
    {K : ℕ} {x : Label} (hx : x ∈ rootLabels N t cs)
    (hw : wordOrderRejectedWeight N t cs T H δ K x ≠ 0) :
    x ∈ orderLabels N t cs (Real.exp (2*δ)-1) := by
  cases cs with
  | nil => simp [wordOrderRejectedWeight] at hw
  | cons c cs =>
    have hraw : rawOrderRejectedWeight N t H δ K x ≠ 0 := by
      intro hz
      exact hw (by simp [wordOrderRejectedWeight,hz])
    obtain ⟨r,hr,_,hclose⟩ := rawOrderRejectedWeight_support ht hδ hx hraw
    apply Finset.mem_filter.mpr
    refine ⟨hx,r,hr,?_⟩
    convert hclose using 1 <;> ring

/-- Elementary exponential-width conversion on a fixed neighbourhood.
It is the same tangent inequality used for the upper-product wall. -/
theorem exp_order_width_le {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : 2*δ ≤ Real.log 2) :
    0 ≤ Real.exp (2*δ)-1 ∧ Real.exp (2*δ)-1 ≤ 4*δ := by
  have hlow : 1 ≤ Real.exp (2*δ) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : (0 : ℝ) ≤ 2*δ)
  have hupper : Real.exp (2*δ) ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      Real.exp_le_exp.mpr hsmall
  have htangent : 1-2*δ ≤ Real.exp (-(2*δ)) := by
    linarith [Real.add_one_le_exp (-(2*δ))]
  have hmul := mul_le_mul_of_nonneg_right htangent (Real.exp_pos (2*δ)).le
  have hexp : Real.exp (-(2*δ))*Real.exp (2*δ)=1 := by
    rw [← Real.exp_add]
    simp
  rw [hexp] at hmul
  have hscale := mul_le_mul_of_nonneg_left hupper (by linarith : 0 ≤ 2*δ)
  exact ⟨by linarith,by nlinarith⟩

/-- J also dominates k-1 for every word whose original fibre exponent is
at most J. This permits ONE exponent for the complete occurrence list. -/
theorem word_length_sub_one_le {cs : List ℕ} {J : ℕ}
    (hJ : (cs.length+2)^2-1 ≤ J) : cs.length-1 ≤ J := by
  have hs : cs.length ≤ (cs.length+2)^2 := by nlinarith
  omega

def orderMeshExponent (J A : ℕ) : ℕ :=
  kernelMomentExponent J+(A+2)+J+(A+2)

private theorem order_logMesh_budget {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ))
    (J A : ℕ) :
    (Real.log (N : ℝ))^(kernelMomentExponent J+(A+2)) *
      (4*boundaryLogMesh (orderMeshExponent J A) N)*(N : ℝ)*
        (1+Real.log (N : ℝ))^J +
      34*(N : ℝ)*(1+Real.log (N : ℝ))^(kernelMomentExponent J)/
        (Real.log (N : ℝ))^(kernelMomentExponent J+(A+2)) ≤
      (4*(2 : ℝ)^J+34*(2 : ℝ)^(kernelMomentExponent J))*(N : ℝ)/
        (Real.log (N : ℝ))^(A+2) := by
  let l := Real.log (N : ℝ)
  let E := kernelMomentExponent J
  have hl : 0 < l := by dsimp [l]; linarith
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hL : 1+l ≤ 2*l := by dsimp [l]; linarith
  have hJ : (1+l)^J ≤ (2*l)^J := pow_le_pow_left₀ (by linarith) hL J
  have hE : (1+l)^E ≤ (2*l)^E := pow_le_pow_left₀ (by linarith) hL E
  calc
    _ ≤ l^(E+(A+2))*(4*boundaryLogMesh (orderMeshExponent J A) N)*
          (N : ℝ)*(2*l)^J + 34*(N : ℝ)*(2*l)^E/l^(E+(A+2)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hJ (by unfold boundaryLogMesh; positivity)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
    _ = _ := by
      change l^(E+(A+2))*(4*(1/l^(E+(A+2)+J+(A+2))))*(N : ℝ)*(2*l)^J+
        34*(N : ℝ)*(2*l)^E/l^(E+(A+2)) =
          (4*(2 : ℝ)^J+34*(2 : ℝ)^E)*(N : ℝ)/l^(A+2)
      simp only [pow_add,mul_pow]
      field_simp [hl.ne']
      ring

/-- Actual ordering residual, with every original mask and the literal
smooth trim. J,A and the mesh precede ONE threshold, then all t/word/grid
and modulus data. Both the cardinality and the mixed moment are supplied. -/
theorem eventually_actual_orderRejected_word_logAccuracy (J A : ℕ)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (t : ℕ × ℕ), t ∈ pairSupport N →
      ∀ (cs : List ℕ), (cs.length+2)^2-1 ≤ J →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) → 0 < δ →
      δ ≤ boundaryLogMesh (orderMeshExponent J A) N →
      |wordError N t cs Q rho (wordOrderRejectedWeight N t cs T H δ K)| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let B := orderMeshExponent J A
  let E := kernelMomentExponent J
  let C : ℝ := 4*(2 : ℝ)^J+34*(2 : ℝ)^E
  have hB : 0 < B := by dsimp [B,orderMeshExponent]; omega
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmesh : ∀ᶠ N : ℕ in atTop, 2*boundaryLogMesh B N ≤ Real.log 2 := by
    have h := (tendsto_boundaryLogMesh hB).eventually
      (gt_mem_nhds (half_pos hlog2))
    filter_upwards [h] with N hN
    linarith
  have hcost := eventually_boundaryLogMesh_main_le_logAccuracy C A
    (k := A+4) (by omega) eta heta
  filter_upwards [hmesh,hcost,eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)]
    with N hmeshN hcostN hlog hN
  intro t ht cs hJ Q rho T H δ K hQ hrho hδ hδmesh
  let l := Real.log (N : ℝ)
  let L := 1+l
  let u := l^(E+(A+2))
  let e := Real.exp (2*δ)-1
  let w := wordOrderRejectedWeight N t cs T H δ K
  have hl : 0 < l := by dsimp [l]; linarith
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have he := exp_order_width_le hδ.le (by linarith)
  have hewidth : e ≤ 4*boundaryLogMesh B N := he.2.trans (by linarith)
  have hzero : ∀ x ∈ rootLabels N t cs, x ∉ orderLabels N t cs e → w x=0 := by
    intro x hx hnot
    by_contra hw
    exact hnot (wordOrderRejectedWeight_mem ht hδ hx hw)
  by_cases hlen : 2 ≤ cs.length
  · have hfinite := wordError_order_strip_le hN ht cs hlen J hJ he.1 hu Q rho w
      hQ hrho (fun x hx => wordOrderRejectedWeight_abs_le_one N t cs T H δ K x) hzero
    have hpow : L^(cs.length-1) ≤ L^J :=
      pow_le_pow_right₀ hL (word_length_sub_one_le hJ)
    have hcoef : u*e*(N : ℝ) ≤ u*(4*boundaryLogMesh B N)*(N : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hewidth hu.le) (Nat.cast_nonneg N)
    have hcoef0 : 0 ≤ u*(4*boundaryLogMesh B N)*(N : ℝ) := by
      have hb0 : 0 ≤ boundaryLogMesh B N := (hδ.trans_le hδmesh).le
      positivity
    have hfirst := mul_le_mul hcoef hpow (pow_nonneg (by linarith : 0 ≤ L) _) hcoef0
    have hcost' : C*(N : ℝ)/l^(A+2) ≤ eta*(N : ℝ)/l^A := by
      have heq : C*(N : ℝ)/l^(A+2) = C*boundaryLogMesh (A+4) N*(N : ℝ)*l^2 := by
        unfold boundaryLogMesh
        change C*(N : ℝ)/l^(A+2)=C*(1/l^(A+4))*(N : ℝ)*l^2
        rw [show A+4=(A+2)+2 by omega,pow_add]
        field_simp [hl.ne']
        ring
      rw [heq]
      exact hcostN
    exact hfinite.trans ((add_le_add_right hfirst _).trans
      ((order_logMesh_budget hlog J A).trans hcost'))
  · have hshort := orderLabels_empty_of_short (N := N) (t := t)
      (show cs.length ≤ 1 by omega) e
    have hz : ∀ x ∈ rootLabels N t cs, w x=0 := by
      intro x hx
      apply hzero x hx
      rw [hshort]
      exact Finset.not_mem_empty x
    have herr : wordError N t cs Q rho w=0 := by
      unfold wordError
      apply Finset.sum_eq_zero
      intro q hq
      have hs : (∑ x ∈ rootLabels N t cs, w x*gammaKernel N q (product (t.1*t.2) x))=0 :=
        Finset.sum_eq_zero (fun x hx => by rw [hz x hx,zero_mul])
      rw [hs,mul_zero]
    rw [herr,abs_zero]
    exact div_nonneg (mul_nonneg heta.le (Nat.cast_nonneg N)) (pow_nonneg hl.le A)

def originalOrderRejectedError (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map (fun cs => wordError N t cs Q rho
    (wordOrderRejectedWeight N t cs T H δ K))).sum

/-- Complete original mother LIST, including repeated occurrences and
unit quotients. The one threshold is uniform in every later marked pair.
No outside t-sum or full prime-product theorem is asserted. -/
theorem eventually_original_orderRejected_logAccuracy (A : ℕ) (eta : ℝ)
    (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (t : ℕ × ℕ), t ∈ pairSupport N →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) → 0 < δ →
      δ ≤ boundaryLogMesh
        (orderMeshExponent (listMomentOrder originalMotherOccurrences) A) N →
      |originalOrderRejectedError N t Q rho T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let L := originalMotherOccurrences
  let J := listMomentOrder L
  let eta0 := eta/((L.length : ℝ)+1)
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  filter_upwards [eventually_actual_orderRejected_word_logAccuracy J A eta0 heta0,
    eventually_one_le_nat_log] with N hword hlog
  intro t ht Q rho T H δ K hQ hrho hδ hδmesh
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  let f := fun cs => wordError N t cs Q rho (wordOrderRejectedWeight N t cs T H δ K)
  let E := eta0*(N : ℝ)/(Real.log (N : ℝ))^A
  have heach : ∀ cs ∈ L, |f cs| ≤ E := by
    intro cs hcs
    exact hword t ht cs (le_listMomentOrder hcs) Q rho T H δ K hQ hrho hδ hδmesh
  have hsum : ∀ W : List (List ℕ), (∀ cs ∈ W, |f cs| ≤ E) →
      |(W.map f).sum| ≤ (W.length : ℝ)*E := by
    intro W
    induction W with
    | nil => intro _; simp
    | cons cs W ih =>
        intro hW
        have hc := hW cs (List.mem_cons_self cs W)
        have hw := ih (fun ds hds => hW ds (List.mem_cons_of_mem cs hds))
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        exact (abs_add (f cs) ((W.map f).sum)).trans ((add_le_add hc hw).trans_eq (by ring))
  have hcoefficient : (L.length : ℝ)*eta0 ≤ eta := by
    dsimp [eta0]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (L.length : ℝ)+1)).mpr
    nlinarith
  calc
    _ ≤ (L.length : ℝ)*E := hsum L heach
    _ = ((L.length : ℝ)*eta0)*((N : ℝ)/(Real.log (N : ℝ))^A) := by dsimp [E]; ring
    _ ≤ eta*((N : ℝ)/(Real.log (N : ℝ))^A) :=
      mul_le_mul_of_nonneg_right hcoefficient
        (div_nonneg (Nat.cast_nonneg N) (pow_nonneg hlog0 A))
    _ = _ := by ring

def wordRemainingRejectedWeight (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (x : Label) : ℝ :=
  if cs=[] then 0 else smoothTrim T (product (t.1*t.2) x) *
    rawRemainingRejectedWeight N t H δ K x

theorem wordRemaining_eq_upper_add_order (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (x : Label) :
    wordRemainingRejectedWeight N t cs T H δ K x =
      wordUpperRejectedWeight N t cs T H δ K x+
        wordOrderRejectedWeight N t cs T H δ K x := by
  by_cases hcs : cs=[]
  · simp [wordRemainingRejectedWeight,wordUpperRejectedWeight,wordOrderRejectedWeight,hcs]
  · simp only [wordRemainingRejectedWeight,wordUpperRejectedWeight,
      wordOrderRejectedWeight,if_neg hcs,remaining_eq_upper_add_order,mul_add]

def originalRemainingRejectedError (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map (fun cs => wordError N t cs Q rho
    (wordRemainingRejectedWeight N t cs T H δ K))).sum

/-- The error now paid is literally Q16's remaining upper/order term,
with the same trim, signed rho, original labels and occurrence list. -/
theorem originalRemainingRejectedError_eq_upper_add_order
    (N : ℕ) (t : ℕ × ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (T H δ : ℝ) (K : ℕ) :
    originalRemainingRejectedError N t Q rho T H δ K =
      originalUpperRejectedError N t Q rho T H δ K+
        originalOrderRejectedError N t Q rho T H δ K := by
  have hword (cs : List ℕ) :
      wordError N t cs Q rho (wordRemainingRejectedWeight N t cs T H δ K) =
        wordError N t cs Q rho (wordUpperRejectedWeight N t cs T H δ K)+
          wordError N t cs Q rho (wordOrderRejectedWeight N t cs T H δ K) := by
    simp only [wordError,wordRemaining_eq_upper_add_order,add_mul,
      Finset.sum_add_distrib,mul_add]
  have hlist (L : List (List ℕ)) :
      (L.map (fun cs => wordError N t cs Q rho (wordRemainingRejectedWeight N t cs T H δ K))).sum =
        (L.map (fun cs => wordError N t cs Q rho (wordUpperRejectedWeight N t cs T H δ K))).sum+
          (L.map (fun cs => wordError N t cs Q rho (wordOrderRejectedWeight N t cs T H δ K))).sum := by
    induction L with
    | nil => simp
    | cons cs L ih => simp only [List.map_cons,List.sum_cons,hword,ih]; ring
  exact hlist originalMotherOccurrences

theorem upperMeshExponent_le_orderMeshExponent (J A : ℕ) :
    upperMeshExponent J A ≤ orderMeshExponent J A := by
  have hE : 15 ≤ kernelMomentExponent J := le_max_right _ _
  unfold upperMeshExponent orderMeshExponent
  omega

/-- FULL upper/order rejection payment on the exact source, using ONE
common logarithmic mesh chosen before N. Q16 separately owns the lower
complete-product error. The remaining external t-sum is not claimed. -/
theorem eventually_original_remainingRejected_logAccuracy (A : ℕ) (eta : ℝ)
    (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (t : ℕ × ℕ), t ∈ pairSupport N →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) → 0 < δ →
      δ ≤ boundaryLogMesh
        (orderMeshExponent (listMomentOrder originalMotherOccurrences) A) N →
      |originalRemainingRejectedError N t Q rho T H δ K| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_original_upperRejected_logAccuracy A (eta/2) (half_pos heta),
    eventually_original_orderRejected_logAccuracy A (eta/2) (half_pos heta),
    eventually_one_le_nat_log] with N hupper horder hlog
  intro t ht Q rho T H δ K hQ hrho hδ hmesh
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hmeshupper : δ ≤ boundaryLogMesh
      (upperMeshExponent (listMomentOrder originalMotherOccurrences) A) N := by
    apply hmesh.trans
    unfold boundaryLogMesh
    exact one_div_le_one_div_of_le (pow_pos hlogpos _)
      (pow_le_pow_right₀ hlog (upperMeshExponent_le_orderMeshExponent _ _))
  rw [originalRemainingRejectedError_eq_upper_add_order]
  exact (abs_add _ _).trans ((add_le_add
    (hupper t ht Q rho T H δ K hQ hrho hmeshupper)
    (horder t ht Q rho T H δ K hQ hrho hδ hmesh)).trans_eq (by ring))

end
end ImbalancedChen.P2GammaOrderingStripPayment
