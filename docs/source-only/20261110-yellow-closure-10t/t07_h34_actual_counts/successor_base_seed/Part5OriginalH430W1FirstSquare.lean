import ImbalancedChen.Part5OriginalH430W1TrueConvertedBase
import ImbalancedChen.P2EnhancedW1FixedPowerLabelMultiplicity

/-! The literal mask (d*N)*first at the middle prime.  Only the first
new letter can hide a prime below that middle cutoff in the actual tail.
The labelled incidence bound is charged to the genuine old quotient. -/
namespace ImbalancedChen.Part5OriginalH430W1FirstSquare
noncomputable section
open Set Finset Real Wu2008DoubleSieve
open P5OriginalU5FrozenSource (receiver receiver_quotient_coprime)
open P2AllW1FrozenReceiverFiniteAction (rawTripleCount)
open P2FrozenReceiverCountActions (quotientCount)
open P2LargerSActualPositiveCounts (historyCarrier)
open P2EnhancedW1SquareExceptionPower (squareEvent weightedSquareEvent weightedSquareEvent_theta_payment)
open P2EnhancedW1FixedPowerLabelMultiplicity (prime_factor_fibre_card_le_inv_power)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open scoped Classical BigOperators

abbrev TWord := ℕ × ℕ × ℕ

def prod (t : TWord) : ℕ := t.1*t.2.1*t.2.2
def tail (N d ell : ℕ) (t : TWord) : ℕ := (N-ell)/(d*prod t)
def oldCarrier (N d : ℕ) (z : ℝ) : Finset ℕ := historyCarrier N d (fun _ => receiver N) z
def words (N d ell : ℕ) (z w : ℝ) : Finset TWord :=
  (orderedTriples (primeWindow (d*N) z w)).filter
    (tripleSurvives (primeWindow (d*N) z w) ((N-ell)/d))
def bad (N d ell : ℕ) (z w : ℝ) : Finset TWord :=
  (words N d ell z w).filter (fun t => ¬ChenPrimeRough (t.2.1:ℝ) (tail N d ell t))

/-- This positive family defines its own additive prime label, old-product
divisibility, absolute inclusive rough tail, and all three distinct labels. -/
def cleanCount (N d : ℕ) (z w : ℝ) : ℝ :=
  ∑ t∈orderedTriples (primeWindow (d*N) z w),
    (((chenAdditivePrimeCarrier N).filter (fun ell => d*prod t∣N-ell ∧
      ChenPrimeRough (t.2.1:ℝ) (tail N d ell t))).card:ℝ)

private theorem raw_mem {N d ell : ℕ} {z w : ℝ} {t : TWord}
    (ht : t∈orderedTriples (primeWindow (d*N) z w)) :
    ell∈oldCarrier N d z ∧ t∈words N d ell z w ↔
      ell∈(sieveCarrier N (d*prod t) ((d*N)*t.1) (t.2.1:ℝ)).filter (receiver N) := by
  rcases t with ⟨a,b,c⟩
  rw [show prod (a,b,c)=a*b*c from rfl,←tripleCarrier_eq N d (d*N) ht]
  simp only [oldCarrier,historyCarrier,words,mem_filter,ht,true_and]
  tauto

private theorem prime_mem {N d ell : ℕ} {z w : ℝ} {t : TWord}
    (ht : t∈orderedTriples (primeWindow (d*N) z w)) :
    (ell∈oldCarrier N d z ∧ t∈words N d ell z w ∧ ChenPrimeRough (t.2.1:ℝ) (tail N d ell t)) ↔
      ell∈(chenAdditivePrimeCarrier N).filter (fun ell =>
        d*prod t∣N-ell ∧ ChenPrimeRough (t.2.1:ℝ) (tail N d ell t)) := by
  rw [mem_filter,mem_chenAdditivePrimeCarrier_iff_le]
  constructor
  · rintro ⟨ha,hw,hr⟩
    obtain ⟨hx,hcop⟩ := mem_filter.mp ((raw_mem ht).mp ⟨ha,hw⟩)
    obtain ⟨hb,hpr,hdiv,_⟩ := mem_filter.mp hx
    exact ⟨⟨Nat.lt_succ_iff.mp (mem_range.mp hb),hpr,hcop⟩,hdiv,hr⟩
  · rintro ⟨⟨hle,hpr,hcop⟩,hdiv,hr⟩
    have hm : ell∈(sieveCarrier N (d*prod t) ((d*N)*t.1) (t.2.1:ℝ)).filter (receiver N) :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_iff.mpr hle),hpr,hdiv,
        fun r hp _ hlt hdiv => (not_lt_of_ge (hr r hp hdiv)) hlt⟩,hcop⟩
    exact ⟨((raw_mem ht).mpr hm).1,((raw_mem ht).mpr hm).2,hr⟩

private theorem flip_cards {ι κ : Type*} (A : Finset ι) (B : Finset κ) (F : ι → κ → Prop)
    :
    (∑ i∈A,((B.filter (F i)).card:ℝ))=∑ j∈B,((A.filter (fun i => F i j)).card:ℝ) := by
  classical
  simp only [card_eq_sum_ones,Nat.cast_sum,Nat.cast_one,sum_filter]
  rw [sum_comm]

theorem raw_split (N d : ℕ) (z w : ℝ) :
    (rawTripleCount N d (d*N) (receiver N) z w:ℝ)=
      cleanCount N d z w+∑ ell∈oldCarrier N d z,((bad N d ell z w).card:ℝ) := by
  let A := oldCarrier N d z
  let T := orderedTriples (primeWindow (d*N) z w)
  let F := fun ell t => t∈words N d ell z w
  let R := fun ell t => ChenPrimeRough (t.2.1:ℝ) (tail N d ell t)
  have hraw : (rawTripleCount N d (d*N) (receiver N) z w:ℝ)=∑ ell∈A,((words N d ell z w).card:ℝ) := by
    unfold rawTripleCount quotientCount
    push_cast
    calc
      _ = ∑ t∈T,((A.filter (fun ell => F ell t)).card:ℝ) := by
        apply sum_congr rfl
        intro t ht
        congr 2
        ext ell
        exact (raw_mem ht).symm.trans mem_filter.symm
      _ = ∑ ell∈A,((T.filter (F ell)).card:ℝ) := flip_cards T A (fun t ell => F ell t)
      _ = _ := by
        apply sum_congr rfl
        intro ell _
        congr 2
        ext t
        exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨(mem_filter.mp h).1,h⟩⟩
  have hclean : cleanCount N d z w=∑ ell∈A,(((words N d ell z w).filter (R ell)).card:ℝ) := by
    unfold cleanCount
    calc
      _ = ∑ t∈T,((A.filter (fun ell => F ell t ∧ R ell t)).card:ℝ) := by
        apply sum_congr rfl
        intro t ht
        congr 2
        ext ell
        exact (prime_mem ht).symm.trans mem_filter.symm
      _ = ∑ ell∈A,((T.filter (fun t => F ell t ∧ R ell t)).card:ℝ) :=
        flip_cards T A (fun t ell => F ell t ∧ R ell t)
      _ = _ := by
        apply sum_congr rfl
        intro ell _
        congr 2
        ext t
        rw [mem_filter,mem_filter]
        exact ⟨fun h => h.2,fun h => ⟨(mem_filter.mp h.1).1,h⟩⟩
  rw [hraw,hclean,←sum_add_distrib]
  apply sum_congr rfl
  intro ell _
  exact_mod_cast (card_filter_add_card_filter_not (s:=words N d ell z w) (R ell)).symm

private theorem old_label {N d ell : ℕ} {z : ℝ} (he : ell∈oldCarrier N d z) :
    ell∈chenAdditivePrimeCarrier N ∧ d∣N-ell := by
  obtain ⟨hx,hcop⟩ := mem_filter.mp he
  obtain ⟨hbound,hpr,hdiv,_⟩ := mem_filter.mp hx
  exact ⟨mem_chenAdditivePrimeCarrier_iff_le.mpr ⟨Nat.lt_succ_iff.mp (mem_range.mp hbound),hpr,hcop⟩,hdiv⟩

/-- Failure of absolute tail roughness forces a second copy of the first
new prime in this same positive old quotient. -/
theorem bad_mem_square {N d ell : ℕ} {z w y : ℝ} {t : TWord}
    (hrough : ChenPrimeRough w d) (hy : y≤z) (he : ell∈oldCarrier N d z)
    (ht : t∈bad N d ell z w) :
    ell∈squareEvent N d (fun _ => receiver N) z y := by
  obtain ⟨hw,hbad⟩ := mem_filter.mp ht
  obtain ⟨ht',hsurv⟩ := mem_filter.mp hw
  obtain ⟨hcart,hab,hbc⟩ := mem_filter.mp ht'
  obtain ⟨ha,hpair⟩ := mem_product.mp hcart
  obtain ⟨hb,hc⟩ := mem_product.mp hpair
  obtain ⟨hpr,_,haz,_⟩ := mem_primeWindow.mp ha
  have hbw := (mem_primeWindow.mp hb).2.2.2
  have hlabel := old_label he
  have hdivs := mem_filter.mp (mem_filter.mp ((raw_mem ht').mp ⟨he,hw⟩)).1
  have hdiv : d*prod t ∣ N-ell := hdivs.2.2.1
  have hsift : Sifted ((d*N)*t.1) (tail N d ell t) (t.2.1:ℝ) := hdivs.2.2.2
  have hcop := receiver_quotient_coprime hlabel.1 hdiv
  change ¬∀ q : ℕ,q.Prime → q∣tail N d ell t → (t.2.1:ℝ)≤(q:ℝ) at hbad
  push_neg at hbad
  obtain ⟨r,hr,hrm,hrb⟩ := hbad
  have hrd : r.Coprime d := hr.coprime_iff_not_dvd.mpr
    (fun h => (not_lt_of_ge (hrough r hr h)) (hrb.trans hbw))
  have hrN : r.Coprime N := hcop.of_dvd_left hrm
  have hfirst : r=t.1 := by
    by_contra hne
    exact hsift r hr (Nat.coprime_mul_iff_right.mpr ⟨Nat.coprime_mul_iff_right.mpr ⟨hrd,hrN⟩,
      (Nat.coprime_primes hr hpr).mpr hne⟩) hrb hrm
  subst r
  have hpt : prod t∣(N-ell)/d := (Nat.dvd_div_iff_mul_dvd hlabel.2).mpr hdiv
  have heq : prod t*tail N d ell t=(N-ell)/d := by
    rw [tail,←Nat.div_div_eq_div_mul]
    exact Nat.mul_div_cancel' hpt
  obtain ⟨u,hu⟩ := hrm
  refine mem_filter.mpr ⟨he,(mem_chenAdditivePrimeCarrier.mp hlabel.1).1,t.1,hpr,hy.trans haz,?_⟩
  refine ⟨t.2.1*t.2.2*u,?_⟩
  rw [←heq,hu,prod]
  ring

theorem bad_fibre {N d ell : ℕ} {z w η : ℝ} (hN : 1<N) (hη : 0<η)
    (hz : (N:ℝ)^η≤z) (hrough : ChenPrimeRough w d) (he : ell∈oldCarrier N d z) :
    ((bad N d ell z w).card:ℝ) ≤
      if ell∈squareEvent N d (fun _ => receiver N) z ((N:ℝ)^η) then (1/η)^3 else 0 := by
  by_cases hh : (bad N d ell z w).Nonempty
  · obtain ⟨t,ht⟩ := hh
    rw [if_pos (bad_mem_square hrough hz he ht)]
    let P := (primeWindow (d*N) z w).filter (fun r => r∣(N-ell)/d)
    have hinc : bad N d ell z w ⊆ P ×ˢ (P ×ˢ P) := by
      intro v hv
      obtain ⟨hw,_⟩ := mem_filter.mp hv
      obtain ⟨ht',hv'⟩ := mem_filter.mp hw
      obtain ⟨hcart,_⟩ := mem_filter.mp ht'
      obtain ⟨ha,hbc⟩ := mem_product.mp hcart
      obtain ⟨hb,hc⟩ := mem_product.mp hbc
      exact mem_product.mpr ⟨mem_filter.mpr ⟨ha,hv'.1⟩,mem_product.mpr
        ⟨mem_filter.mpr ⟨hb,hv'.2.1⟩,mem_filter.mpr ⟨hc,hv'.2.2.1⟩⟩⟩
    have he' := old_label he
    have hq : (N-ell)/d∈chenQuotientPrimeSource N d := mem_image.mpr
      ⟨ell,mem_chenQuotientPrimeCarrier.mpr he',rfl⟩
    obtain ⟨hn,hnN,_⟩ := chenQuotientPrimeSource_data hq
    have hsize := prime_factor_fibre_card_le_inv_power N ((N-ell)/d) P η hN hn hnN
      (fun q hq => Nat.mem_primeFactors.mpr
        ⟨(mem_primeWindow.mp (mem_filter.mp hq).1).1,(mem_filter.mp hq).2,hn.ne'⟩)
      hη (fun q hq => hz.trans (mem_primeWindow.mp (mem_filter.mp hq).1).2.2.1)
    have hcount : (bad N d ell z w).card ≤ P.card^3 := by
      simpa [card_product,pow_succ,mul_assoc] using card_le_card hinc
    exact (show ((bad N d ell z w).card:ℝ)≤(P.card:ℝ)^3 by exact_mod_cast hcount).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hsize 3)
  · rw [not_nonempty_iff_eq_empty.mp hh,card_empty,Nat.cast_zero]
    split_ifs <;> positivity

/-- The labelled square exception, retaining all old receivers, is
uniformly negligible relative to the same one-word physical Theta. -/
theorem true_clean_count {η ε : ℝ} (hη : 0<η) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q : ℝ) (d : ℕ) (z w : ℝ),
      0<d → 1<Q/(d:ℝ) → Q/(d:ℝ)≤N → (N:ℝ)^η≤z → ChenPrimeRough w d →
      (rawTripleCount N d (d*N) (receiver N) z w:ℝ) ≤ cleanCount N d z w+ε*thetaAtom N Q d := by
  let C : ℝ := (1/η)^3
  have hC : 0<C := by dsimp only [C]; positivity
  obtain ⟨T,h4,hT⟩ := weightedSquareEvent_theta_payment hη (div_pos he hC)
  refine ⟨T,h4,?_⟩
  intro N hN Q d z w hd hR hR' hz hr
  let E := squareEvent N d (fun _ => receiver N) z ((N:ℝ)^η)
  let A := oldCarrier N d z
  have hpay := hT N hN Q {d} (fun _ => (1:ℝ)) (fun _ => receiver N) (fun _ => z)
    (by simpa using hd) (by simp) (by simpa using And.intro hR hR')
  simp only [weightedSquareEvent,Theta_eq_sum_atoms,sum_singleton,one_mul] at hpay
  have hfilter : A.filter (fun ell => ell∈E) ⊆ E := fun _ hm => (mem_filter.mp hm).2
  have hc : ((A.filter (fun ell => ell∈E)).card:ℝ)≤(E.card:ℝ) := by exact_mod_cast card_le_card hfilter
  have hsum : (∑ ell∈A,((bad N d ell z w).card:ℝ))≤C*(E.card:ℝ) := by
    calc
      _ ≤ ∑ ell∈A,if ell∈E then C else 0 := sum_le_sum (fun ell h => bad_fibre (by omega) hη hz hr h)
      _ = C*((A.filter (fun ell => ell∈E)).card:ℝ) := by
        rw [←sum_filter]; simp [mul_comm,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hC.le
  have hh := mul_le_mul_of_nonneg_left hpay hC.le
  have hs : C*((ε/C)*thetaAtom N Q d)=ε*thetaAtom N Q d := by field_simp [hC.ne']
  rw [hs] at hh
  rw [raw_split]
  exact add_le_add_left (hsum.trans hh) _

end
end ImbalancedChen.Part5OriginalH430W1FirstSquare
