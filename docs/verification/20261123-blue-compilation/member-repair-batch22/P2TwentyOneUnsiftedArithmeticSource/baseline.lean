import ImbalancedChen.P2EnhancedTwentyOneQuotientFinite
import ImbalancedChen.P5zPositiveFamilyBudget
import ImbalancedChen.P2EnhancedCollisionFloorBound

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Independent arithmetic source for ALL original Gamma7--21 prefix words,
at their original arities, colours and list multiplicities. The tail is
the exact quotient of N-ell by d*l.prod. Its original Sifted(d*N) mask
is retained; it is not silently replaced by absolute roughness. Additive
primality is restored only in the primeMass receiver. No K/PP licence,
whole-group capacity, normalized J or cost integral is assumed here.
-/
namespace ImbalancedChen.P2TwentyOneUnsiftedArithmeticSource
noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2EnhancedPrefixMaskDefect (quotientCarrier)
open P2EnhancedTwentyOneQuotientFinite (quotientPrefixTerm quotientSwitched)

abbrev Label := List ℕ × ℕ
abbrev SourceLabel := Sigma (fun _l : List ℕ => ℕ)

def words (M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : Finset (List ℕ) :=
  (secondFunctionalMotherTuples (primeWindow M a f) cs.length).filter
    (fun l => l.map (secondFunctionalMotherColour b c e)=cs)

def product (d : ℕ) (x : Label) : ℕ := d*x.1.prod*x.2

def threshold (l : List ℕ) : ℝ := l.getD (l.length-2) 0

def Geometry (N d : ℕ) (x : Label) : Prop :=
  0<x.2 ∧ Sifted (d*N) x.2 (threshold x.1) ∧ product d x<N

def arithmeticLabels (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : Finset Label :=
  ((words M a b c e f cs).product (Finset.range (N+1))).filter (Geometry N d)

def sourceLabels (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : Finset SourceLabel :=
  (words M a b c e f cs).sigma (fun l => quotientCarrier N d l)

def encode (N d : ℕ) (x : SourceLabel) : Label := (x.1,(N-x.2)/(d*x.1.prod))

def restoredLabels (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : Finset Label :=
  (arithmeticLabels N d M a b c e f cs).filter (fun x => Nat.Prime (N-product d x))

theorem word_prod_pos {M : ℕ} {a b c e f : ℝ} {cs l : List ℕ}
    (hl : l ∈ words M a b c e f cs) : 0<l.prod := by
  have hm := ((secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hl).1).2.2
  apply List.prod_pos
  intro p hp
  exact (mem_primeWindow.mp (hm p hp)).1.pos

theorem source_output_lt {N d ell : ℕ} {l : List ℕ}
    (hN : 4≤N) (he : Even N) (hell : ell ∈ quotientCarrier N d l) : ell<N := by
  obtain ⟨hrange,hprime,_hdiv,_hsift⟩ := Finset.mem_filter.mp hell
  exact omega3_prime_output_lt hN he hprime (Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange))

theorem encode_source {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hN : 4≤N) (he : Even N) (hd : 0<d) {x : SourceLabel}
    (hx : x ∈ sourceLabels N d M a b c e f cs) :
    encode N d x ∈ arithmeticLabels N d M a b c e f cs ∧
    product d (encode N d x)=N-x.2 ∧ Nat.Prime (N-product d (encode N d x)) := by
  obtain ⟨hw,hell⟩ := Finset.mem_sigma.mp hx
  obtain ⟨hrange,hprime,hdiv,hsift⟩ := Finset.mem_filter.mp hell
  have hlt := source_output_lt hN he hell
  have hD : 0<d*x.1.prod := mul_pos hd (word_prod_pos hw)
  have hm : product d (encode N d x)=N-x.2 := Nat.mul_div_cancel' hdiv
  have hn : 0<(encode N d x).2 := by
    have hp : 0<N-x.2 := Nat.sub_pos_of_lt hlt
    by_contra hn
    have hz : (encode N d x).2=0 := by omega
    rw [← hm] at hp
    simp only [product,hz,mul_zero,lt_self_iff_false] at hp
  have hpos : 0<product d (encode N d x) := mul_pos hD hn
  have hmN : product d (encode N d x)<N := by rw [hm]; exact Nat.sub_lt (by omega) hprime.pos
  have hnN : (encode N d x).2≤N :=
    (Nat.le_of_dvd hpos (dvd_mul_left _ _)).trans hmN.le
  have hr : N-product d (encode N d x)=x.2 := by rw [hm]; omega
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hw,Finset.mem_range.mpr (Nat.lt_succ_of_le hnN)⟩,hn,hsift,hmN⟩,hm,?_⟩
  simpa only [hr] using hprime

theorem arithmetic_restores_source {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hd : 0<d) {x : Label} (hx : x ∈ arithmeticLabels N d M a b c e f cs)
    (hprime : Nat.Prime (N-product d x)) :
    (⟨x.1,N-product d x⟩ : SourceLabel) ∈ sourceLabels N d M a b c e f cs ∧
    encode N d ⟨x.1,N-product d x⟩=x := by
  obtain ⟨hambient,hg⟩ := Finset.mem_filter.mp hx
  have hw := (Finset.mem_product.mp hambient).1
  have hD : 0<d*x.1.prod := mul_pos hd (word_prod_pos hw)
  have hm : N-(N-product d x)=product d x := Nat.sub_sub_self hg.2.2.le
  have hquot : (N-(N-product d x))/(d*x.1.prod)=x.2 := by
    rw [hm]
    exact Nat.mul_div_cancel_left x.2 hD
  refine ⟨Finset.mem_sigma.mpr ⟨hw,Finset.mem_filter.mpr ⟨?_,hprime,?_,?_⟩⟩,?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · rw [hm]
    exact dvd_mul_right _ _
  · simpa only [hquot] using hg.2.1
  · exact Prod.ext rfl hquot

/-- Literal receiver labels and independent arithmetic labels are in
bijection. Equal products, repeated Gamma occurrences and n=1 remain. -/
theorem source_card_eq_restored {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hN : 4≤N) (he : Even N) (hd : 0<d) :
    (sourceLabels N d M a b c e f cs).card=(restoredLabels N d M a b c e f cs).card := by
  refine Finset.card_bij (fun x _ => encode N d x) ?_ ?_ ?_
  · intro x hx
    have hh := encode_source hN he hd hx
    exact Finset.mem_filter.mpr ⟨hh.1,hh.2.2⟩
  · intro x hx y hy hxy
    rcases x with ⟨l,ell⟩
    rcases y with ⟨l',ell'⟩
    have hw : l=l' := congrArg Prod.fst hxy
    have hm := congrArg (product d) hxy
    rw [(encode_source hN he hd hx).2.1,(encode_source hN he hd hy).2.1] at hm
    have hlx := source_output_lt hN he (Finset.mem_sigma.mp hx).2
    have hly := source_output_lt hN he (Finset.mem_sigma.mp hy).2
    have hel : ell=ell' := by omega
    subst l'
    subst ell'
    rfl
  · intro x hx
    obtain ⟨ha,hp⟩ := Finset.mem_filter.mp hx
    exact ⟨⟨x.1,N-product d x⟩,(arithmetic_restores_source hd ha hp).1,
      (arithmetic_restores_source hd ha hp).2⟩

theorem source_card_eq_quotientPrefixTerm (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    ((sourceLabels N d M a b c e f cs).card : ℝ)=quotientPrefixTerm N d M a b c e f cs := by
  calc
    _ = ∑ l ∈ words M a b c e f cs,((quotientCarrier N d l).card : ℝ) := by
      simp only [sourceLabels,Finset.card_sigma,Nat.cast_sum]
    _ = _ := by rw [words,Finset.sum_filter]; rfl

theorem primeMass_eq_restored (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) (sigma : ℝ) :
    p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N = sigma*((restoredLabels N d M a b c e f cs).card : ℝ) := by
  have hs : p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
      (fun _ => sigma) N = ∑ _x ∈ restoredLabels N d M a b c e f cs,sigma := by
    unfold p5z_labelledPrimeMass restoredLabels
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    have hm := (Finset.mem_filter.mp hx).2.2.2
    by_cases hp : Nat.Prime (N-product d x)
    · simp only [if_pos hp,if_pos ⟨hm,hp⟩]
    · simp only [if_neg hp,if_neg (show ¬(product d x<N ∧ Nat.Prime (N-product d x))
        from fun h => hp h.2)]
  rw [hs]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

/-- Exact independent source for every original prefix colour word,
at its original arity, with no additive-prime condition in the source. -/
theorem quotientPrefixTerm_eq_primeMass {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hN : 4≤N) (he : Even N) (hd : 0<d) (sigma : ℝ) :
    sigma*quotientPrefixTerm N d M a b c e f cs =
      p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
        (fun _ => sigma) N := by
  rw [primeMass_eq_restored,← source_card_eq_restored hN he hd,
    source_card_eq_quotientPrefixTerm]

def switchedPrimeMass (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map fun cs =>
      p5z_labelledPrimeMass (arithmeticLabels N d M a b c e f cs) (product d)
        (fun _ => 1) N).sum).sum

/-- ALL original Gamma7--21 words and LIST multiplicities are retained.
This is a count identity, not a full K or PP licence. -/
theorem quotientSwitched_eq_switchedPrimeMass {N d M : ℕ} {a b c e f : ℝ}
    (hN : 4≤N) (he : Even N) (hd : 0<d) :
    quotientSwitched N d M a b c e f=switchedPrimeMass N d M a b c e f := by
  unfold quotientSwitched switchedPrimeMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs hcs
  simpa only [one_mul] using
    (quotientPrefixTerm_eq_primeMass (N:=N) (d:=d) (M:=M)
      (a:=a) (b:=b) (c:=c) (e:=e) (f:=f) (cs:=cs) hN he hd 1)

end
end ImbalancedChen.P2TwentyOneUnsiftedArithmeticSource
