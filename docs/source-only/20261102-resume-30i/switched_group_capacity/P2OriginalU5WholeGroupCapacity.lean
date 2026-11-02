import ImbalancedChen.P2OriginalU5SmallPartnerRootPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The three ORIGINAL arithmetic groups at the actual U5 root are d=p*q,
the entire specified Gamma word, and the exact positive quotient n.
This proves their whole-product floors and the complementary tail capacity.
The complete canonical word has a fixed power floor and rank at most199
after one threshold chosen before the pair, Gamma word and source label.

These are source-product capacities, not D-well modulus support or the
three Restricted Medium monomials. In particular no full square test for
the complete positive switched word is inferred from its product<N.
-/
namespace ImbalancedChen.P2OriginalU5WholeGroupCapacity
noncomputable section
open Finset Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2TwentyOneUnsiftedArithmeticSource
open P2TwentyOneMaskedTailFloor
open P2OriginalU5SmallPartnerRootPayment
open P5OriginalU5CausalFinite (pairSupport coordinates originalResidual)

/-- The actual independent good source used by H, at all original arities. -/
def rootLabels (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ) : Finset Label :=
  absoluteGoodLabels N (t.1*t.2) N
    (cutoff (rootQ N t) (t.1*t.2) (227/50))
    (cutoff (rootQ N t) (t.1*t.2) (353/100))
    (cutoff (rootQ N t) (t.1*t.2) (29/10))
    (cutoff (rootQ N t) (t.1*t.2) (61/25))
    (cutoff (rootQ N t) (t.1*t.2) (11/5)) cs (smallCap N)

theorem rootLabels_data {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ} {x : Label}
    (hx : x ∈ rootLabels N t cs) :
    x.1 ∈ words N
      (cutoff (rootQ N t) (t.1*t.2) (227/50))
      (cutoff (rootQ N t) (t.1*t.2) (353/100))
      (cutoff (rootQ N t) (t.1*t.2) (29/10))
      (cutoff (rootQ N t) (t.1*t.2) (61/25))
      (cutoff (rootQ N t) (t.1*t.2) (11/5)) cs ∧
      0<x.2 ∧ GoodTail (smallCap N) x ∧ product (t.1*t.2) x<N := by
  obtain ⟨ha,hpos,hfloor,hprod⟩ := Finset.mem_filter.mp hx
  exact ⟨(Finset.mem_product.mp ha).1,hpos,hfloor,hprod⟩

theorem root_word_length {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ} {x : Label}
    (hx : x ∈ rootLabels N t cs) : x.1.length=cs.length :=
  ((secondFunctionalMother_tuple_mem _ _ _).mp
    (Finset.mem_filter.mp (rootLabels_data hx).1).1).1

/-- Stronger than H's auxiliary1/100: this is the actual lowest cutoff
floor supplied by the original residual34/125 and original parameter227/50. -/
theorem root_specified_cutoff_floor {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    (N : ℝ)^(68/1135 : ℝ)≤cutoff (rootQ N t) (t.1*t.2) (227/50) := by
  have hr := (P5OriginalU5CausalFinite.original_geometry hN ht).1
  change (34/125 : ℝ)≤originalResidual N t at hr
  unfold cutoff
  rw [root_residual_identity (by omega) ht,← Real.rpow_mul (Nat.cast_nonneg N)]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
  norm_num
  linarith

theorem specified_prime_floor {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {cs : List ℕ} {x : Label}
    (hx : x ∈ rootLabels N t cs) :
    ∀ p ∈ x.1,(N : ℝ)^(68/1135 : ℝ)≤(p : ℝ) := by
  have hm := ((secondFunctionalMother_tuple_mem _ _ _).mp
    (Finset.mem_filter.mp (rootLabels_data hx).1).1).2.2
  intro p hp
  exact (root_specified_cutoff_floor hN ht).trans
    (mem_primeWindow.mp (hm p hp)).2.2.1

private theorem list_floor_product (w : List ℕ) (z : ℝ) (hz : 0≤z)
    (hw : ∀ p ∈ w,z≤(p : ℝ)) : z^w.length≤(w.prod : ℝ) := by
  revert hw
  induction w with
  | nil => intro _; simp
  | cons p w ih =>
      intro hw
      rw [List.length_cons,pow_succ,List.prod_cons,Nat.cast_mul]
      calc
        z^w.length*z≤(w.prod : ℝ)*(p : ℝ) :=
          mul_le_mul (ih (fun q hq => hw q (List.mem_cons_of_mem p hq)))
            (hw p (List.mem_cons_self p w)) hz (Nat.cast_nonneg _)
        _=_ := mul_comm _ _

/-- Capacity is paid by the WHOLE specified group: the arity multiplies
the exponent. It is not replaced by the largest individual source prime. -/
theorem specified_group_floor {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {cs : List ℕ} {x : Label}
    (hx : x ∈ rootLabels N t cs) :
    (N : ℝ)^((68/1135 : ℝ)*(cs.length : ℝ))≤(x.1.prod : ℝ) := by
  have hf := list_floor_product x.1 ((N : ℝ)^(68/1135 : ℝ))
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) (specified_prime_floor hN ht hx)
  rw [Real.rpow_mul (Nat.cast_nonneg N),Real.rpow_natCast,← root_word_length hx]
  exact hf

/-- The original pair is one complete old group; both primes pay its floor. -/
theorem old_group_floor {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    (N : ℝ)^(417/2500 : ℝ)≤((t.1*t.2 : ℕ) : ℝ) := by
  have hp : (N : ℝ)^(417/5000 : ℝ)≤(t.1 : ℝ) := (Finset.mem_filter.mp ht).2.1
  have hpq : (t.1 : ℝ)≤t.2 := by exact_mod_cast (Finset.mem_filter.mp ht).2.2.1.le
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    _=(N : ℝ)^(417/5000 : ℝ)*(N : ℝ)^(417/5000 : ℝ) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      norm_num
    _≤(t.1 : ℝ)*(t.2 : ℝ) :=
      mul_le_mul hp (hp.trans hpq) (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg _)
    _=_ := by rw [Nat.cast_mul]

/-- Actual three-group product budget. The tail remains its complete
integer value, including1 and all repeated prime factors. -/
theorem whole_group_tail_capacity {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {cs : List ℕ} {x : Label}
    (hx : x ∈ rootLabels N t cs) :
    (x.2 : ℝ)<(N : ℝ)^(1-417/2500-(68/1135)*(cs.length : ℝ)) := by
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  let beta : ℝ := 417/2500+(68/1135)*(cs.length : ℝ)
  have hgroup : (N : ℝ)^beta≤((t.1*t.2 : ℕ) : ℝ)*(x.1.prod : ℝ) := by
    rw [show beta=417/2500+(68/1135)*(cs.length : ℝ) from rfl,Real.rpow_add hNpos]
    exact mul_le_mul (old_group_floor hN ht) (specified_group_floor hN ht hx)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg _)
  have hprod : (((t.1*t.2 : ℕ) : ℝ)*(x.1.prod : ℝ))*(x.2 : ℝ)<N := by
    have hp : (product (t.1*t.2) x : ℝ)<N := by
      exact_mod_cast (rootLabels_data hx).2.2.2
    simpa only [product,Nat.cast_mul] using hp
  have hsmall : (N : ℝ)^beta*(x.2 : ℝ)<N :=
    (mul_le_mul_of_nonneg_right hgroup (Nat.cast_nonneg _)).trans_lt hprod
  have hdiv : (x.2 : ℝ)<(N : ℝ)/(N : ℝ)^beta := by
    apply (lt_div_iff₀ (Real.rpow_pos_of_pos hNpos beta)).mpr
    simpa only [mul_comm] using hsmall
  have heq : (N : ℝ)/(N : ℝ)^beta=
      (N : ℝ)^(1-417/2500-(68/1135)*(cs.length : ℝ)) := by
    calc
      _=(N : ℝ)^1/(N : ℝ)^beta := by rw [Real.rpow_one]
      _=(N : ℝ)^(1-beta) := (Real.rpow_sub hNpos 1 beta).symm
      _=_ := by congr 1; dsimp [beta]; ring
  exact hdiv.trans_eq heq

/-- The natural floor in H's actual small split gives a genuine fixed
power floor after one threshold. No floor is silently treated as its real argument. -/
theorem eventually_smallCap_fixed_power :
    ∀ᶠ N : ℕ in atTop,(N : ℝ)^(1/200 : ℝ)≤(smallCap N : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop,(2 : ℝ)≤(N : ℝ)^(1/200 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/200)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlarge] with N hN
  have hfloor := Nat.lt_floor_add_one ((N : ℝ)^(1/100 : ℝ))
  have hsq : ((N : ℝ)^(1/200 : ℝ))^2=(N : ℝ)^(1/100 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    norm_num
  have hquadratic : (N : ℝ)^(1/200 : ℝ)+1≤(N : ℝ)^(1/100 : ℝ) := by
    nlinarith [sq_nonneg ((N : ℝ)^(1/200 : ℝ)-2)]
  change (N : ℝ)^(1/200 : ℝ)≤(Nat.floor ((N : ℝ)^(1/100 : ℝ)) : ℝ)
  linarith

/-- Every original good-source label, at every Gamma arity, has the
complete fixed floor and rank bound. No additive-prime predicate is used. -/
theorem eventually_complete_word_capacity :
    ∀ᶠ N : ℕ in atTop,∀ t ∈ pairSupport N,∀ cs : List ℕ,∀ x ∈ rootLabels N t cs,
      (completeWord (t.1*t.2) x).prod=product (t.1*t.2) x ∧
      (∀ p ∈ completeWord (t.1*t.2) x,p.Prime ∧ (N : ℝ)^(1/200 : ℝ)≤(p : ℝ)) ∧
      (completeWord (t.1*t.2) x).length≤199 := by
  filter_upwards [eventually_smallCap_fixed_power,eventually_ge_atTop (2 : ℕ)] with N hf hN
  intro t ht cs x hx
  have hdata := absoluteGood_completeWord_data (pair_product_pos ht) hx
    (root_old_prime_floor (by omega) ht)
    ((smallCap_le_power N).trans (root_lowest_cutoff_floor hN ht))
  have hfloor : ∀ p ∈ completeWord (t.1*t.2) x,(N : ℝ)^(1/200 : ℝ)≤(p : ℝ) := by
    intro p hp
    exact hf.trans (by exact_mod_cast (hdata.2 p hp).2)
  refine ⟨hdata.1,fun p hp => ⟨(hdata.2 p hp).1,hfloor p hp⟩,?_⟩
  have hpow := list_floor_product (completeWord (t.1*t.2) x)
    ((N : ℝ)^(1/200 : ℝ)) (Real.rpow_nonneg (Nat.cast_nonneg N) _) hfloor
  have hprod : ((completeWord (t.1*t.2) x).prod : ℝ)<N := by
    rw [hdata.1]
    exact_mod_cast (rootLabels_data hx).2.2.2
  have he : (N : ℝ)^((1/200 : ℝ)*((completeWord (t.1*t.2) x).length : ℝ))<(N : ℝ)^1 := by
    rw [Real.rpow_mul (Nat.cast_nonneg N),Real.rpow_natCast,Real.rpow_one]
    exact hpow.trans_lt hprod
  have hexp := (Real.rpow_lt_rpow_left_iff (by exact_mod_cast (show 1<N by omega))).mp he
  have hlen : ((completeWord (t.1*t.2) x).length : ℝ)<200 := by linarith
  have hnat : (completeWord (t.1*t.2) x).length<200 := by exact_mod_cast hlen
  omega

end
end ImbalancedChen.P2OriginalU5WholeGroupCapacity
