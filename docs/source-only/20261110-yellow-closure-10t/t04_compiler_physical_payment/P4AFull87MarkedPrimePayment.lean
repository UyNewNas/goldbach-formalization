import ImbalancedChen.P4AFull87LicensedPhysicalSupport
import ImbalancedChen.P1ActualMovingPrimeIntervalEnvelope

/-! Delete one marked prime. The other *complete* squarefree divisor,
including every prime after the marked slot, is summed once by the actual
Euler product. The interval centre may depend on this divisor and the slot. -/
namespace ImbalancedChen.P4AFull87MarkedPrimePayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport

def clip (a b x : ℝ) := max a (min b x)

private theorem width_bound {a b c R : ℝ} (hab : a ≤ b) (hR : 0 ≤ R) :
    a ≤ clip a b (c-R) ∧ clip a b (c-R) ≤ clip a b (c+2*R) ∧
    clip a b (c+2*R) ≤ b ∧ clip a b (c+2*R)-clip a b (c-R) ≤ 3*R := by
  unfold clip
  constructor
  · exact le_max_left _ _
  refine ⟨max_le_max_left _ (min_le_min_left _ (by linarith)),max_le hab (min_le_left _ _),?_⟩
  simp only [max_def,min_def]
  split_ifs <;> linarith

def window (N : ℕ) (omega v c R : ℝ) :=
  let a := clip omega v (c-R)
  let b := clip omega v (c+2*R)
  roughPrimeFinset N ⌈(N : ℝ)^b⌉₊ ((N : ℝ)^a) ((N : ℝ)^b)

def cost (t : ℕ) : ℝ := 1 / (Nat.totient t : ℝ)

def fibres (N cap J : ℕ) (omega v R : ℝ) (centre : ℕ → ℕ → ℝ) :=
  ((universe N cap ((N : ℝ)^omega) ((N : ℝ)^v)) ×ˢ Finset.range J).sigma fun x =>
    (window N omega v (centre x.1 x.2) R).filter fun p => x.1.Coprime p

abbrev Mark := Σ _x : ℕ × ℕ, ℕ
def restore (x : Mark) := x.1.1*x.2
def covered (N cap J : ℕ) (omega v R : ℝ) (centre : ℕ → ℕ → ℝ) : Finset ℕ :=
  (fibres N cap J omega v R centre).image restore

private theorem image_cost {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ t ∈ s.image f, cost t) ≤ ∑ x ∈ s, cost (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.image_insert, Finset.sum_insert hx]
    by_cases h : f x ∈ s.image f
    · rw [Finset.insert_eq_of_mem h]
      exact ih.trans (le_add_of_nonneg_left (by unfold cost; positivity))
    · rw [Finset.sum_insert h]
      exact add_le_add_left ih _

private theorem sum_fibres_le (N cap J : ℕ) (omega v R K : ℝ)
    (centre : ℕ → ℕ → ℝ) (hR : 0 ≤ R) (hw : 0 < omega) (hwv : omega ≤ v)
    (hwindow : ∀ c : ℝ, actualPrimeReciprocalMass N
      (clip omega v (c-R)) (clip omega v (c+2*R)) ≤
      3*R/omega + v*K/(omega^2*Real.log (N : ℝ))) :
    let U := universe N cap ((N : ℝ)^omega) ((N : ℝ)^v)
    (∑ d ∈ covered N cap J omega v R centre, cost d) ≤
      (∑ t ∈ U, cost t)*(J:ℝ)*(3*R/omega + v*K/(omega^2*Real.log (N : ℝ))) := by
  let U := universe N cap ((N : ℝ)^omega) ((N : ℝ)^v)
  let W := 3*R/omega + v*K/(omega^2*Real.log (N : ℝ))
  let V (x : ℕ × ℕ) := window N omega v (centre x.1 x.2) R
  have hprime (x : ℕ × ℕ) {p : ℕ} (hp : p ∈ V x) := (mem_roughPrimeFinset.mp hp).2.1
  have hlocal (x : ℕ × ℕ) :
      (∑ p ∈ (V x).filter (fun p => x.1.Coprime p), cost (x.1*p)) ≤ cost x.1*W := by
    calc
      _ = cost x.1*(∑ p ∈ (V x).filter (fun p => x.1.Coprime p), 1/((p:ℝ)-1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨hm,hcop⟩ := Finset.mem_filter.mp hp
        have hh := hprime x hm
        simp only [cost,Nat.totient_mul hcop,Nat.totient_prime hh,Nat.cast_mul,
          Nat.cast_sub hh.one_le,Nat.cast_one,one_div_mul_one_div]
      _ ≤ cost x.1*(∑ p ∈ V x, 1/((p:ℝ)-1)) := by
        apply mul_le_mul_of_nonneg_left _ (by unfold cost; positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp _
        exact one_div_nonneg.mpr (sub_nonneg.mpr (by exact_mod_cast (hprime x hp).one_le))
      _ ≤ _ := mul_le_mul_of_nonneg_left (hwindow _) (by unfold cost; positivity)
  calc
    _ ≤ ∑ y ∈ fibres N cap J omega v R centre, cost (restore y) := image_cost _ _
    _ = ∑ x ∈ U ×ˢ Finset.range J, ∑ p ∈ (V x).filter (fun p => x.1.Coprime p),
        cost (x.1*p) := Finset.sum_sigma _ _ _
    _ ≤ ∑ x ∈ U ×ˢ Finset.range J, cost x.1*W := Finset.sum_le_sum (fun x _ => hlocal x)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      calc
        _ = ∑ t ∈ U, cost t*((J:ℝ)*W) := Finset.sum_congr rfl (fun _ _ => by ring)
        _ = _ := by rw [← Finset.sum_mul]; ring

private theorem exists_full_euler :
    ∃ K : ℝ, 1 < K ∧ ∀ N cap : ℕ, Even N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
    (∑ t ∈ universe N cap w z, cost t) ≤ Real.log z/Real.log w*(1+K/Real.log w) := by
  obtain ⟨K,hK,hh⟩ := MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K,hK,?_⟩
  intro N cap hE w z hw hz
  let P := roughPrimeFinset N cap w z
  have pp (p : ℕ) (hp : p ∈ P) := roughPrimeFinset_odd_of_even hE hp
  have cop (p : ℕ) (hp : p ∈ P) : p.Coprime N :=
    (pp p hp).1.coprime_iff_not_dvd.mpr (mem_roughPrimeFinset.mp hp).2.2.1
  have hprod : P2LowerFiniteCellRounding.roughProduct N cap w z = P.prod id := by
    dsimp only [P]
    rw [P2LowerFiniteCellRounding.roughProduct, ← roughPrimeUniverse_toFinset N cap w z]
    simpa using (List.prod_toFinset (fun p : ℕ => p) (roughPrimeUniverse_nodup N cap w z)).symm
  change (∑ t ∈ (P2LowerFiniteCellRounding.roughProduct N cap w z).divisors,
    1/(Nat.totient t : ℝ)) ≤ _
  rw [hprod,reciprocalTotient_sum_divisors_primeProduct N P (fun p hp => (pp p hp).1) cop]
  exact (roughPrime_eulerProduct_le_inverseProduct N cap w z hE).trans
    (hh P pp w z hw hz (fun p hp => (mem_roughPrimeFinset.mp hp).2.2.2))

/-- Uniform in the centre of each *deleted* full divisor's moving prime
interval. K,E precede the smoothness, ranks, cap and fine width. -/
theorem exists_deletion_prime_bound :
    ∃ K E : ℝ, 1 < K ∧ 1 < E ∧ ∀ (N cap J : ℕ), 1 < N → Even N →
      ∀ omega v R : ℝ, 0 < omega → omega ≤ v → 0 ≤ R → 3 ≤ (N : ℝ)^omega →
      ∀ centre : ℕ → ℕ → ℝ,
      (∑ d ∈ covered N cap J omega v R centre, cost d) ≤
        (v/omega)*(1+E/(omega*Real.log (N:ℝ)))*(J:ℝ)*
        (3*R/omega + v*K/(omega^2*Real.log (N:ℝ))) := by
  obtain ⟨K,hK,hwin⟩ := P1ActualMovingPrimeIntervalEnvelope.exists_uniform_exponent_window_envelope
  obtain ⟨E,hE,heuler⟩ := exists_full_euler
  refine ⟨K,E,hK,hE,?_⟩
  intro N cap J hN hEven omega v R hw hv hR h3 centre
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 := zero_lt_one.trans hn
  have hl := Real.log_pos hn
  have hv0 := hw.trans_le hv
  have hbound := sum_fibres_le N cap J omega v R K centre hR hw hv (by
    intro c
    obtain ⟨ha,hab,hb,hwidth⟩ := width_bound (c := c) hv hR
    exact (hwin N hN omega v _ _ hw ha hab hb h3).trans
      (add_le_add_right (div_le_div_of_nonneg_right hwidth hw.le) _))
  have hU := heuler N cap hEven ((N:ℝ)^omega) ((N:ℝ)^v) (by linarith)
    (Real.rpow_le_rpow_of_exponent_le hn.le hv)
  rw [Real.log_rpow hn0,Real.log_rpow hn0] at hU
  have hrat : v*Real.log (N:ℝ)/(omega*Real.log (N:ℝ)) = v/omega := by
    field_simp [hw.ne',hl.ne']
  rw [hrat] at hU
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg _)) (by positivity))

/-- Perform the manuscript power count. In particular neither the number
of fine cells nor the roughness itself enters the coefficient of tau.
The 1/log N term is explicit at positive fixed omega. -/
theorem exists_normalized_marked_rate :
    ∃ K E : ℝ, 1 < K ∧ 1 < E ∧ ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      ∀ (N cap : ℕ), 1 < N → Even N → ∀ omega v tau : ℝ,
      0 < omega → omega ≤ v → v ≤ 1 → 0 ≤ tau → 3 ≤ (N : ℝ)^omega →
      E ≤ omega*Real.log (N : ℝ) → ∀ centre : ℕ → ℕ → ℝ,
      (B/omega)*(∑ d ∈ covered N cap (J0 omega) omega v
        (((J0 omega : ℝ)+C)*tau) centre, cost d) ≤
      (30*B*(5+C)*tau+10*B*K/Real.log (N : ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,hh⟩ := exists_deletion_prime_bound
  refine ⟨K,E,hK,hE,?_⟩
  intro B C hB hC N cap hN hEven omega v tau hw hv hv1 ht h3 hE' centre
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_pos hn
  have hw1 := hv.trans hv1
  have hv0 := hw.trans_le hv
  have hJ0 : 0 ≤ (J0 omega : ℝ) := Nat.cast_nonneg _
  have hJ : (J0 omega : ℝ) ≤ 5/omega := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (599/1000 : ℝ)/omega by positivity)
    dsimp only [J0]
    push_cast
    apply (le_div_iff₀ hw).mpr
    have hc := (lt_div_iff₀ hw).mp (show (⌈(599/1000 : ℝ)/omega⌉₊:ℝ)-1 < (599/1000 : ℝ)/omega by linarith)
    nlinarith
  have hcoef : (J0 omega : ℝ)+C ≤ (5+C)/omega := by
    apply (le_div_iff₀ hw).mpr
    have hj := (le_div_iff₀ hw).mp hJ
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hw1)]
  have heuler : 1+E/(omega*Real.log (N:ℝ)) ≤ 2 := by
    linarith [(div_le_one (mul_pos hw hlog)).mpr hE']
  have hrough : (v/omega)*(1+E/(omega*Real.log (N:ℝ))) ≤ (1/omega)*2 :=
    mul_le_mul (div_le_div_of_nonneg_right hv1 hw.le) heuler (by positivity) (by positivity)
  let R := ((J0 omega : ℝ)+C)*tau
  have hs := hh N cap (J0 omega) hN hEven omega v R hw hv (by positivity) h3 centre
  have hwin : 3*R/omega+v*K/(omega^2*Real.log (N:ℝ)) ≤
      3*((5+C)/omega*tau)/omega+K/(omega^2*Real.log (N:ℝ)) := by
    apply add_le_add
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoef ht) (by norm_num)) hw.le
    · exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (by linarith : 0 ≤ K) hv1)
        (by positivity)
  have hfull := mul_le_mul (mul_le_mul hrough hJ hJ0 (by positivity)) hwin
    (by dsimp only [R]; positivity) (by positivity)
  apply (mul_le_mul_of_nonneg_left (hs.trans hfull) (div_nonneg hB hw.le)).trans
  exact le_of_eq (by field_simp [hw.ne',hlog.ne']; ring)

end
end ImbalancedChen.P4AFull87MarkedPrimePayment
