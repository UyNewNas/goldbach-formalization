import ImbalancedChen.CurrentChenUpsilon7PrimeSemiprimeSource
import ImbalancedChen.PowerErrorBudget
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Sort

/-!
The actual seventh unit fibres and the two small-original-Goldbach-prime
branches have negligible cost, including the ledger coefficient two.
The positive-coordinate floor boxes retain the closed fifth-root endpoint.
The ordered semiprime branch permits repeated factors throughout.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

private theorem seventh_pair_data {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ t.1 < t.2 := by
  obtain ⟨hc, _hD, horder, _hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
  exact ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1,
    (mem_chenAdditivePrimeCarrier.mp h₂).2.1, horder⟩

private theorem seventh_pair_injOn (N : ℕ) :
    Set.InjOn (fun t : ℕ × ℕ => t.1 * t.2)
      (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) := by
  intro t ht u hu heq
  obtain ⟨h₁, h₂, horder⟩ := seventh_pair_data ht
  obtain ⟨h₃, h₄, horder'⟩ := seventh_pair_data hu
  obtain ⟨he₁, he₂⟩ := ordered_prime_factors_unique
    h₁ h₂ h₃ h₄ horder.le horder'.le heq
  exact Prod.ext he₁ he₂

private theorem seventh_pair_bound {N : ℕ} {t : ℕ × ℕ} (hN : 1 ≤ N)
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    0 < t.1 * t.2 ∧ ((t.1 * t.2 : ℕ) : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨hp₁, hp₂, horder⟩ := seventh_pair_data ht
  have hp₁R : (0 : ℝ) < t.1 := by exact_mod_cast hp₁.pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans_le hN)
  have horderR : (t.1 : ℝ) ≤ t.2 := by exact_mod_cast horder.le
  obtain ⟨_hc, _hD, _horder, hcap⟩ := Finset.mem_filter.mp ht
  have hcapsq : (t.2 : ℝ) ^ 2 < (N : ℝ) / (t.1 : ℝ) := by
    have h := (sq_lt_sq₀ (Nat.cast_nonneg t.2) (Real.sqrt_nonneg _)).mpr hcap
    rwa [Real.sq_sqrt (div_nonneg hNpos.le hp₁R.le)] at h
  have hB : (t.1 : ℝ) * (t.2 : ℝ) ^ 2 < (N : ℝ) := by
    have h := (lt_div_iff₀ hp₁R).mp hcapsq
    nlinarith only [h]
  have hcube : ((t.1 : ℝ) * (t.2 : ℝ)) ^ 3 < (N : ℝ) ^ 2 := by
    calc
      ((t.1 : ℝ) * (t.2 : ℝ)) ^ 3 =
          ((t.1 : ℝ) ^ 2 * (t.2 : ℝ) ^ 3) * (t.1 : ℝ) := by ring
      _ ≤ ((t.1 : ℝ) ^ 2 * (t.2 : ℝ) ^ 3) * (t.2 : ℝ) :=
        mul_le_mul_of_nonneg_left horderR (by positivity)
      _ = ((t.1 : ℝ) * (t.2 : ℝ) ^ 2) ^ 2 := by ring
      _ < (N : ℝ) ^ 2 := pow_lt_pow_left₀ hB (by positivity) (by decide)
  have hroot : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hNpos.le]
    norm_num
  refine ⟨mul_pos hp₁.pos hp₂.pos, ?_⟩
  rw [Nat.cast_mul]
  apply (pow_lt_pow_iff_left₀ (by positivity)
    (Real.rpow_nonneg hNpos.le _) (by decide : (3 : ℕ) ≠ 0)).mp
  rwa [hroot]

private theorem seventh_box_card {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ × ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hinj : Set.InjOn f S)
    (hbox : ∀ x ∈ S, 0 < (f x).1 ∧ ((f x).1 : ℝ) ≤ a ∧
      0 < (f x).2 ∧ ((f x).2 : ℝ) ≤ b) : (S.card : ℝ) ≤ a * b := by
  have hc : S.card ≤ (Finset.Ioc 0 (Nat.floor a) ×ˢ
      Finset.Ioc 0 (Nat.floor b)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hbox x hx
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr ⟨h₁, (Nat.le_floor_iff ha).mpr h₂⟩,
          Finset.mem_Ioc.mpr ⟨h₃, (Nat.le_floor_iff hb).mpr h₄⟩⟩
    · exact hinj
  have hcR : (S.card : ℝ) ≤ (Nat.floor a : ℝ) * (Nat.floor b : ℝ) := by
    exact_mod_cast (show S.card ≤ Nat.floor a * Nat.floor b by
      simpa only [Finset.card_product, Nat.card_Ioc, Nat.sub_zero] using hc)
  exact hcR.trans (mul_le_mul (Nat.floor_le ha) (Nat.floor_le hb)
    (Nat.cast_nonneg _) ha)

private theorem seventh_unit_card {N : ℕ} (hN : 1 ≤ N) :
    ((currentChenUpsilon7UnitFibres N).card : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hc : (currentChenUpsilon7UnitFibres N).card ≤
      (Finset.Ioc 0 (Nat.floor ((N : ℝ) ^ (2 / 3 : ℝ)))).card := by
    apply Finset.card_le_card_of_injOn (fun t : ℕ × ℕ => t.1 * t.2)
    · intro t ht
      obtain ⟨hpos, hbound⟩ := seventh_pair_bound hN (Finset.mem_filter.mp ht).1
      exact Finset.mem_Ioc.mpr ⟨hpos,
        (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)).mpr hbound.le⟩
    · intro t ht u hu heq
      exact seventh_pair_injOn N (Finset.mem_filter.mp ht).1
        (Finset.mem_filter.mp hu).1 heq
  have hcR : ((currentChenUpsilon7UnitFibres N).card : ℝ) ≤
      (Nat.floor ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) := by
    exact_mod_cast (show (currentChenUpsilon7UnitFibres N).card ≤
      Nat.floor ((N : ℝ) ^ (2 / 3 : ℝ)) by
        simpa only [Nat.card_Ioc, Nat.sub_zero] using hc)
  exact hcR.trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))

private theorem seventh_prime_injOn (N : ℕ) :
    Set.InjOn (fun x : Σ _ : ℕ × ℕ, ℕ =>
      (x.1.1 * x.1.2, N - x.1.1 * x.1.2 * x.2))
      (currentChenUpsilon7PrimeTriples N) := by
  intro x hx y hy heq
  rcases x with ⟨⟨p₁, p₂⟩, r⟩
  rcases y with ⟨⟨q₁, q₂⟩, s⟩
  have hpq := seventh_pair_injOn N (Finset.mem_sigma.mp hx).1
    (Finset.mem_sigma.mp hy).1 (congrArg Prod.fst heq)
  have he₁ : p₁ = q₁ := congrArg Prod.fst hpq
  have he₂ : p₂ = q₂ := congrArg Prod.snd hpq
  subst q₁
  subst q₂
  obtain ⟨h₁, h₂, _hD, _ho, _hc, _hr, _hcut, hrN, _hP⟩ :=
    mem_currentChenUpsilon7PrimeTriples_iff.mp hx
  obtain ⟨_h₁, _h₂, _hD', _ho', _hc', _hs, _hcut', hsN, _hQ⟩ :=
    mem_currentChenUpsilon7PrimeTriples_iff.mp hy
  have hpos : 0 < p₁ * p₂ := mul_pos
    (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
    (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos
  have hsub : N - p₁ * p₂ * r = N - p₁ * p₂ * s := congrArg Prod.snd heq
  have hmul : (p₁ * p₂) * r = (p₁ * p₂) * s := by omega
  have hrs := Nat.eq_of_mul_eq_mul_left hpos hmul
  subst s
  rfl

private theorem seventh_prime_card {N : ℕ} (hN : 1 ≤ N) :
    (((currentChenUpsilon7PrimeTriples N).filter (fun x =>
      ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 5 : ℝ))).card : ℝ) ≤ (N : ℝ) ^ (13 / 15 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans_le hN)
  have hc := seventh_box_card
    ((currentChenUpsilon7PrimeTriples N).filter (fun x =>
      ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ)))
    (fun x : Σ _ : ℕ × ℕ, ℕ => (x.1.1 * x.1.2, N - x.1.1 * x.1.2 * x.2))
    ((N : ℝ) ^ (2 / 3 : ℝ)) ((N : ℝ) ^ (1 / 5 : ℝ))
    (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)
    (fun x hx y hy heq => seventh_prime_injOn N
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 heq) (by
        intro x hx
        obtain ⟨hxt, hsmall⟩ := Finset.mem_filter.mp hx
        obtain ⟨hpos, hbound⟩ := seventh_pair_bound hN (Finset.mem_sigma.mp hxt).1
        rcases x with ⟨⟨p₁, p₂⟩, r⟩
        obtain ⟨_h₁, _h₂, _hD, _ho, _hc, _hr, _hcut, _hN, hP⟩ :=
          mem_currentChenUpsilon7PrimeTriples_iff.mp hxt
        exact ⟨hpos, hbound.le, (mem_chenAdditivePrimeCarrier.mp hP).2.1.pos, hsmall⟩)
  convert hc using 1
  rw [← Real.rpow_add hNp]
  norm_num

private theorem seventh_three_primes_unique {a b c d e f : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hd : Nat.Prime d) (he : Nat.Prime e) (hf : Nat.Prime f)
    (hab : a ≤ b) (hbc : b ≤ c) (hde : d ≤ e) (hef : e ≤ f)
    (hprod : a * b * c = d * e * f) : a = d ∧ b = e ∧ c = f := by
  have hleft : ([a, b, c] : List ℕ).prod = a * b * c := by
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hright : ([d, e, f] : List ℕ).prod = a * b * c := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hprod.symm
  have hpl : ∀ p ∈ ([a, b, c] : List ℕ), Nat.Prime p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hpr : ∀ p ∈ ([d, e, f] : List ℕ), Nat.Prime p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hd
    · exact he
    · exact hf
  have hperm : ([a, b, c] : List ℕ).Perm [d, e, f] :=
    (Nat.primeFactorsList_unique hleft hpl).trans
      (Nat.primeFactorsList_unique hright hpr).symm
  have hsorted₁ : List.Pairwise (· ≤ ·) [a, b, c] := by
    apply List.pairwise_cons.mpr
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · have hx' : x = c := List.mem_singleton.mp hx
        subst x
        exact hab.trans hbc
    · exact List.pairwise_pair.mpr hbc
  have hsorted₂ : List.Pairwise (· ≤ ·) [d, e, f] := by
    apply List.pairwise_cons.mpr
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hde
      · have hx' : x = f := List.mem_singleton.mp hx
        subst x
        exact hde.trans hef
    · exact List.pairwise_pair.mpr hef
  have heq := List.Perm.eq_of_pairwise' hsorted₁ hsorted₂ hperm
  simpa only [List.cons.injEq, and_true] using heq

private theorem seventh_semiprime_bound {N p₁ p₂ r s : ℕ} (hN : 1 ≤ N)
    (hx : (⟨(p₁, p₂), (r, s)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈
      currentChenUpsilon7SemiprimeQuadruples N) :
    0 < p₁ * p₂ * r ∧ ((p₁ * p₂ * r : ℕ) : ℝ) < (N : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨h₁, h₂, _hD, ho, _hc, hr, _hs, hcut, hrs, hlt, _hP⟩ :=
    mem_currentChenUpsilon7SemiprimeQuadruples_iff.mp hx
  have hpos : 0 < p₁ * p₂ * r := mul_pos
    (mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos) hr.pos
  have hNp : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans_le hN)
  have h₁s : (p₁ : ℝ) ≤ s := by exact_mod_cast ho.le.trans (hcut.trans hrs)
  have h₂s : (p₂ : ℝ) ≤ s := by exact_mod_cast hcut.trans hrs
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have hM : (p₁ : ℝ) * p₂ * r ≤ (s : ℝ) ^ 3 := by
    calc
      (p₁ : ℝ) * p₂ * r ≤ ((s : ℝ) * s) * s :=
        mul_le_mul (mul_le_mul h₁s h₂s (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          hrsR (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hm : (p₁ : ℝ) * p₂ * r * s < (N : ℝ) := by
    exact_mod_cast (show p₁ * p₂ * r * s < N by simpa only [Nat.mul_assoc] using hlt)
  have hfour : ((p₁ : ℝ) * p₂ * r) ^ 4 < (N : ℝ) ^ 3 := by
    calc
      ((p₁ : ℝ) * p₂ * r) ^ 4 =
          ((p₁ : ℝ) * p₂ * r) ^ 3 * ((p₁ : ℝ) * p₂ * r) := by ring
      _ ≤ ((p₁ : ℝ) * p₂ * r) ^ 3 * (s : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = ((p₁ : ℝ) * p₂ * r * s) ^ 3 := by ring
      _ < (N : ℝ) ^ 3 := pow_lt_pow_left₀ hm (by positivity) (by decide)
  have hroot : ((N : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = (N : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast hNp.le]
    norm_num
  refine ⟨hpos, ?_⟩
  simp only [Nat.cast_mul]
  apply (pow_lt_pow_iff_left₀ (by positivity)
    (Real.rpow_nonneg hNp.le _) (by decide : (4 : ℕ) ≠ 0)).mp
  rwa [hroot]

private theorem seventh_semiprime_injOn (N : ℕ) :
    Set.InjOn (fun x : Σ _ : ℕ × ℕ, ℕ × ℕ =>
      (x.1.1 * x.1.2 * x.2.1, N - x.1.1 * x.1.2 * (x.2.1 * x.2.2)))
      (currentChenUpsilon7SemiprimeQuadruples N) := by
  intro x hx y hy heq
  rcases x with ⟨⟨p₁, p₂⟩, ⟨r, s⟩⟩
  rcases y with ⟨⟨q₁, q₂⟩, ⟨u, v⟩⟩
  obtain ⟨hp₁, hp₂, _hD, hporder, _hcap, hr, _hs, hp₂r, _hrs, hm, _hP⟩ :=
    mem_currentChenUpsilon7SemiprimeQuadruples_iff.mp hx
  obtain ⟨hq₁, hq₂, _hD', hqorder, _hcap', hu, _hv, hq₂u, _huv, hn, _hQ⟩ :=
    mem_currentChenUpsilon7SemiprimeQuadruples_iff.mp hy
  have hprefix : p₁ * p₂ * r = q₁ * q₂ * u := congrArg Prod.fst heq
  obtain ⟨he₁, he₂, he₃⟩ := seventh_three_primes_unique
    (mem_chenAdditivePrimeCarrier.mp hp₁).2.1
    (mem_chenAdditivePrimeCarrier.mp hp₂).2.1 hr
    (mem_chenAdditivePrimeCarrier.mp hq₁).2.1
    (mem_chenAdditivePrimeCarrier.mp hq₂).2.1 hu
    hporder.le hp₂r hqorder.le hq₂u hprefix
  subst q₁
  subst q₂
  subst u
  have hpos : 0 < p₁ * p₂ * r := mul_pos
    (mul_pos (mem_chenAdditivePrimeCarrier.mp hp₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp hp₂).2.1.pos) hr.pos
  have hsub : N - p₁ * p₂ * (r * s) = N - p₁ * p₂ * (r * v) :=
    congrArg Prod.snd heq
  have hmul : (p₁ * p₂ * r) * s = (p₁ * p₂ * r) * v := by
    simp only [← Nat.mul_assoc] at hm hn hsub
    omega
  have hsv := Nat.eq_of_mul_eq_mul_left hpos hmul
  subst v
  rfl

private theorem seventh_semiprime_card {N : ℕ} (hN : 1 ≤ N) :
    (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
      ((N - x.1.1 * x.1.2 * (x.2.1 * x.2.2) : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 5 : ℝ))).card : ℝ) ≤ (N : ℝ) ^ (19 / 20 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans_le hN)
  have hc := seventh_box_card
    ((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
      ((N - x.1.1 * x.1.2 * (x.2.1 * x.2.2) : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 5 : ℝ)))
    (fun x : Σ _ : ℕ × ℕ, ℕ × ℕ =>
      (x.1.1 * x.1.2 * x.2.1, N - x.1.1 * x.1.2 * (x.2.1 * x.2.2)))
    ((N : ℝ) ^ (3 / 4 : ℝ)) ((N : ℝ) ^ (1 / 5 : ℝ))
    (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)
    (fun x hx y hy heq => seventh_semiprime_injOn N
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 heq) (by
        intro x hx
        obtain ⟨hxt, hsmall⟩ := Finset.mem_filter.mp hx
        rcases x with ⟨⟨p₁, p₂⟩, ⟨r, s⟩⟩
        obtain ⟨hpos, hbound⟩ := seventh_semiprime_bound hN hxt
        obtain ⟨_h₁, _h₂, _hD, _ho, _hc, _hr, _hs, _hcut, _hrs, _hN, hP⟩ :=
          mem_currentChenUpsilon7SemiprimeQuadruples_iff.mp hxt
        exact ⟨hpos, hbound.le, (mem_chenAdditivePrimeCarrier.mp hP).2.1.pos, hsmall⟩)
  convert hc using 1
  rw [← Real.rpow_add hNp]
  norm_num

theorem eventually_currentChenUpsilon7_unit_smallGoldbach_error_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * (((currentChenUpsilon7UnitFibres N).card : ℝ) +
        (((currentChenUpsilon7PrimeTriples N).filter (fun x =>
          ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ) ≤
            (N : ℝ) ^ (1 / 5 : ℝ))).card : ℝ) +
        (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
          ((N - x.1.1 * x.1.2 * (x.2.1 * x.2.2) : ℕ) : ℝ) ≤
            (N : ℝ) ^ (1 / 5 : ℝ))).card : ℝ)) ≤
          epsilon * singularNormalization N := by
  have hbudget := eventually_powerLog_le_singularNormalization
    6 (19 / 20) 0 (by norm_num) epsilon hepsilon
  filter_upwards [hbudget, eventually_ge_atTop (1 : ℕ)] with N hb hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hu := (seventh_unit_card hN).trans
    (Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (2 / 3 : ℝ) ≤ 19 / 20))
  have ht := (seventh_prime_card hN).trans
    (Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (13 / 15 : ℝ) ≤ 19 / 20))
  have hq := seventh_semiprime_card hN
  have hb' : 6 * (N : ℝ) ^ (19 / 20 : ℝ) ≤ epsilon * singularNormalization N := by
    simpa only [pow_zero, mul_one] using hb
  linarith only [hu, ht, hq, hb']

end

end ImbalancedChen
