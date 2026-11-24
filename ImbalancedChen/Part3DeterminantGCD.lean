import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGcdMean

/-!
# The nonzero determinant gcd sum for (18)

The determinant is the signed integer `h*r' − h'*r`. The two frequency
boxes exclude zero, and the determinant guard is applied before the
nonzero-modulus divisor mean. The squared common gcd of `r` and `r'` has
a cubic bound on the positive box.
-/

namespace ImbalancedChen.Part3

open Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry (sum_int_gcd_le)

/-- The signed reciprocal-frequency determinant in the E1 Cauchy sum. -/
def e1Determinant (h h' : ℤ) (r r' : ℕ) : ℤ := h * r' - h' * r

/-- Factoring the common divisor leaves coprime quotient moduli, so each
remaining gcd sees only its opposite-row coefficient in the determinant. -/
theorem e1Determinant_gcd_le (h h' : ℤ) (r r' : ℕ) (hr : 0 < r) (hr' : 0 < r') :
    Int.gcd (e1Determinant h h' r r') ((r * r' : ℕ) : ℤ) ≤
      r.gcd r' ^ 2 * Int.gcd h (r / r.gcd r' : ℕ) * Int.gcd h' (r' / r.gcd r' : ℕ) := by
  let g := r.gcd r'
  let u := r / g
  let v := r' / g
  let j := h * (v : ℤ) - h' * (u : ℤ)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hr
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left _ hr) hg
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right _ hr') hg
  have hcop : u.Coprime v := Nat.gcd_div_gcd_div_gcd_of_pos_left hr
  have hru : r = g * u := (Nat.mul_div_cancel' (Nat.gcd_dvd_left r r')).symm
  have hrv : r' = g * v := (Nat.mul_div_cancel' (Nat.gcd_dvd_right r r')).symm
  have hj : e1Determinant h h' r r' = (g : ℤ) * j := by
    rw [e1Determinant, hru, hrv]
    push_cast
    dsimp only [j]
    ring
  have hm : ((r * r' : ℕ) : ℤ) = (g : ℤ) * ((g : ℤ) * ((u : ℤ) * (v : ℤ))) := by
    rw [hru, hrv]
    push_cast
    ring
  have hgu : Int.gcd j (u : ℤ) = Int.gcd h (u : ℤ) := by
    dsimp only [j]
    rw [Int.gcd_sub_mul_right_left]
    simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_mul, Int.natAbs_natCast] using
      hcop.symm.gcd_mul_right_cancel h.natAbs
  have hgv : Int.gcd j (v : ℤ) = Int.gcd h' (v : ℤ) := by
    have hneg : j = -(h' * (u : ℤ) - h * (v : ℤ)) := by dsimp only [j]; ring
    rw [hneg, Int.neg_gcd, Int.gcd_sub_mul_right_left]
    simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_mul, Int.natAbs_natCast] using
      hcop.gcd_mul_right_cancel h'.natAbs
  have hdvd : Int.gcd j ((g : ℤ) * ((u : ℤ) * (v : ℤ))) ∣
      g * (Int.gcd h (u : ℤ) * Int.gcd h' (v : ℤ)) := by
    rw [← hgu, ← hgv]
    have hdiv : Int.gcd j (g : ℤ) ∣ g := by simpa using Int.gcd_dvd_natAbs_right j (g : ℤ)
    exact (Int.gcd_mul_right_dvd_mul_gcd j (g : ℤ) ((u : ℤ) * (v : ℤ))).trans
      (Nat.mul_dvd_mul hdiv (Int.gcd_mul_right_dvd_mul_gcd j (u : ℤ) (v : ℤ)))
  have hpos : 0 < g * (Int.gcd h (u : ℤ) * Int.gcd h' (v : ℤ)) :=
    Nat.mul_pos hg (Nat.mul_pos (Int.gcd_pos_of_ne_zero_right h (Int.natCast_ne_zero.mpr hu.ne'))
      (Int.gcd_pos_of_ne_zero_right h' (Int.natCast_ne_zero.mpr hv.ne')))
  rw [hj, hm, Int.gcd_mul_left, Int.natAbs_natCast]
  change g * Int.gcd j _ ≤ g ^ 2 * Int.gcd h (u : ℤ) * Int.gcd h' (v : ℤ)
  calc
    _ ≤ g * (g * (Int.gcd h (u : ℤ) * Int.gcd h' (v : ℤ))) :=
      Nat.mul_le_mul_left g (Nat.le_of_dvd hpos hdvd)
    _ = _ := by ring

/-- The common gcd square summed on a positive box has a cubic bound. -/
theorem sum_gcd_sq_positiveBox_le_cube (R : ℕ) :
    (∑ r ∈ Ioc 0 R, ∑ r' ∈ Ioc 0 R, r.gcd r' ^ 2) ≤ R ^ 3 := by
  let S := Ioc 0 R
  let w (d r : ℕ) : ℕ := if d ∣ r then d else 0
  have hpoint (r r' : ℕ) (hr : r ∈ S) : r.gcd r' ^ 2 ≤ ∑ d ∈ S, w d r * w d r' := by
    have hmem : r.gcd r' ∈ S := mem_Ioc.mpr
      ⟨Nat.gcd_pos_of_pos_left _ (mem_Ioc.mp hr).1, (Nat.gcd_le_left _ (mem_Ioc.mp hr).1).trans
        (mem_Ioc.mp hr).2⟩
    simpa only [w, if_pos (Nat.gcd_dvd_left r r'), if_pos (Nat.gcd_dvd_right r r'), pow_two] using
      (single_le_sum (f := fun d => w d r * w d r') (fun _ _ => Nat.zero_le _) hmem)
  have hmass (d : ℕ) : (∑ r ∈ S, w d r) ≤ R := by
    change (∑ r ∈ Ioc 0 R, if d ∣ r then d else 0) ≤ R
    rw [← sum_filter]
    simpa [Nat.Ioc_filter_dvd_card_eq_div, Nat.mul_comm] using Nat.mul_div_le R d
  calc
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S, ∑ d ∈ S, w d r * w d r' :=
      sum_le_sum fun r hr => sum_le_sum fun r' _ => hpoint r r' hr
    _ = ∑ r ∈ S, ∑ d ∈ S, ∑ r' ∈ S, w d r * w d r' :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ d ∈ S, ∑ r ∈ S, ∑ r' ∈ S, w d r * w d r' := sum_comm
    _ = ∑ d ∈ S, (∑ r ∈ S, w d r) ^ 2 := by
      apply sum_congr rfl
      intro d _
      simp_rw [← mul_sum]
      rw [← sum_mul, pow_two]
    _ ≤ ∑ _d ∈ S, R ^ 2 := sum_le_sum fun d _ => Nat.pow_le_pow_left (hmass d) 2
    _ = R ^ 3 := by simp [S, Nat.card_Ioc, pow_succ, Nat.mul_comm]

/-- Integral frequencies in the symmetric box, excluding the zero mode. -/
noncomputable def e1NonzeroFrequencies (H : ℕ) : Finset ℤ := (Icc (-(H : ℤ)) (H : ℤ)).erase 0

private theorem mem_e1NonzeroFrequencies {H : ℕ} {h : ℤ} :
    h ∈ e1NonzeroFrequencies H ↔ h ≠ 0 ∧ h.natAbs ≤ H := by
  rw [e1NonzeroFrequencies, mem_erase, mem_Icc]
  rcases Int.natAbs_eq_iff.mp (rfl : h.natAbs = h.natAbs) with hh | hh <;> omega

/-- The pinned divisor mean applied to the positive and negative halves. -/
theorem sum_e1NonzeroFrequencies_gcd_le (H r : ℕ) (hr : 0 < r) :
    (∑ h ∈ e1NonzeroFrequencies H, Int.gcd h (r : ℤ)) ≤ 2 * H * r.divisors.card := by
  let pos : ℕ ↪ ℤ := ⟨fun n => (n : ℤ), Int.ofNat_injective⟩
  let neg : ℕ ↪ ℤ := ⟨fun n => -(n : ℤ), neg_injective.comp Int.ofNat_injective⟩
  let S := Ioc 0 H
  have hsign : e1NonzeroFrequencies H = S.map pos ∪ S.map neg := by
    ext h
    rw [mem_e1NonzeroFrequencies, mem_union, mem_map, mem_map]
    constructor
    · rintro ⟨hh, hH⟩
      have hm : h.natAbs ∈ S := mem_Ioc.mpr ⟨Int.natAbs_pos.mpr hh, hH⟩
      rcases Int.natAbs_eq_iff.mp (rfl : h.natAbs = h.natAbs) with he | he
      · exact Or.inl ⟨_, hm, he.symm⟩
      · exact Or.inr ⟨_, hm, he.symm⟩
    · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
      · exact ⟨Int.natCast_ne_zero.mpr (mem_Ioc.mp hn).1.ne', (mem_Ioc.mp hn).2⟩
      · exact ⟨neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (mem_Ioc.mp hn).1.ne'),
          by simpa only [neg, Function.Embedding.coeFn_mk, Int.natAbs_neg, Int.natAbs_natCast]
            using (mem_Ioc.mp hn).2⟩
  have hdisjoint : Disjoint (S.map pos) (S.map neg) := disjoint_left.mpr <| by
    intro h hp hn
    obtain ⟨m, hm, he⟩ := mem_map.mp hp
    obtain ⟨n, hn, he'⟩ := mem_map.mp hn
    have heq : (m : ℤ) = -(n : ℤ) := he.trans he'.symm
    have hmpos := (mem_Ioc.mp hm).1
    have hnpos := (mem_Ioc.mp hn).1
    omega
  rw [hsign, sum_union hdisjoint, sum_map, sum_map]
  change (∑ h ∈ S, Int.gcd (h : ℤ) (r : ℤ)) + ∑ h ∈ S, Int.gcd (-(h : ℤ)) (r : ℤ) ≤ _
  simp_rw [Int.neg_gcd]
  simp only [Int.gcd_comm _ (r : ℤ)]
  have hbound : (∑ h ∈ S, Int.gcd (r : ℤ) (h : ℤ)) ≤ H * r.divisors.card := by
    simpa only [Int.natAbs_natCast] using sum_int_gcd_le (r : ℤ) (Int.natCast_ne_zero.mpr hr.ne') H
  calc
    _ ≤ H * r.divisors.card + H * r.divisors.card := Nat.add_le_add hbound hbound
    _ = 2 * H * r.divisors.card := by ring

/-- Bounds the signed determinant's absolute value before using a divisor
bound, uniformly over the positive modulus and signed frequency boxes. -/
theorem e1Determinant_natAbs_le {R H r r' : ℕ} {h h' : ℤ}
    (hr : r ≤ R) (hr' : r' ≤ R) (hh : h.natAbs ≤ H) (hh' : h'.natAbs ≤ H) :
    (e1Determinant h h' r r').natAbs ≤ 2 * H * R := by
  unfold e1Determinant
  calc
    _ ≤ (h * (r' : ℤ)).natAbs + (h' * (r : ℤ)).natAbs := Int.natAbs_sub_le _ _
    _ = h.natAbs * r' + h'.natAbs * r := by simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ H * R + H * R := Nat.add_le_add (Nat.mul_le_mul hh hr') (Nat.mul_le_mul hh' hr)
    _ = _ := by ring

private theorem sum_e1Determinant_gcd_q_le (j : ℤ) (Q r r' : ℕ)
    (hj : j ≠ 0) (hr : 0 < r) (hr' : 0 < r') :
    (∑ q ∈ Ioc 0 Q, Int.gcd j ((q * r * r' : ℕ) : ℤ)) ≤
      Q * j.natAbs.divisors.card * Int.gcd j ((r * r' : ℕ) : ℤ) := by
  let d := Int.gcd j ((r * r' : ℕ) : ℤ)
  have hpoint (q : ℕ) : Int.gcd j ((q * r * r' : ℕ) : ℤ) ≤ Int.gcd j (q : ℤ) * d := by
    have hdvd := Int.gcd_mul_right_dvd_mul_gcd j (q : ℤ) ((r * r' : ℕ) : ℤ)
    have hpos := Nat.mul_pos (Int.gcd_pos_of_ne_zero_left (q : ℤ) hj)
      (Int.gcd_pos_of_ne_zero_right j (Int.natCast_ne_zero.mpr (Nat.mul_pos hr hr').ne'))
    simpa only [d, Nat.cast_mul, mul_assoc] using Nat.le_of_dvd hpos hdvd
  calc
    _ ≤ ∑ q ∈ Ioc 0 Q, Int.gcd j (q : ℤ) * d := sum_le_sum fun q _ => hpoint q
    _ = (∑ q ∈ Ioc 0 Q, Int.gcd j (q : ℤ)) * d := (sum_mul _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right d (sum_int_gcd_le j hj Q)

/-- The actual nonzero-determinant gcd contribution over positive modulus
boxes and signed frequency boxes. `T` bounds quotient divisor counts and
`J` bounds divisor counts only at nonzero determinant sizes. -/
theorem sum_e1NonzeroDeterminant_gcd_le (Q R H T J : ℕ)
    (hT : ∀ d ∈ Ioc 0 R, d.divisors.card ≤ T)
    (hJ : ∀ j : ℤ, j ≠ 0 → j.natAbs ≤ 2 * H * R → j.natAbs.divisors.card ≤ J) :
    (∑ r ∈ Ioc 0 R, ∑ r' ∈ Ioc 0 R,
      ∑ h ∈ e1NonzeroFrequencies H, ∑ h' ∈ e1NonzeroFrequencies H,
        if e1Determinant h h' r r' = 0 then 0 else
          ∑ q ∈ Ioc 0 Q, Int.gcd (e1Determinant h h' r r') ((q * r * r' : ℕ) : ℤ)) ≤
      Q * J * (2 * H * T) ^ 2 * R ^ 3 := by
  let S := Ioc 0 R
  let F := e1NonzeroFrequencies H
  let B := 2 * H * T
  have hfreq (d : ℕ) (hd : d ∈ S) : (∑ h ∈ F, Int.gcd h (d : ℤ)) ≤ B :=
    (sum_e1NonzeroFrequencies_gcd_le H d (mem_Ioc.mp hd).1).trans
      (Nat.mul_le_mul_left _ (hT d hd))
  have hrow (r r' : ℕ) (hr : r ∈ S) (hr' : r' ∈ S) :
      (∑ h ∈ F, ∑ h' ∈ F, if e1Determinant h h' r r' = 0 then 0 else
        ∑ q ∈ Ioc 0 Q, Int.gcd (e1Determinant h h' r r') ((q * r * r' : ℕ) : ℤ)) ≤
        Q * J * B ^ 2 * (r.gcd r') ^ 2 := by
    let g := r.gcd r'
    let u := r / g
    let v := r' / g
    have hr0 := (mem_Ioc.mp hr).1
    have hr'0 := (mem_Ioc.mp hr').1
    have hg := Nat.gcd_pos_of_pos_left r' hr0
    have hu : u ∈ S := mem_Ioc.mpr
      ⟨Nat.div_pos (Nat.gcd_le_left r' hr0) hg, (Nat.div_le_self _ _).trans (mem_Ioc.mp hr).2⟩
    have hv : v ∈ S := mem_Ioc.mpr
      ⟨Nat.div_pos (Nat.gcd_le_right r hr'0) hg, (Nat.div_le_self _ _).trans (mem_Ioc.mp hr').2⟩
    calc
      _ ≤ ∑ h ∈ F, ∑ h' ∈ F,
            (Q * J * g ^ 2) * (Int.gcd h (u : ℤ) * Int.gcd h' (v : ℤ)) := by
        apply sum_le_sum
        intro h hh
        apply sum_le_sum
        intro h' hh'
        let j := e1Determinant h h' r r'
        by_cases hj : j = 0
        · exact (if_pos hj).trans_le (Nat.zero_le _)
        · rw [if_neg hj]
          have hsize := e1Determinant_natAbs_le (mem_Ioc.mp hr).2 (mem_Ioc.mp hr').2
            (mem_e1NonzeroFrequencies.mp hh).2 (mem_e1NonzeroFrequencies.mp hh').2
          calc
            _ ≤ Q * j.natAbs.divisors.card * Int.gcd j ((r * r' : ℕ) : ℤ) :=
              sum_e1Determinant_gcd_q_le j Q r r' hj hr0 hr'0
            _ ≤ (Q * J) * (g ^ 2 * Int.gcd h (u : ℤ) * Int.gcd h' (v : ℤ)) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left Q (hJ j hj hsize))
                (e1Determinant_gcd_le h h' r r' hr0 hr'0)
            _ = _ := by ring
      _ = (Q * J * g ^ 2) * ((∑ h ∈ F, Int.gcd h (u : ℤ)) *
            ∑ h' ∈ F, Int.gcd h' (v : ℤ)) := by
        simp_rw [← mul_sum]
        rw [← sum_mul]
      _ ≤ (Q * J * g ^ 2) * (B * B) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (hfreq u hu) (hfreq v hv))
      _ = _ := by change (Q * J * g ^ 2) * (B * B) = Q * J * B ^ 2 * g ^ 2; ring
  calc
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S, Q * J * B ^ 2 * r.gcd r' ^ 2 :=
      sum_le_sum fun r hr => sum_le_sum fun r' hr' => hrow r r' hr hr'
    _ = Q * J * B ^ 2 * (∑ r ∈ S, ∑ r' ∈ S, r.gcd r' ^ 2) := by simp_rw [mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_gcd_sq_positiveBox_le_cube R)

/-- The zero determinant tuples retain both signed frequencies and both
dyadic positive denominators. -/
noncomputable def e1ZeroDeterminantTuples (H R : ℕ) : Finset ((ℤ × ℕ) × (ℤ × ℕ)) :=
  ((e1NonzeroFrequencies H ×ˢ Ico R (2 * R)) ×ˢ
    (e1NonzeroFrequencies H ×ˢ Ico R (2 * R))).filter
    (fun p => e1Determinant p.1.1 p.2.1 p.1.2 p.2.2 = 0)

private theorem e1_zeroDeterminant_reduced_dvd {h h' : ℤ} {r r' : ℕ}
    (hr : 0 < r) (hj : e1Determinant h h' r r' = 0) : r / r.gcd h.natAbs ∣ r' := by
  have hj' : h * (r' : ℤ) = h' * (r : ℤ) := sub_eq_zero.mp hj
  have he := congrArg Int.natAbs hj'
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at he
  have hd : r ∣ h.natAbs * r' := by rw [he]; exact dvd_mul_left _ _
  have hd' : r ∣ r.gcd h.natAbs * r' := by
    simpa only [gcd_eq_nat_gcd] using dvd_gcd_mul_of_dvd_mul hd
  have hg := Nat.gcd_pos_of_pos_left h.natAbs hr
  have he' : r.gcd h.natAbs * (r / r.gcd h.natAbs) ∣ r.gcd h.natAbs * r' := by
    rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_left r h.natAbs)]
  exact (Nat.mul_dvd_mul_iff_left hg).mp he'

/-- For a fixed signed numerator and positive dyadic denominator, the
partner denominator determines the partner numerator. -/
private theorem e1_zeroDeterminant_partners_card_le (H R : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Icc R (2 * R)) {h : ℤ} {r : ℕ}
    (hR : 0 < R) (hr : R ≤ r) :
    (((e1NonzeroFrequencies H ×ˢ S).filter
      (fun p => e1Determinant h p.1 r p.2 = 0)).card) ≤ 2 * r.gcd h.natAbs := by
  let d := r / r.gcd h.natAbs
  have hr0 := hR.trans_le hr
  have hg := Nat.gcd_pos_of_pos_left h.natAbs hr0
  have hd0 : 0 < d := Nat.div_pos (Nat.gcd_le_left h.natAbs hr0) hg
  have hdiv : r.gcd h.natAbs * d = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r h.natAbs)
  calc
    _ ≤ ((Ioc 0 (2 * R)).filter (d ∣ ·)).card := by
      apply card_le_card_of_injOn Prod.snd
      · intro p hp
        obtain ⟨hp, hj⟩ := mem_filter.mp hp
        obtain ⟨hlo, hhi⟩ := mem_Icc.mp (hS (mem_product.mp hp).2)
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hR.trans_le hlo, hhi⟩,
          e1_zeroDeterminant_reduced_dvd hr0 hj⟩
      · intro p hp p' hp' he
        have hpj : h * (p.2 : ℤ) = p.1 * (r : ℤ) := sub_eq_zero.mp (mem_filter.mp hp).2
        have hpj' : h * (p'.2 : ℤ) = p'.1 * (r : ℤ) := sub_eq_zero.mp (mem_filter.mp hp').2
        apply Prod.ext _ he
        apply mul_right_cancel₀ (Int.natCast_ne_zero.mpr hr0.ne')
        exact hpj.symm.trans ((congrArg (fun n : ℕ => h * (n : ℤ)) he).trans hpj')
    _ = (2 * R) / d := Nat.Ioc_filter_dvd_card_eq_div _ _
    _ ≤ 2 * r.gcd h.natAbs := by
      apply le_of_mul_le_mul_right _ hd0
      calc
        ((2 * R) / d) * d ≤ 2 * R := Nat.div_mul_le_self _ _
        _ ≤ 2 * r := Nat.mul_le_mul_left _ hr
        _ = (2 * r.gcd h.natAbs) * d := by rw [mul_assoc, hdiv]

private theorem e1ZeroDeterminantTuplesOn_card_le (H R : ℕ) (S : Finset ℕ)
    (hR : 0 < R) (hS : S ⊆ Icc R (2 * R)) :
    (((e1NonzeroFrequencies H ×ˢ S) ×ˢ (e1NonzeroFrequencies H ×ˢ S)).filter
      (fun p => e1Determinant p.1.1 p.2.1 p.1.2 p.2.2 = 0)).card ≤
      4 * H * ∑ r ∈ S, r.divisors.card := by
  let F := e1NonzeroFrequencies H
  calc
    _ = ∑ h ∈ F, ∑ r ∈ S,
        ((F ×ˢ S).filter (fun p => e1Determinant h p.1 r p.2 = 0)).card := by
      simp only [F, card_eq_sum_ones, sum_filter, sum_product]
    _ ≤ ∑ h ∈ F, ∑ r ∈ S, 2 * Int.gcd h (r : ℤ) := by
      apply sum_le_sum
      intro h _
      apply sum_le_sum
      intro r hr
      simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, Nat.gcd_comm r] using
        (e1_zeroDeterminant_partners_card_le H R S hS (h := h) hR (mem_Icc.mp (hS hr)).1)
    _ = ∑ r ∈ S, 2 * ∑ h ∈ F, Int.gcd h (r : ℤ) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ ≤ ∑ r ∈ S, 2 * (2 * H * r.divisors.card) := by
      apply sum_le_sum
      intro r hr
      exact Nat.mul_le_mul_left 2 (sum_e1NonzeroFrequencies_gcd_le H r (hR.trans_le (mem_Icc.mp (hS hr)).1))
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      ring

/-- The signed zero-determinant count over a half-open dyadic denominator box. -/
theorem e1ZeroDeterminantTuples_card_le (H R : ℕ) (hR : 0 < R) :
    (e1ZeroDeterminantTuples H R).card ≤
      4 * H * ∑ r ∈ Ico R (2 * R), r.divisors.card :=
  e1ZeroDeterminantTuplesOn_card_le H R _ hR fun _ hr =>
    mem_Icc.mpr ⟨(mem_Ico.mp hr).1, (mem_Ico.mp hr).2.le⟩

/-- A uniform divisor-count cap gives the stated `R*H` count with its
explicit divisor factor. -/
theorem e1ZeroDeterminantTuples_card_le_of_divisor_cap (H R T : ℕ) (hR : 0 < R)
    (hT : ∀ r ∈ Ico R (2 * R), r.divisors.card ≤ T) :
    (e1ZeroDeterminantTuples H R).card ≤ 4 * H * R * T := by
  rw [mul_assoc (4 * H) R T]
  refine (e1ZeroDeterminantTuples_card_le H R hR).trans (Nat.mul_le_mul_left _ ?_)
  calc
    _ ≤ ∑ _r ∈ Ico R (2 * R), T := sum_le_sum hT
    _ = _ := by
      have hcard : (Ico R (2 * R)).card = R := by rw [Nat.card_Ico]; omega
      simp only [sum_const, hcard, Nat.nsmul_eq_mul]

/-- The zero determinant tuples retain both signed frequencies and both
closed dyadic positive denominators. -/
noncomputable def e1ZeroDeterminantTuplesClosed (H R : ℕ) : Finset ((ℤ × ℕ) × (ℤ × ℕ)) :=
  ((e1NonzeroFrequencies H ×ˢ Icc R (2 * R)) ×ˢ
    (e1NonzeroFrequencies H ×ˢ Icc R (2 * R))).filter
    (fun p => e1Determinant p.1.1 p.2.1 p.1.2 p.2.2 = 0)

/-- The signed zero-determinant count over the closed dyadic denominator box. -/
theorem e1ZeroDeterminantTuplesClosed_card_le (H R : ℕ) (hR : 0 < R) :
    (e1ZeroDeterminantTuplesClosed H R).card ≤
      4 * H * ∑ r ∈ Icc R (2 * R), r.divisors.card :=
  e1ZeroDeterminantTuplesOn_card_le H R _ hR Subset.rfl

/-- The closed interval has exactly `R+1` denominator values. -/
theorem e1ZeroDeterminantTuplesClosed_card_le_of_divisor_cap (H R T : ℕ) (hR : 0 < R)
    (hT : ∀ r ∈ Icc R (2 * R), r.divisors.card ≤ T) :
    (e1ZeroDeterminantTuplesClosed H R).card ≤ 4 * H * (R + 1) * T := by
  rw [mul_assoc (4 * H) (R + 1) T]
  refine (e1ZeroDeterminantTuplesClosed_card_le H R hR).trans (Nat.mul_le_mul_left _ ?_)
  calc
    _ ≤ ∑ _r ∈ Icc R (2 * R), T := sum_le_sum hT
    _ = _ := by
      have hcard : (Icc R (2 * R)).card = R + 1 := by rw [Nat.card_Icc]; omega
      simp only [sum_const, hcard, Nat.nsmul_eq_mul]

/-- A closed dyadic box has at most `8 * H * R * T` zero determinant tuples. -/
theorem e1ZeroDeterminantTuplesClosed_card_le_eight_mul (H R T : ℕ) (hR : 0 < R)
    (hT : ∀ r ∈ Icc R (2 * R), r.divisors.card ≤ T) :
    (e1ZeroDeterminantTuplesClosed H R).card ≤ 8 * H * R * T := by
  calc
    _ ≤ 4 * H * (R + 1) * T := e1ZeroDeterminantTuplesClosed_card_le_of_divisor_cap H R T hR hT
    _ ≤ 4 * H * (2 * R) * T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

/-- With the exact complete scale `x = M*N`, the three raw Cauchy
monomials become the terms of (18). The frequency cutoff slack is linear
on the diagonal term and quadratic on the other two. -/
theorem e1_cauchyMonomials_le (N Q R M H L x : ℝ)
    (hN : 0 < N) (hQ : 0 < Q) (hR : 0 < R) (hM : 0 < M) (hH : 0 ≤ H)
    (hx : x = M * N) (hcut : H ≤ L * (Q * R / M)) :
    N ^ 3 / (Q ^ 3 * R ^ 2) *
        (N * Q * R * H + Q * Real.sqrt Q * R ^ 3 * H ^ 2 + N * R * H ^ 2) ≤
      N ^ 4 / Q ^ 2 * (L * (N * Q / x) + L ^ 2 * (N * Q ^ (5 / 2 : ℝ) * R ^ 3 / x ^ 2) +
        L ^ 2 * (N ^ 2 * Q * R / x ^ 2)) := by
  subst x
  have hcutSq := pow_le_pow_left₀ hH hcut 2
  have hQpow : Q ^ (5 / 2 : ℝ) = Q ^ 2 * Real.sqrt Q := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hQ,
      Real.rpow_two, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ N ^ 3 / (Q ^ 3 * R ^ 2) *
        (N * Q * R * (L * (Q * R / M)) + Q * Real.sqrt Q * R ^ 3 * (L * (Q * R / M)) ^ 2 +
          N * R * (L * (Q * R / M)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hcut (by positivity))
        (mul_le_mul_of_nonneg_left hcutSq (by positivity)))
        (mul_le_mul_of_nonneg_left hcutSq (by positivity))
    _ = _ := by
      rw [hQpow]
      field_simp

end ImbalancedChen.Part3
