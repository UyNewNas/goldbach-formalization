import ImbalancedChen.Part3ActualLargeGCDBetaMass

/-!
# Signed nonzero difference multiplicity at all positive auxiliary divisors

The carrier keeps all ordered s and h labels, positive f, both frequency
signs, and the literal nonzero difference. Divisor-decomposition Cauchy
retains cross-f collisions before the remaining f sum is counted once.
All bounds in this file are finite; no spectral estimate is a hypothesis.
-/

namespace ImbalancedChen.Part3.LichtmanSignedDifferenceMultiplicity

noncomputable section
open Classical Finset
open scoped BigOperators

def dyadicCarrier (T : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 (Nat.floor (2 * T))).filter
    (fun n => T ≤ (n : ℝ) ∧ (n : ℝ) < 2 * T)

def frequencyCarrier (H : ℝ) : Finset ℤ :=
  ((Finset.Icc 1 (Nat.floor H)).image (fun n : ℕ => (n : ℤ))) ∪
    ((Finset.Icc 1 (Nat.floor H)).image (fun n : ℕ => -(n : ℤ)))

def difference (t : (ℕ × ℕ × ℕ) × (ℤ × ℤ)) : ℤ :=
  t.2.1 * (t.1.1 : ℤ) - t.2.2 * (t.1.2.1 : ℤ)

def sourceCarrier (S H F : ℝ) : Finset ((ℕ × ℕ × ℕ) × (ℤ × ℤ)) :=
  ((dyadicCarrier S ×ˢ (dyadicCarrier S ×ˢ dyadicCarrier F)) ×ˢ
    (frequencyCarrier H ×ˢ frequencyCarrier H)).filter
      (fun t => difference t ≠ 0)

def output (t : (ℕ × ℕ × ℕ) × (ℤ × ℤ)) : ℕ × ℤ :=
  (t.1.1 * t.1.2.1, (t.1.2.2 : ℤ) * difference t)

def multiplicity (S H F : ℝ) (z : ℕ) (y : ℤ) : ℕ :=
  ((sourceCarrier S H F).filter (fun t => output t = (z, y))).card

def multiplicityL2 (S H F : ℝ) (nu : ℕ) : ℝ :=
  ∑ zy ∈ (sourceCarrier S H F).image output,
    if (nu : ℤ) ∣ zy.2 then (multiplicity S H F zy.1 zy.2 : ℝ) ^ 2 else 0

def supportCap (S H F : ℝ) : ℕ :=
  Nat.ceil (max (4 * S ^ 2) (8 * F * H * S))

def divisorMaximum (S H F : ℝ) : ℕ :=
  (Finset.Icc 1 (supportCap S H F)).sup (fun n : ℕ => n.divisors.card)

private theorem mem_dyadicCarrier_iff {T : ℝ} {n : ℕ} :
    n ∈ dyadicCarrier T ↔ 0 < n ∧ T ≤ (n : ℝ) ∧ (n : ℝ) < 2 * T := by
  constructor
  · intro hn
    obtain ⟨hn, hlo, hhi⟩ := mem_filter.mp hn
    exact ⟨(mem_Ioc.mp hn).1, hlo, hhi⟩
  · rintro ⟨hn, hlo, hhi⟩
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn, Nat.le_floor hhi.le⟩, hlo, hhi⟩

private theorem card_dyadicCarrier_le {T : ℝ} (hT : 0 ≤ T) :
    ((dyadicCarrier T).card : ℝ) ≤ 2 * T := by
  calc
    _ ≤ ((Ioc 0 (Nat.floor (2 * T))).card : ℝ) := by
      exact_mod_cast card_le_card (filter_subset _ _)
    _ = (Nat.floor (2 * T) : ℝ) := by simp only [Nat.card_Ioc, Nat.sub_zero]
    _ ≤ 2 * T := Nat.floor_le (by positivity)

private theorem mem_frequencyCarrier_iff {H : ℝ} (hH : 0 ≤ H) {h : ℤ} :
    h ∈ frequencyCarrier H ↔ h ≠ 0 ∧ (h.natAbs : ℝ) ≤ H := by
  constructor
  · intro hh
    rcases mem_union.mp hh with hh | hh
    · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
      obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
      refine ⟨by omega, ?_⟩
      simpa only [Int.natAbs_natCast] using
        (show (n : ℝ) ≤ (Nat.floor H : ℝ) by exact_mod_cast hnhi).trans
          (Nat.floor_le hH)
    · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
      obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
      refine ⟨by omega, ?_⟩
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
        (show (n : ℝ) ≤ (Nat.floor H : ℝ) by exact_mod_cast hnhi).trans
          (Nat.floor_le hH)
  · rintro ⟨hh, hbound⟩
    have hn : h.natAbs ∈ Icc 1 (Nat.floor H) :=
      mem_Icc.mpr ⟨Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr hh), Nat.le_floor hbound⟩
    rcases Int.natAbs_eq h with heq | heq
    · exact mem_union.mpr (Or.inl (mem_image.mpr ⟨h.natAbs, hn, heq.symm⟩))
    · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨h.natAbs, hn, heq.symm⟩))

private theorem card_frequencyCarrier_le {H : ℝ} (hH : 0 ≤ H) :
    ((frequencyCarrier H).card : ℝ) ≤ 2 * H := by
  have hcard : (frequencyCarrier H).card ≤ 2 * Nat.floor H := by
    calc
      _ ≤ ((Icc 1 (Nat.floor H)).image (fun n : ℕ => (n : ℤ))).card +
          ((Icc 1 (Nat.floor H)).image (fun n : ℕ => -(n : ℤ))).card :=
        card_union_le _ _
      _ ≤ (Icc 1 (Nat.floor H)).card + (Icc 1 (Nat.floor H)).card :=
        Nat.add_le_add card_image_le card_image_le
      _ = _ := by simp only [Nat.card_Icc]; omega
  calc
    _ ≤ (2 : ℝ) * (Nat.floor H : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * H := mul_le_mul_of_nonneg_left (Nat.floor_le hH) (by norm_num)

private theorem frequency_norm_bound {H : ℝ} (hH : 0 ≤ H) {h : ℤ}
    (hh : h ∈ frequencyCarrier H) : |(h : ℝ)| ≤ H := by
  have habs : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by
    exact_mod_cast Int.natCast_natAbs h
  rw [← habs]
  exact ((mem_frequencyCarrier_iff hH).mp hh).2

private theorem sum_frequency_gcd_le (nu : ℕ) (hnu : 0 < nu)
    (L : ℝ) (hL : 0 ≤ L) :
    (∑ k ∈ frequencyCarrier L, (nu.gcd k.natAbs : ℝ)) ≤
      2 * L * (nu.divisors.card : ℝ) := by
  let A := Icc 1 (Nat.floor L)
  have hdisjoint : Disjoint (A.image (fun n : ℕ => (n : ℤ)))
      (A.image (fun n : ℕ => -(n : ℤ))) := by
    apply disjoint_left.mpr
    intro k hkpos hkneg
    obtain ⟨a, ha, hak⟩ := mem_image.mp hkpos
    obtain ⟨b, hb, hbk⟩ := mem_image.mp hkneg
    have ha1 := (mem_Icc.mp ha).1
    have hb1 := (mem_Icc.mp hb).1
    have hab : (a : ℤ) = -(b : ℤ) := hak.trans hbk.symm
    omega
  have himagepos :
      (∑ k ∈ A.image (fun n : ℕ => (n : ℤ)), (nu.gcd k.natAbs : ℝ)) =
        ∑ n ∈ A, (nu.gcd n : ℝ) := by
    rw [sum_image]
    · simp only [Int.natAbs_natCast]
    · intro a _ b _ hab
      exact Int.ofNat_inj.mp hab
  have himageneg :
      (∑ k ∈ A.image (fun n : ℕ => -(n : ℤ)), (nu.gcd k.natAbs : ℝ)) =
        ∑ n ∈ A, (nu.gcd n : ℝ) := by
    rw [sum_image]
    · simp only [Int.natAbs_neg, Int.natAbs_natCast]
    · intro a _ b _ hab
      exact Int.ofNat_inj.mp (neg_injective hab)
  have hmean : (∑ n ∈ A, (nu.gcd n : ℝ)) ≤
      L * (nu.divisors.card : ℝ) := by
    have hI : A = Ioc 0 (Nat.floor L) := by
      ext n
      simp only [A, mem_Icc, mem_Ioc]
      omega
    calc
      _ = ∑ n ∈ Ioc 0 (Nat.floor L), (nu.gcd n : ℝ) := by rw [hI]
      _ ≤ (Nat.floor L : ℝ) * (nu.divisors.card : ℝ) := by
        exact_mod_cast ActualLargeGCDBetaMass.sum_gcd_le hnu.ne' (Nat.floor L)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le hL) (Nat.cast_nonneg _)
  calc
    _ = (∑ k ∈ A.image (fun n : ℕ => (n : ℤ)), (nu.gcd k.natAbs : ℝ)) +
          ∑ k ∈ A.image (fun n : ℕ => -(n : ℤ)), (nu.gcd k.natAbs : ℝ) := by
      exact sum_union hdisjoint
    _ = 2 * ∑ n ∈ A, (nu.gcd n : ℝ) := by rw [himagepos, himageneg]; ring
    _ ≤ 2 * (L * (nu.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hmean (by norm_num)
    _ = _ := by ring

private theorem card_dyadic_multiples_le (F : ℝ) (hF : 0 ≤ F)
    (m : ℕ) (hm : 0 < m) :
    (((dyadicCarrier F).filter (fun f => m ∣ f)).card : ℝ) ≤ 2 * F / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : ((dyadicCarrier F).filter (fun f => m ∣ f)).card ≤
      (Icc 1 (Nat.floor (2 * F / m))).card := by
    apply card_le_card_of_injOn (fun f : ℕ => f / m)
    · intro f hf
      obtain ⟨hf, hmf⟩ := mem_filter.mp hf
      obtain ⟨hfpos, _hflo, hfhi⟩ := mem_dyadicCarrier_iff.mp hf
      have hqpos : 0 < f / m := Nat.div_pos (Nat.le_of_dvd hfpos hmf) hm
      have heq : ((f / m : ℕ) : ℝ) * m = f := by exact_mod_cast Nat.div_mul_cancel hmf
      have hupper : ((f / m : ℕ) : ℝ) ≤ 2 * F / m := by
        apply (le_div_iff₀ hmR).mpr
        rw [heq]
        exact hfhi.le
      exact mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hqpos, Nat.le_floor hupper⟩
    · intro f hf g hg heq
      have hfdiv := (mem_filter.mp hf).2
      have hgdiv := (mem_filter.mp hg).2
      calc
        f = (f / m) * m := (Nat.div_mul_cancel hfdiv).symm
        _ = (g / m) * m := congrArg (fun n : ℕ => n * m) heq
        _ = g := Nat.div_mul_cancel hgdiv
  calc
    _ ≤ ((Icc 1 (Nat.floor (2 * F / m))).card : ℝ) := by exact_mod_cast hc
    _ = (Nat.floor (2 * F / m) : ℝ) := by simp only [Nat.card_Icc]; congr 1; omega
    _ ≤ _ := Nat.floor_le (div_nonneg (by positivity) hmR.le)

private theorem card_le_sum_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β) (C : β → ℝ)
    (hmap : ∀ a ∈ A, f a ∈ B)
    (hbound : ∀ b ∈ B, ((A.filter (fun a => f a = b)).card : ℝ) ≤ C b) :
    (A.card : ℝ) ≤ ∑ b ∈ B, C b := by
  have heq := card_eq_sum_card_fiberwise hmap
  calc
    (A.card : ℝ) = ∑ b ∈ B, ((A.filter (fun a => f a = b)).card : ℝ) := by
      exact_mod_cast heq
    _ ≤ _ := sum_le_sum hbound

private theorem sum_le_sum_injective_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (g : α → β) (f : α → ℝ) (F : β → ℝ)
    (hmap : ∀ a ∈ A, g a ∈ B) (hinj : Set.InjOn g A)
    (hweight : ∀ a ∈ A, f a ≤ F (g a)) (hF : ∀ b ∈ B, 0 ≤ F b) :
    (∑ a ∈ A, f a) ≤ ∑ b ∈ B, F b := by
  calc
    _ ≤ ∑ a ∈ A, F (g a) := sum_le_sum hweight
    _ = ∑ b ∈ A.image g, F b := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (by intro b hb; obtain ⟨a, ha, rfl⟩ := mem_image.mp hb; exact hmap a ha)
      (fun b hb _ => hF b hb)

private theorem product_divisibility_reduced {nu f : ℕ} (hnu : 0 < nu) (k : ℤ)
    (hdiv : (nu : ℤ) ∣ (f : ℤ) * k) :
    nu / nu.gcd k.natAbs ∣ f := by
  let g := nu.gcd k.natAbs
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hnu
  have hfactnu : nu / g * g = nu := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hfactk : k.natAbs / g * g = k.natAbs :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hnat : nu ∣ f * k.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using (Int.natCast_dvd.mp hdiv)
  have hcancel : nu / g ∣ f * (k.natAbs / g) := by
    apply Nat.dvd_of_mul_dvd_mul_right hg
    simpa only [hfactnu, mul_assoc, hfactk] using hnat
  exact (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_right hcancel

private theorem card_f_product_divisible_le (F : ℝ) (hF : 0 ≤ F)
    (nu : ℕ) (hnu : 0 < nu) (k : ℤ) :
    (((dyadicCarrier F).filter (fun f => (nu : ℤ) ∣ (f : ℤ) * k)).card : ℝ) ≤
      2 * F * (nu.gcd k.natAbs : ℝ) / nu := by
  let g := nu.gcd k.natAbs
  let m := nu / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hnu
  have hm : 0 < m := Nat.div_gcd_pos_of_pos_left _ hnu
  have hfactor : (m : ℝ) * (g : ℝ) = (nu : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left nu k.natAbs)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  calc
    _ ≤ (((dyadicCarrier F).filter (fun f => m ∣ f)).card : ℝ) := by
      apply Nat.cast_le.mpr
      apply card_le_card
      intro f hf
      obtain ⟨hf, hd⟩ := mem_filter.mp hf
      exact mem_filter.mpr ⟨hf, product_divisibility_reduced hnu k hd⟩
    _ ≤ 2 * F / m := card_dyadic_multiples_le F hF m hm
    _ = 2 * F * (nu.gcd k.natAbs : ℝ) / nu := by
      change 2 * F / (m : ℝ) = 2 * F * (g : ℝ) / (nu : ℝ)
      rw [← hfactor]
      field_simp [hmR.ne', hgR.ne']

private theorem sum_divisible_ratio_le_harmonic (e M : ℕ) (he : 0 < e) :
    (∑ d ∈ Icc 1 M, if e ∣ d then (e : ℝ) / d else 0) ≤
      (harmonic M : ℝ) := by
  have hH : (∑ j ∈ Icc 1 M, 1 / (j : ℝ)) = (harmonic M : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [← hH, ← sum_filter]
  apply sum_le_sum_injective_map
    ((Icc 1 M).filter (fun d => e ∣ d)) (Icc 1 M)
    (fun d => d / e) (fun d => (e : ℝ) / d) (fun j => 1 / (j : ℝ))
  · intro d hd
    obtain ⟨hd, hed⟩ := mem_filter.mp hd
    obtain ⟨hdlo, hdhi⟩ := mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    exact mem_Icc.mpr
      ⟨Nat.succ_le_iff.mpr (Nat.div_pos (Nat.le_of_dvd hdpos hed) he),
        (Nat.div_le_self d e).trans hdhi⟩
  · intro d hd j hj heq
    have hde := (mem_filter.mp hd).2
    have hje := (mem_filter.mp hj).2
    calc
      d = (d / e) * e := (Nat.div_mul_cancel hde).symm
      _ = (j / e) * e := congrArg (fun n : ℕ => n * e) heq
      _ = j := Nat.div_mul_cancel hje
  · intro d hd
    obtain ⟨hd, hed⟩ := mem_filter.mp hd
    have hdpos : 0 < d := by have := (mem_Icc.mp hd).1; omega
    have hqpos : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hdpos hed) he
    have hfact : (e : ℝ) * ((d / e : ℕ) : ℝ) = d := by
      exact_mod_cast Nat.mul_div_cancel' hed
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    have hqR : (0 : ℝ) < (d / e : ℕ) := by exact_mod_cast hqpos
    apply le_of_eq
    rw [← hfact]
    field_simp [heR.ne', hqR.ne']
  · intros; positivity

private theorem sum_gcd_div_le_divisors_harmonic (nu M : ℕ) (hnu : 0 < nu) :
    (∑ d ∈ Icc 1 M, (d.gcd nu : ℝ) / (d : ℝ)) ≤
      (nu.divisors.card : ℝ) * (harmonic M : ℝ) := by
  calc
    _ ≤ ∑ d ∈ Icc 1 M,
        (∑ e ∈ nu.divisors, if e ∣ d then (e : ℝ) else 0) / (d : ℝ) := by
      apply sum_le_sum
      intro d hd
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have h := ActualLargeGCDBetaMass.gcd_le_divisor_sum hnu.ne' d
      rw [Nat.gcd_comm] at h
      exact_mod_cast h
    _ = ∑ e ∈ nu.divisors, ∑ d ∈ Icc 1 M,
        if e ∣ d then (e : ℝ) / d else 0 := by
      simp only [sum_div, ite_div, zero_div]
      exact sum_comm
    _ ≤ ∑ _e ∈ nu.divisors, (harmonic M : ℝ) := by
      apply sum_le_sum
      intro e he
      exact sum_divisible_ratio_le_harmonic e M (Nat.pos_of_mem_divisors he)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

private theorem source_data {S H F : ℝ} {t : (ℕ × ℕ × ℕ) × (ℤ × ℤ)}
    (ht : t ∈ sourceCarrier S H F) :
    t.1.1 ∈ dyadicCarrier S ∧ t.1.2.1 ∈ dyadicCarrier S ∧
      t.1.2.2 ∈ dyadicCarrier F ∧ t.2.1 ∈ frequencyCarrier H ∧
      t.2.2 ∈ frequencyCarrier H ∧ difference t ≠ 0 := by
  obtain ⟨hprod, hne⟩ := mem_filter.mp ht
  obtain ⟨hs, hh⟩ := mem_product.mp hprod
  obtain ⟨hs₁, hs₂f⟩ := mem_product.mp hs
  exact ⟨hs₁, (mem_product.mp hs₂f).1, (mem_product.mp hs₂f).2,
    (mem_product.mp hh).1, (mem_product.mp hh).2, hne⟩

private theorem source_output_bounds {S H F : ℝ}
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F)
    {t : (ℕ × ℕ × ℕ) × (ℤ × ℤ)} (ht : t ∈ sourceCarrier S H F) :
    0 < (output t).1 ∧ (output t).2 ≠ 0 ∧
      ((output t).1 : ℝ) < 4 * S ^ 2 ∧
      ((output t).2.natAbs : ℝ) < 8 * F * H * S := by
  obtain ⟨hs₁, hs₂, hf, hh₁, hh₂, hk⟩ := source_data ht
  obtain ⟨hs₁pos, hs₁lo, hs₁hi⟩ := mem_dyadicCarrier_iff.mp hs₁
  obtain ⟨hs₂pos, hs₂lo, hs₂hi⟩ := mem_dyadicCarrier_iff.mp hs₂
  obtain ⟨hfpos, _hflo, hfhi⟩ := mem_dyadicCarrier_iff.mp hf
  have hH0 : 0 ≤ H := by linarith
  have hSpos : 0 < S := by linarith
  have hFpos : 0 < F := by linarith
  have hh₁bound := frequency_norm_bound hH0 hh₁
  have hh₂bound := frequency_norm_bound hH0 hh₂
  have hkbound : |((difference t : ℤ) : ℝ)| < 4 * H * S := by
    calc
      _ = |(t.2.1 : ℝ) * (t.1.1 : ℝ) - (t.2.2 : ℝ) * (t.1.2.1 : ℝ)| := by
        simp only [difference, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      _ ≤ |(t.2.1 : ℝ) * (t.1.1 : ℝ)| + |(t.2.2 : ℝ) * (t.1.2.1 : ℝ)| :=
        abs_sub _ _
      _ = |(t.2.1 : ℝ)| * (t.1.1 : ℝ) + |(t.2.2 : ℝ)| * (t.1.2.1 : ℝ) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ H * (t.1.1 : ℝ) + H * (t.1.2.1 : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right hh₁bound (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_right hh₂bound (Nat.cast_nonneg _))
      _ = H * ((t.1.1 : ℝ) + (t.1.2.1 : ℝ)) := by ring
      _ < H * (4 * S) := mul_lt_mul_of_pos_left (by linarith) (by linarith)
      _ = _ := by ring
  have hfnz : (t.1.2.2 : ℤ) ≠ 0 := by exact_mod_cast hfpos.ne'
  refine ⟨Nat.mul_pos hs₁pos hs₂pos, mul_ne_zero hfnz hk, ?_, ?_⟩
  · change ((t.1.1 * t.1.2.1 : ℕ) : ℝ) < _
    rw [Nat.cast_mul]
    calc
      (t.1.1 : ℝ) * (t.1.2.1 : ℝ) < (2 * S) * (t.1.2.1 : ℝ) :=
        mul_lt_mul_of_pos_right hs₁hi (by exact_mod_cast hs₂pos)
      _ < (2 * S) * (2 * S) := mul_lt_mul_of_pos_left hs₂hi (by positivity)
      _ = _ := by ring
  · have habs : ((output t).2.natAbs : ℝ) =
        (t.1.2.2 : ℝ) * |((difference t : ℤ) : ℝ)| := by
      change (((t.1.2.2 : ℤ) * difference t).natAbs : ℝ) = _
      rw [Int.natAbs_mul, Nat.cast_mul, Int.natAbs_natCast]
      congr 1
      exact_mod_cast Int.natCast_natAbs (difference t)
    rw [habs]
    calc
      _ ≤ (2 * F) * |((difference t : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_right hfhi.le (abs_nonneg _)
      _ < (2 * F) * (4 * H * S) := mul_lt_mul_of_pos_left hkbound (by positivity)
      _ = _ := by ring

private theorem zero_above_support (S H F : ℝ) (hS : 1 ≤ S) (hH : 1 ≤ H)
    (hF : 1 ≤ F) (nu : ℕ) (hnu : 0 < nu)
    (hlarge : 8 * F * H * S ≤ (nu : ℝ)) : multiplicityL2 S H F nu = 0 := by
  unfold multiplicityL2
  apply sum_eq_zero
  intro zy hzy
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hzy
  have hb := source_output_bounds hS hH hF ht
  have hnot : ¬ (nu : ℤ) ∣ (output t).2 := by
    intro hd
    have hnat := Int.natCast_dvd.mp hd
    have hle : nu ≤ (output t).2.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hb.2.1) hnat
    have hleR : (nu : ℝ) ≤ ((output t).2.natAbs : ℝ) := by exact_mod_cast hle
    exact (not_lt_of_ge hleR) (hb.2.2.2.trans_le hlarge)
  exact if_neg hnot

private theorem divisorMaximum_pos (S H F : ℝ) (hS : 1 ≤ S) :
    1 ≤ divisorMaximum S H F := by
  have hcap : 1 ≤ supportCap S H F := by
    have hreal : (1 : ℝ) ≤ (supportCap S H F : ℝ) := by
      calc
        (1 : ℝ) ≤ 4 * S ^ 2 := by nlinarith [sq_nonneg (S - 1)]
        _ ≤ max (4 * S ^ 2) (8 * F * H * S) := le_max_left _ _
        _ ≤ _ := Nat.le_ceil _
    exact_mod_cast hreal
  have h := le_sup (s := Icc 1 (supportCap S H F)) (f := fun n : ℕ => n.divisors.card)
    (mem_Icc.mpr ⟨le_rfl, hcap⟩ : 1 ∈ Icc 1 (supportCap S H F))
  simpa only [Nat.divisors_one, card_singleton] using h

private theorem tau_le_divisorMaximum {S H F : ℝ} {n : ℕ}
    (hn : 0 < n) (hbound : (n : ℝ) ≤ max (4 * S ^ 2) (8 * F * H * S)) :
    n.divisors.card ≤ divisorMaximum S H F := by
  apply le_sup
  apply mem_Icc.mpr
  refine ⟨Nat.succ_le_iff.mpr hn, ?_⟩
  exact_mod_cast hbound.trans (Nat.le_ceil _)

private def row (H : ℝ) (s : ℕ × ℕ) (k : ℤ) : Finset (ℤ × ℤ) :=
  (frequencyCarrier H ×ˢ frequencyCarrier H).filter
    (fun h => h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) = k)

private def outputFiber (S H F : ℝ) (zy : ℕ × ℤ) :
    Finset ((ℕ × ℕ × ℕ) × (ℤ × ℤ)) :=
  (sourceCarrier S H F).filter (fun t => output t = zy)

private def decompositionCarrier (S H F : ℝ) (zy : ℕ × ℤ) : Finset (ℕ × ℕ × ℕ) :=
  (outputFiber S H F zy).image Prod.fst

private theorem decomposition_witness {S H F : ℝ} {zy : ℕ × ℤ}
    {p : ℕ × ℕ × ℕ} (hp : p ∈ decompositionCarrier S H F zy) :
    ∃ h : ℤ × ℤ, (p, h) ∈ sourceCarrier S H F ∧ output (p, h) = zy := by
  obtain ⟨⟨p', h⟩, ht, rfl⟩ := mem_image.mp hp
  exact ⟨h, (mem_filter.mp ht).1, (mem_filter.mp ht).2⟩

private theorem card_decompositionCarrier_le {S H F : ℝ}
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F) {zy : ℕ × ℤ}
    (hzy : zy ∈ (sourceCarrier S H F).image output) :
    (decompositionCarrier S H F zy).card ≤ divisorMaximum S H F ^ 2 := by
  obtain ⟨t, ht, hout⟩ := mem_image.mp hzy
  have hbounds := source_output_bounds hS hH hF ht
  have hz : 0 < zy.1 := by simpa only [hout] using hbounds.1
  have hy : zy.2 ≠ 0 := by simpa only [hout] using hbounds.2.1
  have hzc : zy.1.divisors.card ≤ divisorMaximum S H F := by
    apply tau_le_divisorMaximum hz
    have h := hbounds.2.2.1.le.trans (le_max_left (4 * S ^ 2) (8 * F * H * S))
    simpa only [hout] using h
  have hyc : zy.2.natAbs.divisors.card ≤ divisorMaximum S H F := by
    apply tau_le_divisorMaximum (Int.natAbs_pos.mpr hy)
    have h := hbounds.2.2.2.le.trans (le_max_right (4 * S ^ 2) (8 * F * H * S))
    simpa only [hout] using h
  calc
    _ ≤ (zy.1.divisors ×ˢ zy.2.natAbs.divisors).card := by
      apply card_le_card_of_injOn (fun p : ℕ × ℕ × ℕ => (p.1, p.2.2))
      · intro p hp
        obtain ⟨h, _hsource, heq⟩ := decomposition_witness hp
        have hdivz : p.1 ∣ zy.1 := by
          have hzEq := congrArg Prod.fst heq
          change p.1 * p.2.1 = zy.1 at hzEq
          rw [← hzEq]
          exact dvd_mul_right _ _
        have hdivy : p.2.2 ∣ zy.2.natAbs := by
          apply Int.natCast_dvd.mp
          have hyEq := congrArg Prod.snd heq
          change (p.2.2 : ℤ) * difference (p, h) = zy.2 at hyEq
          exact ⟨difference (p, h), hyEq.symm⟩
        exact mem_product.mpr
          ⟨Nat.mem_divisors.mpr ⟨hdivz, hz.ne'⟩,
            Nat.mem_divisors.mpr ⟨hdivy, (Int.natAbs_pos.mpr hy).ne'⟩⟩
      · intro a ha b hb heq
        obtain ⟨ha', hasource, haout⟩ := decomposition_witness ha
        obtain ⟨hb', _hbsource, hbout⟩ := decomposition_witness hb
        have hfirst : a.1 = b.1 := congrArg Prod.fst heq
        have hlast : a.2.2 = b.2.2 := congrArg Prod.snd heq
        have haz : a.1 * a.2.1 = zy.1 := congrArg Prod.fst haout
        have hbz : b.1 * b.2.1 = zy.1 := congrArg Prod.fst hbout
        have hapos := (mem_dyadicCarrier_iff.mp (source_data hasource).1).1
        have hmiddle : a.2.1 = b.2.1 := by
          apply Nat.eq_of_mul_eq_mul_left hapos
          calc
            a.1 * a.2.1 = zy.1 := haz
            _ = b.1 * b.2.1 := hbz.symm
            _ = a.1 * b.2.1 := by rw [hfirst]
        exact Prod.ext hfirst (Prod.ext hmiddle hlast)
    _ = zy.1.divisors.card * zy.2.natAbs.divisors.card := card_product _ _
    _ ≤ divisorMaximum S H F * divisorMaximum S H F := Nat.mul_le_mul hzc hyc
    _ = _ := (pow_two _).symm

private theorem fiber_cauchy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) (C : ℝ)
    (hC : ((A.image f).card : ℝ) ≤ C) :
    (A.card : ℝ) ^ 2 ≤ C * ∑ a ∈ A, ((A.filter (fun b => f b = f a)).card : ℝ) := by
  let B := A.image f
  have hcount : (∑ b ∈ B, ((A.filter (fun a => f a = b)).card : ℝ)) =
      (A.card : ℝ) := by
    exact_mod_cast (card_eq_sum_card_image f A).symm
  have hsecond :
      (∑ b ∈ B, ((A.filter (fun a => f a = b)).card : ℝ) ^ 2) =
        ∑ a ∈ A, ((A.filter (fun b => f b = f a)).card : ℝ) := by
    have hsum := sum_fiberwise_of_maps_to (s := A) (t := B) (g := f)
      (fun a ha => mem_image_of_mem f ha)
      (fun a => ((A.filter (fun b => f b = f a)).card : ℝ))
    rw [← hsum]
    apply sum_congr rfl
    intro b _
    calc
      ((A.filter (fun a => f a = b)).card : ℝ) ^ 2 =
          ∑ _a ∈ A.filter (fun a => f a = b),
            ((A.filter (fun a => f a = b)).card : ℝ) := by
        simp only [sum_const, nsmul_eq_mul, pow_two]
      _ = _ := by
        apply sum_congr rfl
        intro a ha
        rw [(mem_filter.mp ha).2]
  have hcs := sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ))
    (fun b => ((A.filter (fun a => f a = b)).card : ℝ))
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hcount, hsecond] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hC (sum_nonneg (by intros; positivity)))

private theorem row_fiber_card {S H F : ℝ}
    {t : (ℕ × ℕ × ℕ) × (ℤ × ℤ)} (ht : t ∈ sourceCarrier S H F) :
    ((outputFiber S H F (output t)).filter (fun u => u.1 = t.1)).card =
      (row H (t.1.1, t.1.2.1) (difference t)).card := by
  have hdata := source_data ht
  have hfpos := (mem_dyadicCarrier_iff.mp hdata.2.2.1).1
  have hfnz : (t.1.2.2 : ℤ) ≠ 0 := by exact_mod_cast hfpos.ne'
  apply card_bij' (fun u _ => u.2) (fun h _ => (t.1, h))
  · intro u hu
    obtain ⟨hu, hprefix⟩ := mem_filter.mp hu
    obtain ⟨husource, huout⟩ := mem_filter.mp hu
    have hudata := source_data husource
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hudata.2.2.2.1, hudata.2.2.2.2.1⟩, ?_⟩
    have hy := congrArg Prod.snd huout
    change (u.1.2.2 : ℤ) * difference u = (t.1.2.2 : ℤ) * difference t at hy
    rw [hprefix] at hy
    have hk := (mul_right_inj' hfnz).mp hy
    simpa only [difference, hprefix] using hk
  · intro h hh
    obtain ⟨hh, hk⟩ := mem_filter.mp hh
    have hsource : (t.1, h) ∈ sourceCarrier S H F := by
      apply mem_filter.mpr
      refine ⟨mem_product.mpr
        ⟨mem_product.mpr ⟨hdata.1, mem_product.mpr ⟨hdata.2.1, hdata.2.2.1⟩⟩, hh⟩, ?_⟩
      change h.1 * (t.1.1 : ℤ) - h.2 * (t.1.2.1 : ℤ) ≠ 0
      rw [hk]
      exact hdata.2.2.2.2.2
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨hsource, ?_⟩, rfl⟩
    apply Prod.ext rfl
    change (t.1.2.2 : ℤ) *
      (h.1 * (t.1.1 : ℤ) - h.2 * (t.1.2.1 : ℤ)) = _
    rw [hk]
  · intro u hu
    have hprefix := (mem_filter.mp hu).2
    exact Prod.ext hprefix.symm rfl
  · intro h _
    rfl

private theorem multiplicityL2_le_source_rows (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F) (nu : ℕ) :
    multiplicityL2 S H F nu ≤ (divisorMaximum S H F : ℝ) ^ 2 *
      ∑ t ∈ sourceCarrier S H F,
        if (nu : ℤ) ∣ (output t).2 then
          ((row H (t.1.1, t.1.2.1) (difference t)).card : ℝ) else 0 := by
  let A := sourceCarrier S H F
  let Z := A.image output
  let W := fun t : (ℕ × ℕ × ℕ) × (ℤ × ℤ) =>
    if (nu : ℤ) ∣ (output t).2 then
      ((row H (t.1.1, t.1.2.1) (difference t)).card : ℝ) else 0
  have hpoint : ∀ zy ∈ Z,
      (if (nu : ℤ) ∣ zy.2 then (multiplicity S H F zy.1 zy.2 : ℝ) ^ 2 else 0) ≤
        (divisorMaximum S H F : ℝ) ^ 2 * ∑ t ∈ outputFiber S H F zy, W t := by
    intro zy hzy
    have hc := fiber_cauchy (outputFiber S H F zy) Prod.fst
      ((divisorMaximum S H F : ℝ) ^ 2)
      (by exact_mod_cast card_decompositionCarrier_le hS hH hF hzy)
    have hinner :
        (∑ t ∈ outputFiber S H F zy,
          (((outputFiber S H F zy).filter (fun u => u.1 = t.1)).card : ℝ)) =
        ∑ t ∈ outputFiber S H F zy,
          ((row H (t.1.1, t.1.2.1) (difference t)).card : ℝ) := by
      apply sum_congr rfl
      intro t ht
      obtain ⟨htsource, htout⟩ := mem_filter.mp ht
      have h := row_fiber_card htsource
      rw [htout] at h
      exact_mod_cast h
    rw [hinner] at hc
    by_cases hd : (nu : ℤ) ∣ zy.2
    · rw [if_pos hd]
      have hw : (∑ t ∈ outputFiber S H F zy, W t) =
          ∑ t ∈ outputFiber S H F zy,
            ((row H (t.1.1, t.1.2.1) (difference t)).card : ℝ) := by
        apply sum_congr rfl
        intro t ht
        have heq := congrArg Prod.snd (mem_filter.mp ht).2
        simp only [W, heq, if_pos hd]
      rw [hw]
      exact hc
    · rw [if_neg hd]
      apply mul_nonneg (sq_nonneg _)
      apply sum_nonneg
      intro t _
      unfold W
      split_ifs <;> positivity
  have hsum := sum_fiberwise_of_maps_to (s := A) (t := Z) (g := output)
    (fun t ht => mem_image_of_mem output ht) W
  calc
    _ ≤ ∑ zy ∈ Z, (divisorMaximum S H F : ℝ) ^ 2 *
        ∑ t ∈ outputFiber S H F zy, W t := sum_le_sum hpoint
    _ = (divisorMaximum S H F : ℝ) ^ 2 *
        ∑ zy ∈ Z, ∑ t ∈ outputFiber S H F zy, W t := (mul_sum _ _ _).symm
    _ = _ := by rw [hsum]

private theorem difference_mem_frequency {H T : ℝ} (hH : 0 ≤ H) (hT : 0 ≤ T)
    {s : ℕ × ℕ} (hs₁ : (s.1 : ℝ) ≤ 2 * T) (hs₂ : (s.2 : ℝ) ≤ 2 * T)
    {h : ℤ × ℤ} (hh : h ∈ frequencyCarrier H ×ˢ frequencyCarrier H)
    (hne : h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) ≠ 0) :
    h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) ∈ frequencyCarrier (4 * H * T) := by
  apply (mem_frequencyCarrier_iff (by positivity)).mpr
  refine ⟨hne, ?_⟩
  have hh₁ := frequency_norm_bound hH (mem_product.mp hh).1
  have hh₂ := frequency_norm_bound hH (mem_product.mp hh).2
  have hb : |(h.1 : ℝ) * (s.1 : ℝ) - (h.2 : ℝ) * (s.2 : ℝ)| ≤ 4 * H * T := by
    calc
      _ ≤ |(h.1 : ℝ) * (s.1 : ℝ)| + |(h.2 : ℝ) * (s.2 : ℝ)| := abs_sub _ _
      _ = |(h.1 : ℝ)| * (s.1 : ℝ) + |(h.2 : ℝ)| * (s.2 : ℝ) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ H * (2 * T) + H * (2 * T) :=
        add_le_add (mul_le_mul hh₁ hs₁ (Nat.cast_nonneg _) hH)
          (mul_le_mul hh₂ hs₂ (Nat.cast_nonneg _) hH)
      _ = _ := by ring
  have habs :
      ((h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ)).natAbs : ℝ) =
        |(h.1 : ℝ) * (s.1 : ℝ) - (h.2 : ℝ) * (s.2 : ℝ)| := by
    have h := Int.natCast_natAbs (h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ))
    exact_mod_cast h
  rwa [habs]

private theorem row_fiberwise (H L : ℝ) (hL : 0 ≤ L)
    (s : ℕ × ℕ) (w : ℤ → ℝ)
    (hmap : ∀ h ∈ frequencyCarrier H ×ˢ frequencyCarrier H,
      h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) ≠ 0 →
        h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) ∈ frequencyCarrier L) :
    (∑ h ∈ (frequencyCarrier H ×ˢ frequencyCarrier H).filter
      (fun h => h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) ≠ 0),
        w (h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ))) =
      ∑ k ∈ frequencyCarrier L, ((row H s k).card : ℝ) * w k := by
  let A := (frequencyCarrier H ×ˢ frequencyCarrier H).filter
    (fun h => h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) ≠ 0)
  let f := fun h : ℤ × ℤ => h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ)
  have hsum := sum_fiberwise_of_maps_to (s := A) (t := frequencyCarrier L) (g := f)
    (fun h hh => hmap h (mem_filter.mp hh).1 (mem_filter.mp hh).2) (fun h => w (f h))
  rw [← hsum]
  apply sum_congr rfl
  intro k hk
  have hkne := ((mem_frequencyCarrier_iff hL).mp hk).1
  have hset : A.filter (fun h => f h = k) = row H s k := by
    ext h
    simp only [A, f, row, mem_filter]
    constructor
    · rintro ⟨⟨hh, _hne⟩, heq⟩
      exact ⟨hh, heq⟩
    · rintro ⟨hh, heq⟩
      exact ⟨⟨hh, by rwa [heq]⟩, heq⟩
  calc
    _ = ∑ _h ∈ A.filter (fun h => f h = k), w k := by
      apply sum_congr rfl
      intro h hh
      rw [(mem_filter.mp hh).2]
    _ = ((row H s k).card : ℝ) * w k := by
      rw [hset]
      simp only [sum_const, nsmul_eq_mul]

private theorem source_rows_eq_moment (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (nu : ℕ) :
    (∑ t ∈ sourceCarrier S H F,
        if (nu : ℤ) ∣ (output t).2 then
          ((row H (t.1.1, t.1.2.1) (difference t)).card : ℝ) else 0) =
      ∑ s₁ ∈ dyadicCarrier S, ∑ s₂ ∈ dyadicCarrier S,
        ∑ k ∈ frequencyCarrier (4 * H * S), ((row H (s₁, s₂) k).card : ℝ) ^ 2 *
          (((dyadicCarrier F).filter (fun f => (nu : ℤ) ∣ (f : ℤ) * k)).card : ℝ) := by
  have hS0 : 0 ≤ S := by linarith
  have hH0 : 0 ≤ H := by linarith
  calc
    _ = ∑ s₁ ∈ dyadicCarrier S, ∑ s₂ ∈ dyadicCarrier S, ∑ f ∈ dyadicCarrier F,
        ∑ h ∈ (frequencyCarrier H ×ˢ frequencyCarrier H).filter
          (fun h => h.1 * (s₁ : ℤ) - h.2 * (s₂ : ℤ) ≠ 0),
          if (nu : ℤ) ∣ (f : ℤ) * (h.1 * (s₁ : ℤ) - h.2 * (s₂ : ℤ)) then
            ((row H (s₁, s₂) (h.1 * (s₁ : ℤ) - h.2 * (s₂ : ℤ))).card : ℝ) else 0 := by
      simp only [sourceCarrier, sum_filter, sum_product, output, difference]
    _ = ∑ s₁ ∈ dyadicCarrier S, ∑ s₂ ∈ dyadicCarrier S, ∑ f ∈ dyadicCarrier F,
        ∑ k ∈ frequencyCarrier (4 * H * S),
          if (nu : ℤ) ∣ (f : ℤ) * k then ((row H (s₁, s₂) k).card : ℝ) ^ 2 else 0 := by
      apply sum_congr rfl
      intro s₁ hs₁
      apply sum_congr rfl
      intro s₂ hs₂
      apply sum_congr rfl
      intro f _
      have hmap := fun h hh hne => difference_mem_frequency hH0 hS0
        (mem_dyadicCarrier_iff.mp hs₁).2.2.le (mem_dyadicCarrier_iff.mp hs₂).2.2.le hh hne
      rw [row_fiberwise H (4 * H * S) (by positivity) (s₁, s₂)
        (fun k => if (nu : ℤ) ∣ (f : ℤ) * k then
          ((row H (s₁, s₂) k).card : ℝ) else 0) hmap]
      apply sum_congr rfl
      intro k _
      by_cases hd : (nu : ℤ) ∣ (f : ℤ) * k <;> simp only [hd, if_true, if_false, mul_zero, pow_two]
    _ = _ := by
      apply sum_congr rfl
      intro s₁ _
      apply sum_congr rfl
      intro s₂ _
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      have hc : (((dyadicCarrier F).filter
          (fun f => (nu : ℤ) ∣ (f : ℤ) * k)).card : ℝ) =
          ∑ f ∈ dyadicCarrier F, if (nu : ℤ) ∣ (f : ℤ) * k then (1 : ℝ) else 0 := by
        simp only [card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero]
      rw [hc, mul_sum]
      apply sum_congr rfl
      intro f _
      by_cases hd : (nu : ℤ) ∣ (f : ℤ) * k <;> simp only [hd, if_true, if_false, mul_one, mul_zero]

private theorem card_integer_progression_le (A : Finset ℤ) (H : ℝ) (hH : 0 ≤ H)
    (m : ℕ) (hm : 0 < m) (hbound : ∀ a ∈ A, |(a : ℝ)| ≤ H)
    (hmod : ∀ a ∈ A, ∀ b ∈ A, (m : ℤ) ∣ a - b) :
    (A.card : ℝ) ≤ 1 + 2 * H / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hA : A.Nonempty
  · let a₀ := A.min' hA
    have ha₀ : a₀ ∈ A := A.min'_mem hA
    let q := fun a : ℤ => ((a - a₀) / (m : ℤ)).toNat
    have hrepr : ∀ a ∈ A, a = a₀ + (m : ℤ) * (q a : ℤ) := by
      intro a ha
      have hnonneg : 0 ≤ a - a₀ := sub_nonneg.mpr (A.min'_le a ha)
      have hqnonneg : 0 ≤ (a - a₀) / (m : ℤ) :=
        Int.ediv_nonneg hnonneg (by exact_mod_cast hm.le)
      have hqcast : (q a : ℤ) = (a - a₀) / (m : ℤ) := Int.toNat_of_nonneg hqnonneg
      have heq : (m : ℤ) * (q a : ℤ) = a - a₀ := by
        rw [hqcast, mul_comm]
        exact Int.ediv_mul_cancel (hmod a ha a₀ ha₀)
      omega
    have hc : A.card ≤ (Icc 0 (Nat.floor (2 * H / m))).card := by
      apply card_le_card_of_injOn q
      · intro a ha
        have hr : (m : ℝ) * (q a : ℝ) = (a : ℝ) - (a₀ : ℝ) := by
          have h := hrepr a ha
          exact_mod_cast (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm))
        have ha := abs_le.mp (hbound a ha)
        have hb := abs_le.mp (hbound a₀ ha₀)
        have hqbound : (q a : ℝ) ≤ 2 * H / m := by
          apply (le_div_iff₀ hmR).mpr
          nlinarith
        exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hqbound⟩
      · intro a ha b hb hab
        rw [hrepr a ha, hrepr b hb, hab]
    calc
      _ ≤ ((Icc 0 (Nat.floor (2 * H / m))).card : ℝ) := by exact_mod_cast hc
      _ = (Nat.floor (2 * H / m) : ℝ) + 1 := by
        simp only [Nat.card_Icc, Nat.sub_zero, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := by linarith [Nat.floor_le (div_nonneg (by positivity) hmR.le)]
  · have hEmpty : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    rw [hEmpty, card_empty, Nat.cast_zero]
    positivity

private theorem row_first_coordinate_congruence {H : ℝ} {s : ℕ × ℕ} {k : ℤ}
    (hs₁ : 0 < s.1) {h j : ℤ × ℤ}
    (hh : h ∈ row H s k) (hj : j ∈ row H s k) :
    ((s.2 / s.1.gcd s.2 : ℕ) : ℤ) ∣ h.1 - j.1 := by
  let d := s.1.gcd s.2
  let u := s.1 / d
  let v := s.2 / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ hs₁
  have hdu : (d : ℤ) * (u : ℤ) = (s.1 : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left s.1 s.2)
  have hdv : (d : ℤ) * (v : ℤ) = (s.2 : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right s.1 s.2)
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hd
  have hhEq := (mem_filter.mp hh).2
  have hjEq := (mem_filter.mp hj).2
  have hscaled : (h.1 - j.1) * (u : ℤ) = (h.2 - j.2) * (v : ℤ) := by
    apply (mul_right_inj' (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')).mp
    calc
      (d : ℤ) * ((h.1 - j.1) * (u : ℤ)) = (h.1 - j.1) * (s.1 : ℤ) := by
        rw [← hdu]
        ring
      _ = (h.2 - j.2) * (s.2 : ℤ) := by nlinarith [hhEq, hjEq]
      _ = (d : ℤ) * ((h.2 - j.2) * (v : ℤ)) := by rw [← hdv]; ring
  have hdiv : (v : ℤ) ∣ (h.1 - j.1) * (u : ℤ) := by
    rw [hscaled]
    exact dvd_mul_left _ _
  have hgcd : Int.gcd (v : ℤ) (u : ℤ) = 1 := by
    change v.gcd u = 1
    exact hcop.symm.gcd_eq_one
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hdiv hgcd

private theorem row_card_le (S H : ℝ) (hS : 1 ≤ S) (hH : 0 ≤ H)
    {s₁ s₂ : ℕ} (hs₁ : s₁ ∈ dyadicCarrier S) (hs₂ : s₂ ∈ dyadicCarrier S)
    (k : ℤ) :
    ((row H (s₁, s₂) k).card : ℝ) ≤ 1 + 2 * H * (s₁.gcd s₂ : ℝ) / S := by
  let A := (row H (s₁, s₂) k).image Prod.fst
  have hs₁pos := (mem_dyadicCarrier_iff.mp hs₁).1
  have hs₂pos := (mem_dyadicCarrier_iff.mp hs₂).1
  let d := s₁.gcd s₂
  let v := s₂ / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ hs₁pos
  have hv : 0 < v := Nat.div_gcd_pos_of_pos_right _ hs₂pos
  have hAcard : A.card = (row H (s₁, s₂) k).card := by
    apply card_image_of_injOn
    intro h hh j hj heq
    have hhEq := (mem_filter.mp hh).2
    have hjEq := (mem_filter.mp hj).2
    have hfirst : h.1 = j.1 := heq
    have hsecond : h.2 = j.2 := by
      apply (mul_left_inj' (show (s₂ : ℤ) ≠ 0 by exact_mod_cast hs₂pos.ne')).mp
      rw [hfirst] at hhEq
      nlinarith [hhEq, hjEq]
    exact Prod.ext hfirst hsecond
  have hprogression : (A.card : ℝ) ≤ 1 + 2 * H / (v : ℝ) := by
    apply card_integer_progression_le A H hH v hv
    · intro a ha
      obtain ⟨h, hh, rfl⟩ := mem_image.mp ha
      exact frequency_norm_bound hH (mem_product.mp (mem_filter.mp hh).1).1
    · intro a ha b hb
      obtain ⟨h, hh, rfl⟩ := mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
      exact row_first_coordinate_congruence hs₁pos hh hj
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hSpos : 0 < S := by linarith
  have hfact : (d : ℝ) * (v : ℝ) = (s₂ : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right s₁ s₂)
  have hratio : 2 * H / (v : ℝ) ≤ 2 * H * (d : ℝ) / S := by
    apply (div_le_div_iff₀ hvR hSpos).mpr
    have hlo := (mem_dyadicCarrier_iff.mp hs₂).2.1
    calc
      (2 * H) * S ≤ (2 * H) * (s₂ : ℝ) := mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = (2 * H * (d : ℝ)) * (v : ℝ) := by rw [← hfact]; ring
  rw [hAcard] at hprogression
  exact hprogression.trans (add_le_add le_rfl hratio)

private theorem row_square_le (S H : ℝ) (hS : 1 ≤ S) (hH : 0 ≤ H)
    {s₁ s₂ : ℕ} (hs₁ : s₁ ∈ dyadicCarrier S) (hs₂ : s₂ ∈ dyadicCarrier S) (k : ℤ) :
    ((row H (s₁, s₂) k).card : ℝ) ^ 2 ≤
      ((row H (s₁, s₂) k).card : ℝ) +
        (2 * H / S) * (s₁.gcd s₂ : ℝ) * ((row H (s₁, s₂) k).card : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (row_card_le S H hS hH hs₁ hs₂ k)
    (Nat.cast_nonneg (row H (s₁, s₂) k).card)
  nlinarith

private theorem linear_first_moment_le (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F)
    (d : ℕ) (hd : 0 < d) (V : Finset ℕ)
    (hV : V ⊆ Ioc 0 (Nat.floor (2 * S / d))) (k : ℤ) :
    (∑ s ∈ V ×ˢ V, ((row H s k).card : ℝ)) ≤
      (4 * H * S / d) * (divisorMaximum S H F : ℝ) := by
  let Q := (V ×ˢ V).sigma (fun s => row H s k)
  let f := fun q : Σ _ : ℕ × ℕ, ℤ × ℤ => (q.2.1, q.1.1)
  have hH0 : 0 ≤ H := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdone : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.succ_le_iff.mpr hd)
  have hU0 : 0 ≤ 2 * S / d := by positivity
  have hpair : ∀ q ∈ Q, q.1 ∈ V ×ˢ V ∧ q.2 ∈ row H q.1 k := by
    intro q hq
    exact mem_sigma.mp hq
  have hmap : ∀ q ∈ Q, f q ∈ frequencyCarrier H ×ˢ V := by
    intro q hq
    obtain ⟨hs, hh⟩ := hpair q hq
    exact mem_product.mpr
      ⟨(mem_product.mp (mem_filter.mp hh).1).1, (mem_product.mp hs).1⟩
  have hfiber : ∀ a ∈ frequencyCarrier H ×ˢ V,
      ((Q.filter (fun q => f q = a)).card : ℝ) ≤ (divisorMaximum S H F : ℝ) := by
    intro a _ha
    let A := Q.filter (fun q => f q = a)
    by_cases hA : A.Nonempty
    · obtain ⟨q₀, hq₀⟩ := hA
      let n : ℤ := a.1 * (a.2 : ℤ) - k
      have hidentity : ∀ q ∈ A, n = q.2.2 * (q.1.2 : ℤ) := by
        intro q hq
        obtain ⟨hq, heq⟩ := mem_filter.mp hq
        obtain ⟨_hs, hh⟩ := hpair q hq
        have h₁ : q.2.1 = a.1 := congrArg Prod.fst heq
        have hu : q.1.1 = a.2 := congrArg Prod.snd heq
        have hrow := (mem_filter.mp hh).2
        change a.1 * (a.2 : ℤ) - k = _
        rw [← h₁, ← hu]
        nlinarith [hrow]
      obtain ⟨hs₀, hh₀⟩ := hpair q₀ (mem_filter.mp hq₀).1
      have hv₀ := hV (mem_product.mp hs₀).2
      have hv₀pos := (mem_Ioc.mp hv₀).1
      have hh₂₀ := (mem_product.mp (mem_filter.mp hh₀).1).2
      have hh₂₀ne := ((mem_frequencyCarrier_iff hH0).mp hh₂₀).1
      have hn : n ≠ 0 := by
        rw [hidentity q₀ hq₀]
        exact mul_ne_zero hh₂₀ne (by exact_mod_cast hv₀pos.ne')
      have hnabs : (n.natAbs : ℝ) ≤ max (4 * S ^ 2) (8 * F * H * S) := by
        have hvupper : (q₀.1.2 : ℝ) ≤ 2 * S / d :=
          (show (q₀.1.2 : ℝ) ≤ (Nat.floor (2 * S / d) : ℝ) by
            exact_mod_cast (mem_Ioc.mp hv₀).2).trans (Nat.floor_le hU0)
        have hhbound := frequency_norm_bound hH0 hh₂₀
        have hprod : (n.natAbs : ℝ) ≤ H * (2 * S / d) := by
          have heq : (n.natAbs : ℝ) = |(q₀.2.2 : ℝ)| * (q₀.1.2 : ℝ) := by
            rw [hidentity q₀ hq₀, Int.natAbs_mul, Nat.cast_mul, Int.natAbs_natCast]
            congr 1
            exact_mod_cast Int.natCast_natAbs q₀.2.2
          rw [heq]
          exact mul_le_mul hhbound hvupper (Nat.cast_nonneg _) hH0
        have hquot : 2 * S / d ≤ 2 * S := div_le_self (by positivity) hdone
        have hcap : H * (2 * S / d) ≤ 8 * F * H * S := by
          calc
            _ ≤ H * (2 * S) := mul_le_mul_of_nonneg_left hquot hH0
            _ = 2 * (H * S) := by ring
            _ ≤ (8 * F) * (H * S) :=
              mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hH0 hS0)
            _ = _ := by ring
        exact (hprod.trans hcap).trans (le_max_right _ _)
      have htau := tau_le_divisorMaximum (Int.natAbs_pos.mpr hn) hnabs
      have hc : A.card ≤ n.natAbs.divisors.card := by
        apply card_le_card_of_injOn (fun q : Σ _ : ℕ × ℕ, ℤ × ℤ => q.1.2)
        · intro q hq
          apply Nat.mem_divisors.mpr
          refine ⟨?_, (Int.natAbs_pos.mpr hn).ne'⟩
          apply Int.natCast_dvd.mp
          exact ⟨q.2.2, by rw [hidentity q hq, mul_comm]⟩
        · intro q hq r hr hv
          have hqf := (mem_filter.mp hq).2
          have hrf := (mem_filter.mp hr).2
          have hu : q.1.1 = r.1.1 := by
            exact (congrArg Prod.snd hqf).trans (congrArg Prod.snd hrf).symm
          have hh₁ : q.2.1 = r.2.1 := by
            exact (congrArg Prod.fst hqf).trans (congrArg Prod.fst hrf).symm
          obtain ⟨hqs, hqh⟩ := hpair q (mem_filter.mp hq).1
          obtain ⟨_hrs, hrh⟩ := hpair r (mem_filter.mp hr).1
          have hqvpos := (mem_Ioc.mp (hV (mem_product.mp hqs).2)).1
          have hqeq := (mem_filter.mp hqh).2
          have hreq := (mem_filter.mp hrh).2
          have hh₂ : q.2.2 = r.2.2 := by
            apply (mul_left_inj'
              (show (q.1.2 : ℤ) ≠ 0 by exact_mod_cast hqvpos.ne')).mp
            rw [← hu, ← hh₁, ← hv] at hreq
            nlinarith [hqeq, hreq]
          apply Sigma.ext (Prod.ext hu hv)
          exact heq_of_eq (Prod.ext hh₁ hh₂)
      exact_mod_cast hc.trans htau
    · have hEmpty : A = ∅ := not_nonempty_iff_eq_empty.mp hA
      change (A.card : ℝ) ≤ _
      rw [hEmpty, card_empty, Nat.cast_zero]
      positivity
  have hcard := card_le_sum_fiber_bound Q (frequencyCarrier H ×ˢ V) f
    (fun _ => (divisorMaximum S H F : ℝ)) hmap hfiber
  have hVcard : (V.card : ℝ) ≤ 2 * S / d := by
    calc
      _ ≤ ((Ioc 0 (Nat.floor (2 * S / d))).card : ℝ) := by exact_mod_cast card_le_card hV
      _ = (Nat.floor (2 * S / d) : ℝ) := by simp only [Nat.card_Ioc, Nat.sub_zero]
      _ ≤ _ := Nat.floor_le hU0
  calc
    _ = (Q.card : ℝ) := by simp only [Q, card_sigma, Nat.cast_sum]
    _ ≤ (frequencyCarrier H).card * (V.card : ℝ) * (divisorMaximum S H F : ℝ) := by
      simpa only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul] using hcard
    _ ≤ (2 * H) * (2 * S / d) * (divisorMaximum S H F : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (card_frequencyCarrier_le hH0) hVcard (Nat.cast_nonneg _) (by positivity))
        (Nat.cast_nonneg _)
    _ = _ := by ring

private def hPairs (H : ℝ) (s : ℕ × ℕ) : Finset (ℤ × ℤ) :=
  (frequencyCarrier H ×ˢ frequencyCarrier H).filter
    (fun h => h.1 * (s.1 : ℤ) - h.2 * (s.2 : ℤ) ≠ 0)

private theorem sigma_hPairs_sum_eq (V : Finset ℕ) (H T : ℝ)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hV : V ⊆ Ioc 0 (Nat.floor (2 * T)))
    (w : (ℕ × ℕ) → ℤ → ℝ) :
    (∑ q ∈ (V ×ˢ V).sigma (hPairs H),
      w q.1 (q.2.1 * (q.1.1 : ℤ) - q.2.2 * (q.1.2 : ℤ))) =
      ∑ s ∈ V ×ˢ V, ∑ k ∈ frequencyCarrier (4 * H * T),
        ((row H s k).card : ℝ) * w s k := by
  rw [sum_sigma]
  apply sum_congr rfl
  intro s hs
  have h₁ := (mem_Ioc.mp (hV (mem_product.mp hs).1)).2
  have h₂ := (mem_Ioc.mp (hV (mem_product.mp hs).2)).2
  have h₁R : (s.1 : ℝ) ≤ 2 * T :=
    (show (s.1 : ℝ) ≤ (Nat.floor (2 * T) : ℝ) by exact_mod_cast h₁).trans
      (Nat.floor_le (by positivity))
  have h₂R : (s.2 : ℝ) ≤ 2 * T :=
    (show (s.2 : ℝ) ≤ (Nat.floor (2 * T) : ℝ) by exact_mod_cast h₂).trans
      (Nat.floor_le (by positivity))
  exact row_fiberwise H (4 * H * T) (by positivity) s (w s)
    (fun h hh hne => difference_mem_frequency hH hT h₁R h₂R hh hne)

private theorem reduced_weighted_sum_le (S H : ℝ) (hS : 1 ≤ S) (hH : 1 ≤ H)
    (nu : ℕ) :
    (∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
      ∑ k ∈ frequencyCarrier (4 * H * S),
        (s.1.gcd s.2 : ℝ) * ((row H s k).card : ℝ) * (nu.gcd k.natAbs : ℝ)) ≤
      ∑ d ∈ Icc 1 (Nat.floor (2 * S)), (d : ℝ) *
        ∑ s ∈ Ioc 0 (Nat.floor (2 * S / d)) ×ˢ Ioc 0 (Nat.floor (2 * S / d)),
          ∑ k ∈ frequencyCarrier (4 * H * (S / d)),
            ((row H s k).card : ℝ) * (nu.gcd ((d : ℤ) * k).natAbs : ℝ) := by
  let A := (dyadicCarrier S ×ˢ dyadicCarrier S).sigma (hPairs H)
  let T := (Icc 1 (Nat.floor (2 * S))).sigma (fun d =>
    (Ioc 0 (Nat.floor (2 * S / d)) ×ˢ Ioc 0 (Nat.floor (2 * S / d))).sigma (hPairs H))
  let g := fun q : Σ _ : ℕ × ℕ, ℤ × ℤ =>
    (⟨q.1.1.gcd q.1.2, ⟨(q.1.1 / q.1.1.gcd q.1.2,
      q.1.2 / q.1.1.gcd q.1.2), q.2⟩⟩ : Σ _ : ℕ, Σ _ : ℕ × ℕ, ℤ × ℤ)
  let W := fun q : Σ _ : ℕ × ℕ, ℤ × ℤ =>
    (q.1.1.gcd q.1.2 : ℝ) *
      (nu.gcd (q.2.1 * (q.1.1 : ℤ) - q.2.2 * (q.1.2 : ℤ)).natAbs : ℝ)
  let V := fun r : Σ _ : ℕ, Σ _ : ℕ × ℕ, ℤ × ℤ =>
    (r.1 : ℝ) * (nu.gcd ((r.1 : ℤ) *
      (r.2.2.1 * (r.2.1.1 : ℤ) - r.2.2.2 * (r.2.1.2 : ℤ))).natAbs : ℝ)
  have hS0 : 0 ≤ S := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hdata : ∀ q ∈ A,
      q.1.1 ∈ dyadicCarrier S ∧ q.1.2 ∈ dyadicCarrier S ∧ q.2 ∈ hPairs H q.1 := by
    intro q hq
    obtain ⟨hs, hh⟩ := mem_sigma.mp hq
    exact ⟨(mem_product.mp hs).1, (mem_product.mp hs).2, hh⟩
  have hfactor : ∀ q ∈ A,
      (q.1.1.gcd q.1.2 : ℤ) *
        (q.2.1 * ((q.1.1 / q.1.1.gcd q.1.2 : ℕ) : ℤ) -
          q.2.2 * ((q.1.2 / q.1.1.gcd q.1.2 : ℕ) : ℤ)) =
        q.2.1 * (q.1.1 : ℤ) - q.2.2 * (q.1.2 : ℤ) := by
    intro q _
    have h₁ : (q.1.1.gcd q.1.2 : ℤ) *
        ((q.1.1 / q.1.1.gcd q.1.2 : ℕ) : ℤ) = (q.1.1 : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left q.1.1 q.1.2)
    have h₂ : (q.1.1.gcd q.1.2 : ℤ) *
        ((q.1.2 / q.1.1.gcd q.1.2 : ℕ) : ℤ) = (q.1.2 : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right q.1.1 q.1.2)
    calc
      _ = q.2.1 * ((q.1.1.gcd q.1.2 : ℤ) *
          ((q.1.1 / q.1.1.gcd q.1.2 : ℕ) : ℤ)) -
          q.2.2 * ((q.1.1.gcd q.1.2 : ℤ) *
            ((q.1.2 / q.1.1.gcd q.1.2 : ℕ) : ℤ)) := by ring
      _ = _ := by rw [h₁, h₂]
  have hmap : ∀ q ∈ A, g q ∈ T := by
    intro q hq
    obtain ⟨hs₁, hs₂, hh⟩ := hdata q hq
    let d := q.1.1.gcd q.1.2
    have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (mem_dyadicCarrier_iff.mp hs₁).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hdBound : d ≤ Nat.floor (2 * S) := by
      apply Nat.le_floor
      exact (show (d : ℝ) ≤ (q.1.1 : ℝ) by
        exact_mod_cast Nat.gcd_le_left q.1.2 (mem_dyadicCarrier_iff.mp hs₁).1).trans
        (mem_dyadicCarrier_iff.mp hs₁).2.2.le
    have hu : q.1.1 / d ∈ Ioc 0 (Nat.floor (2 * S / d)) := by
      refine mem_Ioc.mpr
        ⟨Nat.div_gcd_pos_of_pos_left _ (mem_dyadicCarrier_iff.mp hs₁).1, ?_⟩
      apply Nat.le_floor
      apply (le_div_iff₀ hdR).mpr
      have heq : ((q.1.1 / d : ℕ) : ℝ) * d = (q.1.1 : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left q.1.1 q.1.2)
      rw [heq]
      exact (mem_dyadicCarrier_iff.mp hs₁).2.2.le
    have hv : q.1.2 / d ∈ Ioc 0 (Nat.floor (2 * S / d)) := by
      refine mem_Ioc.mpr
        ⟨Nat.div_gcd_pos_of_pos_right _ (mem_dyadicCarrier_iff.mp hs₂).1, ?_⟩
      apply Nat.le_floor
      apply (le_div_iff₀ hdR).mpr
      have heq : ((q.1.2 / d : ℕ) : ℝ) * d = (q.1.2 : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right q.1.1 q.1.2)
      rw [heq]
      exact (mem_dyadicCarrier_iff.mp hs₂).2.2.le
    apply mem_sigma.mpr
    refine ⟨mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hd, hdBound⟩, mem_sigma.mpr
      ⟨mem_product.mpr ⟨hu, hv⟩, ?_⟩⟩
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp hh).1, ?_⟩
    intro hzero
    have hneq := (mem_filter.mp hh).2
    apply hneq
    rw [← hfactor q hq, hzero, mul_zero]
  have hinj : Set.InjOn g A := by
    intro q _hq r _hr heq
    have hd := congrArg (fun z : Σ _ : ℕ, Σ _ : ℕ × ℕ, ℤ × ℤ => z.1) heq
    have huv := congrArg (fun z : Σ _ : ℕ, Σ _ : ℕ × ℕ, ℤ × ℤ => z.2.1) heq
    have hh := congrArg (fun z : Σ _ : ℕ, Σ _ : ℕ × ℕ, ℤ × ℤ => z.2.2) heq
    have hs₁ : q.1.1 = r.1.1 := by
      calc
        q.1.1 = q.1.1.gcd q.1.2 * (q.1.1 / q.1.1.gcd q.1.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
        _ = r.1.1.gcd r.1.2 * (r.1.1 / r.1.1.gcd r.1.2) := by
          exact congrArg₂ (fun a b : ℕ => a * b) hd (congrArg Prod.fst huv)
        _ = r.1.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hs₂ : q.1.2 = r.1.2 := by
      calc
        q.1.2 = q.1.1.gcd q.1.2 * (q.1.2 / q.1.1.gcd q.1.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
        _ = r.1.1.gcd r.1.2 * (r.1.2 / r.1.1.gcd r.1.2) := by
          exact congrArg₂ (fun a b : ℕ => a * b) hd (congrArg Prod.snd huv)
        _ = r.1.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    apply Sigma.ext (Prod.ext hs₁ hs₂)
    exact heq_of_eq hh
  have hweight : ∀ q ∈ A, W q ≤ V (g q) := by
    intro q hq
    apply le_of_eq
    change _ = (q.1.1.gcd q.1.2 : ℝ) * _
    rw [hfactor q hq]
  have hsum := sum_le_sum_injective_map A T g W V hmap hinj hweight
    (by intros; dsimp [V]; positivity)
  have hleft :
      (∑ q ∈ A, W q) =
      ∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S, ∑ k ∈ frequencyCarrier (4 * H * S),
        (s.1.gcd s.2 : ℝ) * ((row H s k).card : ℝ) * (nu.gcd k.natAbs : ℝ) := by
    rw [sigma_hPairs_sum_eq (dyadicCarrier S) H S hH0 hS0 (filter_subset _ _)]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro k _
    ring
  have hright :
      (∑ r ∈ T, V r) =
      ∑ d ∈ Icc 1 (Nat.floor (2 * S)), (d : ℝ) *
        ∑ s ∈ Ioc 0 (Nat.floor (2 * S / d)) ×ˢ Ioc 0 (Nat.floor (2 * S / d)),
          ∑ k ∈ frequencyCarrier (4 * H * (S / d)),
            ((row H s k).card : ℝ) * (nu.gcd ((d : ℤ) * k).natAbs : ℝ) := by
    rw [sum_sigma]
    apply sum_congr rfl
    intro d hd
    have hdpos : 0 < d := by have := (mem_Icc.mp hd).1; omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hVeq : Ioc 0 (Nat.floor (2 * S / d)) = Ioc 0 (Nat.floor (2 * (S / d))) := by
      congr 2
      ring
    rw [hVeq, sigma_hPairs_sum_eq _ H (S / d) hH0 (by positivity) (by intro n hn; exact hn)]
    simp only [V, mul_sum]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro k _
    ring
  rwa [hleft, hright] at hsum

private theorem bounded_first_moment_gcd_le (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F) (nu : ℕ) (hnu : 0 < nu)
    (d : ℕ) (hd : 0 < d) (V : Finset ℕ)
    (hV : V ⊆ Ioc 0 (Nat.floor (2 * S / d))) :
    (∑ s ∈ V ×ˢ V, ∑ k ∈ frequencyCarrier (4 * H * (S / d)),
      ((row H s k).card : ℝ) * (nu.gcd ((d : ℤ) * k).natAbs : ℝ)) ≤
      32 * (divisorMaximum S H F : ℝ) * (nu.divisors.card : ℝ) *
        (H * S) ^ 2 / (d : ℝ) ^ 2 * (d.gcd nu : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hS0 : 0 ≤ S := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hprod : ∀ k : ℤ,
      (nu.gcd ((d : ℤ) * k).natAbs : ℝ) ≤
        (d.gcd nu : ℝ) * (nu.gcd k.natAbs : ℝ) := by
    intro k
    have hpositive : 0 < nu.gcd d * nu.gcd k.natAbs :=
      Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hnu) (Nat.gcd_pos_of_pos_left _ hnu)
    have hle := Nat.le_of_dvd hpositive (Nat.gcd_mul_right_dvd_mul_gcd nu d k.natAbs)
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, Nat.cast_mul, Nat.gcd_comm d nu]
      using (show (nu.gcd (d * k.natAbs) : ℝ) ≤
        (nu.gcd d : ℝ) * (nu.gcd k.natAbs : ℝ) by exact_mod_cast hle)
  calc
    _ = ∑ k ∈ frequencyCarrier (4 * H * (S / d)),
        (∑ s ∈ V ×ˢ V, ((row H s k).card : ℝ)) *
          (nu.gcd ((d : ℤ) * k).natAbs : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      exact (sum_mul _ _ _).symm
    _ ≤ ∑ k ∈ frequencyCarrier (4 * H * (S / d)),
        ((4 * H * S / d) * (divisorMaximum S H F : ℝ)) *
          ((d.gcd nu : ℝ) * (nu.gcd k.natAbs : ℝ)) := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul (linear_first_moment_le S H F hS hH hF d hd V hV k)
        (hprod k) (Nat.cast_nonneg _) (by positivity)
    _ = ((4 * H * S / d) * (divisorMaximum S H F : ℝ)) * (d.gcd nu : ℝ) *
        ∑ k ∈ frequencyCarrier (4 * H * (S / d)), (nu.gcd k.natAbs : ℝ) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ ((4 * H * S / d) * (divisorMaximum S H F : ℝ)) * (d.gcd nu : ℝ) *
        (2 * (4 * H * (S / d)) * (nu.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_frequency_gcd_le nu hnu (4 * H * (S / d)) (by positivity)) (by positivity)
    _ = _ := by field_simp [hdR.ne']; ring

private theorem first_moment_gcd_le (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F) (nu : ℕ) (hnu : 0 < nu) :
    (∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
      ∑ k ∈ frequencyCarrier (4 * H * S),
        ((row H s k).card : ℝ) * (nu.gcd k.natAbs : ℝ)) ≤
      32 * (divisorMaximum S H F : ℝ) * (nu.divisors.card : ℝ) * (H * S) ^ 2 := by
  have h := bounded_first_moment_gcd_le S H F hS hH hF nu hnu 1 (by norm_num)
    (dyadicCarrier S) (by simpa only [Nat.cast_one, div_one] using (filter_subset
      (fun n => S ≤ (n : ℝ) ∧ (n : ℝ) < 2 * S) (Ioc 0 (Nat.floor (2 * S)))))
  simpa only [Nat.cast_one, Int.natCast_one, div_one, one_mul, one_pow,
    Nat.gcd_one_left, Nat.cast_one, mul_one] using h

private theorem gcd_weighted_first_moment_le (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F) (nu : ℕ) (hnu : 0 < nu) :
    (∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
      ∑ k ∈ frequencyCarrier (4 * H * S),
        (s.1.gcd s.2 : ℝ) * ((row H s k).card : ℝ) * (nu.gcd k.natAbs : ℝ)) ≤
      32 * (divisorMaximum S H F : ℝ) * (nu.divisors.card : ℝ) ^ 2 *
        (H * S) ^ 2 * (harmonic (Nat.floor (2 * S)) : ℝ) := by
  have hred := reduced_weighted_sum_le S H hS hH nu
  calc
    _ ≤ ∑ d ∈ Icc 1 (Nat.floor (2 * S)), (d : ℝ) *
        (32 * (divisorMaximum S H F : ℝ) * (nu.divisors.card : ℝ) *
          (H * S) ^ 2 / (d : ℝ) ^ 2 * (d.gcd nu : ℝ)) := by
      apply hred.trans
      apply sum_le_sum
      intro d hd
      have hdpos : 0 < d := by have := (mem_Icc.mp hd).1; omega
      exact mul_le_mul_of_nonneg_left
        (bounded_first_moment_gcd_le S H F hS hH hF nu hnu d hdpos
          (Ioc 0 (Nat.floor (2 * S / d))) (by intro n hn; exact hn)) (Nat.cast_nonneg _)
    _ = 32 * (divisorMaximum S H F : ℝ) * (nu.divisors.card : ℝ) * (H * S) ^ 2 *
        ∑ d ∈ Icc 1 (Nat.floor (2 * S)), (d.gcd nu : ℝ) / d := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by have := (mem_Icc.mp hd).1; omega : 0 < d)
      field_simp [hdpos.ne']
      ring
    _ ≤ 32 * (divisorMaximum S H F : ℝ) * (nu.divisors.card : ℝ) * (H * S) ^ 2 *
        ((nu.divisors.card : ℝ) * (harmonic (Nat.floor (2 * S)) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_gcd_div_le_divisors_harmonic nu (Nat.floor (2 * S)) hnu) (by positivity)
    _ = _ := by ring

private theorem row_second_moment_gcd_le (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F) (nu : ℕ) (hnu : 0 < nu) :
    (∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
      ∑ k ∈ frequencyCarrier (4 * H * S),
        ((row H s k).card : ℝ) ^ 2 * (nu.gcd k.natAbs : ℝ)) ≤
      32 * (divisorMaximum S H F : ℝ) * (nu.divisors.card : ℝ) * (H * S) ^ 2 +
        (2 * H / S) * (32 * (divisorMaximum S H F : ℝ) *
          (nu.divisors.card : ℝ) ^ 2 * (H * S) ^ 2 *
            (harmonic (Nat.floor (2 * S)) : ℝ)) := by
  have hH0 : 0 ≤ H := by linarith
  have hSpos : 0 < S := by linarith
  calc
    _ ≤ ∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
        ∑ k ∈ frequencyCarrier (4 * H * S),
          (((row H s k).card : ℝ) + (2 * H / S) * (s.1.gcd s.2 : ℝ) *
            ((row H s k).card : ℝ)) * (nu.gcd k.natAbs : ℝ) := by
      apply sum_le_sum
      intro s hs
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right
        (row_square_le S H hS hH0 (mem_product.mp hs).1 (mem_product.mp hs).2 k)
        (Nat.cast_nonneg _)
    _ = (∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
          ∑ k ∈ frequencyCarrier (4 * H * S),
            ((row H s k).card : ℝ) * (nu.gcd k.natAbs : ℝ)) +
        (2 * H / S) * ∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
          ∑ k ∈ frequencyCarrier (4 * H * S),
            (s.1.gcd s.2 : ℝ) * ((row H s k).card : ℝ) * (nu.gcd k.natAbs : ℝ) := by
      simp only [add_mul, sum_add_distrib, mul_sum, mul_assoc]
    _ ≤ _ := add_le_add (first_moment_gcd_le S H F hS hH hF nu hnu)
      (mul_le_mul_of_nonneg_left (gcd_weighted_first_moment_le S H F hS hH hF nu hnu)
        (by positivity))

private theorem multiplicityL2_le_second_moment (S H F : ℝ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F) (nu : ℕ) (hnu : 0 < nu) :
    multiplicityL2 S H F nu ≤ (divisorMaximum S H F : ℝ) ^ 2 * (2 * F / nu) *
      ∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
        ∑ k ∈ frequencyCarrier (4 * H * S),
          ((row H s k).card : ℝ) ^ 2 * (nu.gcd k.natAbs : ℝ) := by
  have hF0 : 0 ≤ F := by linarith
  have hfirst := multiplicityL2_le_source_rows S H F hS hH hF nu
  rw [source_rows_eq_moment S H F hS hH nu] at hfirst
  have hmoment :
      (∑ s₁ ∈ dyadicCarrier S, ∑ s₂ ∈ dyadicCarrier S,
        ∑ k ∈ frequencyCarrier (4 * H * S), ((row H (s₁, s₂) k).card : ℝ) ^ 2 *
          (((dyadicCarrier F).filter (fun f => (nu : ℤ) ∣ (f : ℤ) * k)).card : ℝ)) ≤
      (2 * F / nu) * ∑ s ∈ dyadicCarrier S ×ˢ dyadicCarrier S,
        ∑ k ∈ frequencyCarrier (4 * H * S),
          ((row H s k).card : ℝ) ^ 2 * (nu.gcd k.natAbs : ℝ) := by
    simp only [sum_product, mul_sum]
    apply sum_le_sum
    intro s₁ _
    apply sum_le_sum
    intro s₂ _
    apply sum_le_sum
    intro k _
    have h := mul_le_mul_of_nonneg_left (card_f_product_divisible_le F hF0 nu hnu k)
      (sq_nonneg ((row H (s₁, s₂) k).card : ℝ))
    convert h using 1 <;> ring
  exact (hfirst.trans (mul_le_mul_of_nonneg_left hmoment (sq_nonneg _))).trans_eq (by ring)

private theorem harmonic_floor_twice_ge_one (S : ℝ) (hS : 1 ≤ S) :
    1 ≤ (harmonic (Nat.floor (2 * S)) : ℝ) := by
  have hM : 1 ≤ Nat.floor (2 * S) := Nat.le_floor (by linarith : (1 : ℝ) ≤ 2 * S)
  have h := single_le_sum (s := Icc 1 (Nat.floor (2 * S)))
    (f := fun n : ℕ => 1 / (n : ℝ)) (fun _ _ => by positivity)
    (mem_Icc.mpr ⟨le_rfl, hM⟩ : 1 ∈ Icc 1 (Nat.floor (2 * S)))
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    one_div, Nat.cast_one, inv_one] using h

private theorem scalar_budget {D t J x T : ℝ}
    (hD : 1 ≤ D) (ht : 0 ≤ t) (htD : t ≤ D) (hJ : 1 ≤ J)
    (hx : 0 ≤ x) (hT : 0 ≤ T) :
    (64 * D ^ 3 * t + 128 * D ^ 3 * t ^ 2 * J * x) * T ≤
      576 * D ^ 5 * J * (1 + x) * T := by
  have hD0 : 0 ≤ D := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hA : D ^ 3 * t ≤ D ^ 5 * J := by
    calc
      _ ≤ D ^ 3 * D := mul_le_mul_of_nonneg_left htD (by positivity)
      _ = D ^ 4 := by ring
      _ ≤ D ^ 4 * D := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hD (show 0 ≤ D ^ 4 by positivity)
      _ = D ^ 5 := by ring
      _ ≤ D ^ 5 * J := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hJ (show 0 ≤ D ^ 5 by positivity)
  have hB : D ^ 3 * t ^ 2 ≤ D ^ 5 := by
    calc
      _ ≤ D ^ 3 * D ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htD 2) (by positivity)
      _ = _ := by ring
  have hP : 0 ≤ D ^ 5 * J := by positivity
  have hcoefficient : 64 * D ^ 3 * t + 128 * D ^ 3 * t ^ 2 * J * x ≤
      576 * D ^ 5 * J * (1 + x) := by
    calc
      _ ≤ 64 * (D ^ 5 * J) + 128 * ((D ^ 5 * J) * x) := by
        apply add_le_add
        · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 64)
        · have h := mul_le_mul_of_nonneg_right hB (mul_nonneg hJ0 hx)
          have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 128)
          simpa only [mul_assoc] using h'
      _ ≤ 576 * (D ^ 5 * J) + 576 * ((D ^ 5 * J) * x) :=
        add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (64 : ℝ) ≤ 576) hP)
          (mul_le_mul_of_nonneg_right (by norm_num : (128 : ℝ) ≤ 576) (mul_nonneg hP hx))
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right hcoefficient hT

/-- The full positive-f signed-difference multiplicity has its explicit
divisor and harmonic bound at every positive auxiliary modulus. The same
literal nonzero support gives an exact zero above its true upper endpoint. -/
theorem signedDifference_multiplicityL2_bound
    (S H F : ℝ) (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F)
    (nu : ℕ) (hnu : 0 < nu) :
    multiplicityL2 S H F nu ≤
      576 * (divisorMaximum S H F : ℝ) ^ 5 *
        (harmonic (Nat.floor (2 * S)) : ℝ) *
          (1 + H / S) * (H * S) ^ 2 * F / (nu : ℝ) ∧
      (8 * F * H * S ≤ (nu : ℝ) → multiplicityL2 S H F nu = 0) := by
  let D : ℝ := divisorMaximum S H F
  let t : ℝ := nu.divisors.card
  let J : ℝ := harmonic (Nat.floor (2 * S))
  let x : ℝ := H / S
  let T : ℝ := (H * S) ^ 2 * F / nu
  have hSpos : 0 < S := by linarith
  have hHpos : 0 < H := by linarith
  have hFpos : 0 < F := by linarith
  have hnuR : (0 : ℝ) < nu := by exact_mod_cast hnu
  have hD : 1 ≤ D := by exact_mod_cast divisorMaximum_pos S H F hS
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hJ : 1 ≤ J := harmonic_floor_twice_ge_one S hS
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  constructor
  · by_cases hlarge : 8 * F * H * S ≤ (nu : ℝ)
    · rw [zero_above_support S H F hS hH hF nu hnu hlarge]
      have hJ0 : 0 ≤ (harmonic (Nat.floor (2 * S)) : ℝ) := by change 0 ≤ J; linarith
      positivity
    · have hsmall : (nu : ℝ) < 8 * F * H * S := lt_of_not_ge hlarge
      have htD : t ≤ D := by
        exact_mod_cast tau_le_divisorMaximum hnu
          (hsmall.le.trans (le_max_right (4 * S ^ 2) (8 * F * H * S)))
      have hraw := multiplicityL2_le_second_moment S H F hS hH hF nu hnu
      have hmoment := row_second_moment_gcd_le S H F hS hH hF nu hnu
      have hpaid := hraw.trans (mul_le_mul_of_nonneg_left hmoment
        (show 0 ≤ (divisorMaximum S H F : ℝ) ^ 2 * (2 * F / nu) by positivity))
      have hraw' : multiplicityL2 S H F nu ≤
          (64 * D ^ 3 * t + 128 * D ^ 3 * t ^ 2 * J * x) * T := by
        convert hpaid using 1
        dsimp [D, t, J, x, T]
        simp only [div_eq_mul_inv]
        ring
      have hfinal := hraw'.trans (scalar_budget hD ht htD hJ hx hT)
      convert hfinal using 1
      dsimp [D, J, x, T]
      simp only [div_eq_mul_inv]
      ring
  · exact zero_above_support S H F hS hH hF nu hnu

end

end ImbalancedChen.Part3.LichtmanSignedDifferenceMultiplicity
