import ImbalancedChen.Part3PairedAlphaDeletion

/-!
# A finite large-paired-gcd count with a shared first factor

The modulus p is any positive integer, including a composite integer.
Both primitive gates, the shared congruence, and every diagonal pair
remain in the source set. The actual gcd g is coprime to p before it
is cancelled from that congruence.

The gain is 2T^2/(pY)+T(1+log T). In particular the diagonal is paid
by the second term. This leaf contains no W or Fourier estimate, no
assumption about a moving residue, and no transfer of an old payment.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

def sharedPrimitiveLargeGCDPairs (N : Finset ℕ) (p : ℕ) (Y : ℝ) :
    Finset (ℕ × ℕ) :=
  (N ×ˢ N).filter (fun z ↦ z.1.Coprime p ∧ z.2.Coprime p ∧
    Nat.ModEq p z.1 z.2 ∧ Y < (z.1.gcd z.2 : ℝ))

namespace SharedFirstFactorPairCount

private def congruentPairs (K p : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 K ×ˢ Ioc 0 K).filter (fun z ↦ Nat.ModEq p z.1 z.2)

private def divisibleCongruentPairs (K p g : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 K ×ˢ Ioc 0 K).filter (fun z ↦
    g ∣ z.1 ∧ g ∣ z.2 ∧ Nat.ModEq p z.1 z.2)

/-- Quotient blocks count a progression for every positive composite p too. -/
private theorem card_congruentPairs_le (K p : ℕ) :
    (congruentPairs K p).card ≤ K * (K / p + 1) := by
  calc
    _ ≤ (Ioc 0 K ×ˢ range (K / p + 1)).card := by
      apply card_le_card_of_injOn (fun z : ℕ × ℕ ↦ (z.1, z.2 / p))
      · intro z hz
        obtain ⟨hz0, _⟩ := mem_filter.mp hz
        obtain ⟨hz1, hz2⟩ := mem_product.mp hz0
        exact mem_product.mpr ⟨hz1, mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (mem_Ioc.mp hz2).2))⟩
      · intro z hz w hw he
        obtain ⟨_, hzmod⟩ := mem_filter.mp hz
        obtain ⟨_, hwmod⟩ := mem_filter.mp hw
        have hfirst : z.1 = w.1 := by
          simpa only using congrArg (fun t : ℕ × ℕ ↦ t.1) he
        have hquot : z.2 / p = w.2 / p := by
          simpa only using congrArg (fun t : ℕ × ℕ ↦ t.2) he
        apply Prod.ext hfirst
        apply Nat.ext_div_modEq hquot
        rw [hfirst] at hzmod
        exact hzmod.symm.trans hwmod
    _ = _ := by simp only [card_product, Nat.card_Ioc, Nat.sub_zero, card_range]

/-- Cancellation is made only after the actual g-coprime-p gate. -/
private theorem card_divisibleCongruentPairs_le (K p g : ℕ)
    (hg : 0 < g) (hgp : g.Coprime p) :
    (divisibleCongruentPairs K p g).card ≤ (K / g) * ((K / g) / p + 1) := by
  apply (show (divisibleCongruentPairs K p g).card ≤
      (congruentPairs (K / g) p).card from ?_).trans
    (card_congruentPairs_le (K / g) p)
  apply card_le_card_of_injOn (fun z : ℕ × ℕ ↦ (z.1 / g, z.2 / g))
  · intro z hz
    obtain ⟨hz0, hz1, hz2, hzmod⟩ := mem_filter.mp hz
    obtain ⟨hzlo, hzhi⟩ := mem_product.mp hz0
    have hu : 0 < z.1 / g := Nat.div_pos
      (Nat.le_of_dvd (mem_Ioc.mp hzlo).1 hz1) hg
    have hv : 0 < z.2 / g := Nat.div_pos
      (Nat.le_of_dvd (mem_Ioc.mp hzhi).1 hz2) hg
    refine mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Ioc.mpr ⟨hu, Nat.div_le_div_right (mem_Ioc.mp hzlo).2⟩,
        mem_Ioc.mpr ⟨hv, Nat.div_le_div_right (mem_Ioc.mp hzhi).2⟩⟩, ?_⟩
    apply Nat.ModEq.cancel_right_of_coprime hgp.symm
    simpa only [Nat.div_mul_cancel hz1, Nat.div_mul_cancel hz2] using hzmod
  · intro z hz w hw he
    obtain ⟨_, hz1, hz2, _⟩ := mem_filter.mp hz
    obtain ⟨_, hw1, hw2, _⟩ := mem_filter.mp hw
    apply Prod.ext
    · calc
        z.1 = (z.1 / g) * g := (Nat.div_mul_cancel hz1).symm
        _ = (w.1 / g) * g := congrArg (fun n : ℕ ↦ n * g) (congrArg Prod.fst he)
        _ = w.1 := Nat.div_mul_cancel hw1
    · calc
        z.2 = (z.2 / g) * g := (Nat.div_mul_cancel hz2).symm
        _ = (w.2 / g) * g := congrArg (fun n : ℕ ↦ n * g) (congrArg Prod.snd he)
        _ = w.2 := Nat.div_mul_cancel hw2

/-- The second inverse moment uses a literal finite telescope. -/
private theorem sum_inv_sq_Icc_le (M K : ℕ) (hM : 0 < M) :
    (∑ g ∈ Icc M K, ((g : ℝ)⁻¹) ^ 2) ≤ 2 / M := by
  by_cases hMK : M ≤ K
  · calc
      _ ≤ ∑ g ∈ Icc M K, 2 * ((g : ℝ)⁻¹ - ((g : ℝ) + 1)⁻¹) := by
        apply sum_le_sum
        intro g hg
        have hg0 : (0 : ℝ) < g := by exact_mod_cast hM.trans_le (mem_Icc.mp hg).1
        have hg1 : (0 : ℝ) < (g : ℝ) + 1 := by linarith
        calc
          _ = 1 / (g : ℝ) ^ 2 := by simp only [one_div, inv_pow]
          _ ≤ 2 / ((g : ℝ) * ((g : ℝ) + 1)) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hg0) (mul_pos hg0 hg1)).mpr
            have hgOne : (1 : ℝ) ≤ g := by
              exact_mod_cast (Nat.succ_le_iff.mpr hM).trans (mem_Icc.mp hg).1
            nlinarith
          _ = _ := by field_simp; ring
      _ = 2 * ((M : ℝ)⁻¹ - ((K : ℝ) + 1)⁻¹) := by
        rw [← mul_sum]
        congr 1
        have ht := sum_Icc_sub hMK (fun g : ℕ ↦ (g : ℝ)⁻¹)
        simp only [Nat.cast_add, Nat.cast_one] at ht
        have hneg : (∑ g ∈ Icc M K, (((g : ℝ) + 1)⁻¹ - (g : ℝ)⁻¹)) =
            -(∑ g ∈ Icc M K, ((g : ℝ)⁻¹ - ((g : ℝ) + 1)⁻¹)) := by
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro g _
          ring
        linarith
      _ ≤ _ := by
        have hK : 0 ≤ ((K : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left (sub_le_self ((M : ℝ)⁻¹) hK) (by norm_num : (0 : ℝ) ≤ 2)
  · have hempty : Icc M K = ∅ := Icc_eq_empty_of_lt (Nat.lt_of_not_ge hMK)
    simp only [hempty, sum_empty]
    positivity

private theorem sum_inv_sq_large_le (T Y : ℝ) (hY : 1 ≤ Y)
    (G : Finset ℕ) (hG : ∀ g ∈ G, g ≤ Nat.floor T ∧ Y < (g : ℝ)) :
    (∑ g ∈ G, ((g : ℝ)⁻¹) ^ 2) ≤ 2 / Y := by
  have hY0 : 0 ≤ Y := by linarith
  have hsub : G ⊆ Icc (Nat.floor Y + 1) (Nat.floor T) := by
    intro g hg
    obtain ⟨hgT, hgY⟩ := hG g hg
    have hlo : Nat.floor Y < g := by
      by_contra hn
      have hgle : g ≤ Nat.floor Y := Nat.le_of_not_gt hn
      have hgleR : (g : ℝ) ≤ Y := (Nat.cast_le.mpr hgle).trans (Nat.floor_le hY0)
      linarith
    exact mem_Icc.mpr ⟨by omega, hgT⟩
  calc
    _ ≤ ∑ g ∈ Icc (Nat.floor Y + 1) (Nat.floor T), ((g : ℝ)⁻¹) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ sq_nonneg _)
    _ ≤ 2 / (Nat.floor Y + 1 : ℕ) := sum_inv_sq_Icc_le _ _ (Nat.succ_pos _)
    _ ≤ _ := by
      have hfloor : Y < (Nat.floor Y + 1 : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one Y
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hfloor.le

private theorem sum_inv_le_log {T : ℝ} (hT : 1 ≤ T)
    (G : Finset ℕ) (hG : G ⊆ Ioc 0 (Nat.floor T)) :
    (∑ g ∈ G, (g : ℝ)⁻¹) ≤ 1 + Real.log T := by
  have hI : Ioc 0 (Nat.floor T) = Icc 1 (Nat.floor T) := by
    ext g
    simp only [mem_Ioc, mem_Icc]
    omega
  calc
    _ ≤ ∑ g ∈ Ioc 0 (Nat.floor T), (g : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hG (fun _ _ _ ↦ by positivity)
    _ = (harmonic (Nat.floor T) : ℝ) := by
      rw [hI]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_floor_le_one_add_log T hT

/-- Every source pair has its actual gcd in the coprime divisor union. -/
private theorem card_le_sum_divisible (T Y : ℝ) (N : Finset ℕ) (p : ℕ)
    (hN : N ⊆ Ioc 0 (Nat.floor T)) :
    (sharedPrimitiveLargeGCDPairs N p Y).card ≤
      ∑ g ∈ (Ioc 0 (Nat.floor T)).filter (fun g : ℕ ↦ Y < (g : ℝ) ∧ g.Coprime p),
        (divisibleCongruentPairs (Nat.floor T) p g).card := by
  let G := (Ioc 0 (Nat.floor T)).filter (fun g : ℕ ↦ Y < (g : ℝ) ∧ g.Coprime p)
  let S := sharedPrimitiveLargeGCDPairs N p Y
  have hsub : S ⊆ Ioc 0 (Nat.floor T) ×ˢ Ioc 0 (Nat.floor T) := by
    intro z hz
    obtain ⟨hz, _⟩ := mem_filter.mp hz
    exact mem_product.mpr ⟨hN (mem_product.mp hz).1, hN (mem_product.mp hz).2⟩
  calc
    _ = ∑ _z ∈ S, (1 : ℕ) := by simp [S]
    _ ≤ ∑ z ∈ S, ∑ g ∈ G,
        if g ∣ z.1 ∧ g ∣ z.2 ∧ Nat.ModEq p z.1 z.2 then 1 else 0 := by
      apply sum_le_sum
      intro z hz
      obtain ⟨hzN, hz1p, _hz2p, hzmod, hzY⟩ := mem_filter.mp hz
      have hz1 := hN (mem_product.mp hzN).1
      have hgpos : 0 < z.1.gcd z.2 := Nat.gcd_pos_of_pos_left z.2 (mem_Ioc.mp hz1).1
      have hgK : z.1.gcd z.2 ≤ Nat.floor T :=
        (Nat.le_of_dvd (mem_Ioc.mp hz1).1 (Nat.gcd_dvd_left _ _)).trans (mem_Ioc.mp hz1).2
      have hgp : (z.1.gcd z.2).Coprime p := hz1p.of_dvd_left (Nat.gcd_dvd_left _ _)
      have hgG : z.1.gcd z.2 ∈ G := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hgpos, hgK⟩, hzY, hgp⟩
      have hs := single_le_sum (s := G)
        (f := fun g ↦ if g ∣ z.1 ∧ g ∣ z.2 ∧ Nat.ModEq p z.1 z.2 then (1 : ℕ) else 0)
        (fun _ _ ↦ Nat.zero_le _) hgG
      have hdiv : z.1.gcd z.2 ∣ z.1 ∧ z.1.gcd z.2 ∣ z.2 ∧ Nat.ModEq p z.1 z.2 :=
        ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _, hzmod⟩
      simpa only [if_pos hdiv] using hs
    _ ≤ ∑ z ∈ Ioc 0 (Nat.floor T) ×ˢ Ioc 0 (Nat.floor T), ∑ g ∈ G,
        if g ∣ z.1 ∧ g ∣ z.2 ∧ Nat.ModEq p z.1 z.2 then 1 else 0 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro g _
      rw [← sum_filter]
      simp only [divisibleCongruentPairs, sum_const, nsmul_eq_mul, mul_one]
      rfl

end SharedFirstFactorPairCount

/-- All ordered pairs and all positive composite moduli; the diagonal stays. -/
theorem card_sharedPrimitiveLargeGCDPairs_le
    {T Y : ℝ} (hT : 1 ≤ T) (hY : 1 ≤ Y) {p : ℕ} (hp : 0 < p)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 (Nat.floor T)) :
    ((sharedPrimitiveLargeGCDPairs N p Y).card : ℝ) ≤
      2 * T ^ 2 / ((p : ℝ) * Y) + T * (1 + Real.log T) := by
  let G := (Ioc 0 (Nat.floor T)).filter (fun g : ℕ ↦ Y < (g : ℝ) ∧ g.Coprime p)
  have hT0 : 0 ≤ T := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcount : ((sharedPrimitiveLargeGCDPairs N p Y).card : ℝ) ≤
      ∑ g ∈ G, ((SharedFirstFactorPairCount.divisibleCongruentPairs (Nat.floor T) p g).card : ℝ) := by
    exact_mod_cast SharedFirstFactorPairCount.card_le_sum_divisible T Y N p hN
  have hpoint : ∀ g ∈ G,
      ((SharedFirstFactorPairCount.divisibleCongruentPairs (Nat.floor T) p g).card : ℝ) ≤
        (T ^ 2 / p) * ((g : ℝ)⁻¹) ^ 2 + T * (g : ℝ)⁻¹ := by
    intro g hg
    obtain ⟨hgI, _hgY, hgp⟩ := mem_filter.mp hg
    have hgpos : 0 < g := (mem_Ioc.mp hgI).1
    have hkg : ((Nat.floor T / g : ℕ) : ℝ) ≤ T / g :=
      (show ((Nat.floor T / g : ℕ) : ℝ) ≤ (Nat.floor T : ℝ) / g from Nat.cast_div_le).trans
        (div_le_div_of_nonneg_right (Nat.floor_le hT0) (Nat.cast_nonneg g))
    have hkgp : (((Nat.floor T / g) / p : ℕ) : ℝ) ≤ (T / g) / p :=
      (show (((Nat.floor T / g) / p : ℕ) : ℝ) ≤ ((Nat.floor T / g : ℕ) : ℝ) / p from
        Nat.cast_div_le).trans (div_le_div_of_nonneg_right hkg hpR.le)
    calc
      _ ≤ (((Nat.floor T / g) * ((Nat.floor T / g) / p + 1) : ℕ) : ℝ) := by
        exact_mod_cast SharedFirstFactorPairCount.card_divisibleCongruentPairs_le
          (Nat.floor T) p g hgpos hgp
      _ ≤ (T / g) * ((T / g) / p + 1) := by
        push_cast
        exact mul_le_mul hkg (add_le_add hkgp le_rfl) (by positivity) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv]; ring
  calc
    _ ≤ ∑ g ∈ G, ((SharedFirstFactorPairCount.divisibleCongruentPairs (Nat.floor T) p g).card : ℝ) := hcount
    _ ≤ ∑ g ∈ G, ((T ^ 2 / p) * ((g : ℝ)⁻¹) ^ 2 + T * (g : ℝ)⁻¹) := sum_le_sum hpoint
    _ = (T ^ 2 / p) * (∑ g ∈ G, ((g : ℝ)⁻¹) ^ 2) +
        T * (∑ g ∈ G, (g : ℝ)⁻¹) := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ (T ^ 2 / p) * (2 / Y) + T * (1 + Real.log T) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg T) hpR.le)
        exact SharedFirstFactorPairCount.sum_inv_sq_large_le T Y hY G
          (fun g hg ↦ ⟨(mem_Ioc.mp (mem_filter.mp hg).1).2, (mem_filter.mp hg).2.1⟩)
      · apply mul_le_mul_of_nonneg_left _ hT0
        exact SharedFirstFactorPairCount.sum_inv_le_log hT G (filter_subset _ _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Actual paired-alpha carrier at original U, without changing its interval. -/
theorem MediumAtom.card_sharedPrimitiveLargeGCDPairs_le
    {d : MediumAtom} (hU : 1 ≤ d.U) {Y : ℝ} (hY : 1 ≤ Y)
    {p : ℕ} (hp : 0 < p) :
    ((sharedPrimitiveLargeGCDPairs d.transposedAtom.betaCarrier p Y).card : ℝ) ≤
      8 * d.U ^ 2 / ((p : ℝ) * Y) + 2 * d.U * (1 + Real.log (2 * d.U)) := by
  have hsub : d.transposedAtom.betaCarrier ⊆ Ioc 0 (Nat.floor (2 * d.U)) := by
    intro n hn
    change n ∈ factorCarrier d.U at hn
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
    have hceil : 1 ≤ Nat.ceil d.U := by exact_mod_cast hU.trans (Nat.le_ceil d.U)
    exact mem_Ioc.mpr ⟨by omega, hnhi⟩
  have h := ImbalancedChen.Part3.card_sharedPrimitiveLargeGCDPairs_le
    (T := 2 * d.U) (by linarith) hY hp d.transposedAtom.betaCarrier hsub
  calc
    _ ≤ 2 * (2 * d.U) ^ 2 / ((p : ℝ) * Y) +
        (2 * d.U) * (1 + Real.log (2 * d.U)) := h
    _ = _ := by ring

end

end ImbalancedChen.Part3
