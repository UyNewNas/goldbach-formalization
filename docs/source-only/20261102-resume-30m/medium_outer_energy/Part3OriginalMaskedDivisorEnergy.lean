import ImbalancedChen.Part3OriginalMaskedOuterEnergy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original outer image is pushed to (b,c,f) with a PROVED divisor
multiplicity. All enlargement statements concern positive squared
prefix norms after the original Cauchy step. No comparison between a
masked oscillatory sum and its unrestricted final sum is asserted.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalMask20261102
open ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
open ImbalancedChen.Part3.OriginalReciprocalProductAbel20261102
open ImbalancedChen.Part3.OriginalReciprocalAbelCaller20261102
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalMaskedDivisorEnergy20261102

attribute [local instance] Classical.propDecidable

abbrev PacketIndex := ℕ × ℕ × ℤ
def packetIndex (o : Outer) : PacketIndex := (packetB o, packetC o, o.f)

def packetRepresentative (v : PacketIndex) : Outer :=
  ⟨0, v.2.1, v.1, 1, 1, 1, v.2.2⟩

def packetEnvelope (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4)
    (v : PacketIndex) : ℝ :=
  rowEnvelope B atom z k small R st st' e (packetRepresentative v)

/-- K removed the product endpoints, so the envelope now depends on
the outer tuple only through b,c and its original SIGNED f. -/
theorem rowEnvelope_eq_packetEnvelope (B : FixedBlock) (atom : MediumAtom)
    (z : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) :
    rowEnvelope B atom z k small R st st' e o =
      packetEnvelope B atom z k small R st st' e (packetIndex o) := by
  simp only [packetEnvelope, rowEnvelope, shiftedBare, bareSAtom,
    packetRepresentative, packetIndex, packetB, packetC, mul_one]

theorem nCarrier_bounds (B : FixedBlock) {n : ℕ} (hn : n ∈ B.nCarrier) :
    0 < n ∧ (n : ℝ) ≤ 2 * B.atom.U := by
  obtain ⟨hl, hu⟩ := mem_Icc.mp (mem_filter.mp hn).1
  have hl' : B.atom.U ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hl)
  have hu' : (n : ℝ) ≤ 2 * B.atom.U :=
    (show (n : ℝ) ≤ Nat.floor (2 * B.atom.U) by exact_mod_cast hu).trans
      (Nat.floor_le (mul_nonneg (by norm_num) B.U_pos.le))
  exact ⟨by exact_mod_cast B.U_pos.trans_le hl', hu'⟩

theorem nCarrier_lower (B : FixedBlock) {n : ℕ} (hn : n ∈ B.nCarrier) :
    B.atom.U ≤ (n : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1)

theorem originalOuter_positive (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    {o : Outer} (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') :
    0 < o.n1 ∧ 0 < o.n2 ∧ 0 < o.r1 ∧ 0 < o.s2 ∧ 0 < o.r2 := by
  obtain ⟨_, _, hr1, hs2, hr2, _, _, hn1, hn2, _⟩ :=
    originalOuter_gate B atom z y k small R Br Bs st st' ho
  have hR : 0 < (2 : ℕ) ^ k.v := pow_pos (by norm_num) _
  have hS : 0 < (2 : ℕ) ^ k.u := pow_pos (by norm_num) _
  exact ⟨(nCarrier_bounds B hn1).1, (nCarrier_bounds B hn2).1,
    hR.trans_le (commonR_window atom z k small st hr1).1,
    hS.trans_le (commonS_window atom z k small st' hs2).1,
    hR.trans_le (commonR_window atom z k small st' hr2).1⟩

def packetFibre (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (v : PacketIndex) : Finset Outer :=
  (originalOuter B atom z y k small R Br Bs st st').filter (fun o => packetIndex o = v)

def representation (o : Outer) : ℕ × ℕ × ℕ := (o.r1, o.r2, o.s2)
def representationCarrier (v : PacketIndex) : Finset (ℕ × ℕ × ℕ) :=
  v.1.divisors ×ˢ (v.2.1.divisors ×ˢ v.2.1.divisors)

theorem representation_mem (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (v : PacketIndex) {o : Outer}
    (ho : o ∈ packetFibre B atom z y k small R Br Bs st st' v) :
    representation o ∈ representationCarrier v := by
  obtain ⟨ho, hv⟩ := mem_filter.mp ho
  obtain ⟨hn1, hn2, hr1, hs2, hr2⟩ :=
    originalOuter_positive B atom z y k small R Br Bs st st' ho
  rw [← hv]
  unfold representation representationCarrier packetIndex packetB packetC
  apply mem_product.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, (Nat.mul_pos hn2 hr1).ne'⟩,
    mem_product.mpr ⟨?_, ?_⟩⟩
  · exact Nat.mem_divisors.mpr ⟨⟨o.n1 * o.s2, by ring⟩,
      (Nat.mul_pos (Nat.mul_pos hn1 hr2) hs2).ne'⟩
  · exact Nat.mem_divisors.mpr ⟨dvd_mul_left _ _,
      (Nat.mul_pos (Nat.mul_pos hn1 hr2) hs2).ne'⟩

/-- The ordered r2,s2 factors remain ordered. Given them and b,c,f,
recover n2,n1 and then q using f!=0 and d>0. -/
theorem representation_injOn (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (hx : 1 < B.x) (v : PacketIndex) :
    Set.InjOn representation (packetFibre B atom z y k small R Br Bs st st' v) := by
  intro o ho o' ho' he
  obtain ⟨ho, hv⟩ := mem_filter.mp ho
  obtain ⟨ho', hv'⟩ := mem_filter.mp ho'
  have hr1 : o.r1 = o'.r1 := congrArg (fun t : ℕ × ℕ × ℕ => t.1) he
  have hr2 : o.r2 = o'.r2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) he
  have hs2 : o.s2 = o'.s2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he
  have hk := hv.trans hv'.symm
  have hb : packetB o = packetB o' := congrArg (fun t : PacketIndex => t.1) hk
  have hc : packetC o = packetC o' := congrArg (fun t : PacketIndex => t.2.1) hk
  have hf : o.f = o'.f := congrArg (fun t : PacketIndex => t.2.2) hk
  obtain ⟨_, _, hr1p, hs2p, hr2p⟩ :=
    originalOuter_positive B atom z y k small R Br Bs st st' ho'
  have hn2 : o.n2 = o'.n2 := by
    unfold packetB at hb
    rw [hr1] at hb
    exact mul_right_cancel₀ hr1p.ne' hb
  have hn1 : o.n1 = o'.n1 := by
    unfold packetC at hc
    rw [hr2, hs2] at hc
    exact mul_right_cancel₀ hr2p.ne' (mul_right_cancel₀ hs2p.ne' hc)
  have hE := originalOuter_equation B atom z y k small R Br Bs st st' ho
  have hE' := originalOuter_equation B atom z y k small R Br Bs st st' ho'
  have hf0 := originalOuter_f_ne_zero B atom z y k small R Br Bs st st' hx ho'
  have hprod : ((o.q * B.d : ℕ) : ℤ) * o'.f =
      ((o'.q * B.d : ℕ) : ℤ) * o'.f := by
    calc
      _ = (o.n1 : ℤ) - o.n2 := by rw [← hf]; exact hE
      _ = (o'.n1 : ℤ) - o'.n2 := by rw [hn1, hn2]
      _ = _ := hE'.symm
  have hqd : o.q * B.d = o'.q * B.d := by
    exact_mod_cast mul_right_cancel₀ hf0 hprod
  have hq : o.q = o'.q := mul_right_cancel₀ B.d_pos.ne' hqd
  cases o
  cases o'
  simp_all

theorem packetFibre_card_le (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (hx : 1 < B.x) (v : PacketIndex) :
    (packetFibre B atom z y k small R Br Bs st st' v).card ≤
      v.1.divisors.card * v.2.1.divisors.card ^ 2 := by
  have hc := card_le_card_of_injOn representation
    (fun o ho => representation_mem B atom z y k small R Br Bs st st' v ho)
    (representation_injOn B atom z y k small R Br Bs st st' hx v)
  simpa only [representationCarrier, card_product, pow_two] using hc

/-- Exact grouping, including the true number of original outer points
above every b,c,f. No divisor multiplier is hidden in a claimed identity. -/
theorem prefixEnergy_eq_fibres (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) :
    prefixEnergy B atom z y k small R Br Bs st st' e =
      ∑ v ∈ (originalOuter B atom z y k small R Br Bs st st').image packetIndex,
        ((packetFibre B atom z y k small R Br Bs st st' v).card : ℝ) *
          packetEnvelope B atom z k small R st st' e v ^ 2 := by
  let O := originalOuter B atom z y k small R Br Bs st st'
  have hh := sum_fiberwise_of_maps_to (s := O) (t := O.image packetIndex)
    (g := packetIndex) (fun o ho => mem_image_of_mem _ ho)
    (fun o => rowEnvelope B atom z k small R st st' e o ^ 2)
  change (∑ o ∈ O, rowEnvelope B atom z k small R st st' e o ^ 2) = _
  rw [← hh]
  apply sum_congr rfl
  intro v hv
  calc
    _ = ∑ _o ∈ O.filter (fun o => packetIndex o = v),
        packetEnvelope B atom z k small R st st' e v ^ 2 := by
      apply sum_congr rfl
      intro o ho
      rw [rowEnvelope_eq_packetEnvelope, (mem_filter.mp ho).2]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl

theorem prefixEnergy_le_divisor_image (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) (hx : 1 < B.x) :
    prefixEnergy B atom z y k small R Br Bs st st' e ≤
      ∑ v ∈ (originalOuter B atom z y k small R Br Bs st st').image packetIndex,
        (v.1.divisors.card * v.2.1.divisors.card ^ 2 : ℕ) *
          packetEnvelope B atom z k small R st st' e v ^ 2 := by
  rw [prefixEnergy_eq_fibres]
  apply sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast packetFibre_card_le B atom z y k small R Br Bs st st' hx v)
    (sq_nonneg _)

def packetAmbient (B : FixedBlock) (k : Key) : Finset PacketIndex :=
  ((Icc (Nat.ceil (B.atom.U * scaleR k))
      (Nat.floor (4 * B.atom.U * scaleR k))) ×ˢ
    (Icc (Nat.ceil (B.atom.U * scaleR k * scaleS k))
      (Nat.floor (8 * B.atom.U * scaleR k * scaleS k)) ×ˢ
      signedWindow (2 * B.atom.U / B.atom.Q1))).filter
        (fun v => v.1.Coprime v.2.1)

theorem packetIndex_mem_ambient (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (hx : 1 < B.x) {o : Outer}
    (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') :
    packetIndex o ∈ packetAmbient B k := by
  obtain ⟨_, _, hr1, hs2, hr2, _, _, hn1, hn2, _⟩ :=
    originalOuter_gate B atom z y k small R Br Bs st st' ho
  obtain ⟨hn1p, hn2p, hr1p, hs2p, hr2p⟩ :=
    originalOuter_positive B atom z y k small R Br Bs st st' ho
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  have hU := B.U_pos
  have hQ := B.Q_pos
  have hr1b : (o.r1 : ℝ) ≤ 2 * scaleR k := by
    exact_mod_cast (commonR_window atom z k small st hr1).2.le
  have hr2b : (o.r2 : ℝ) ≤ 2 * scaleR k := by
    exact_mod_cast (commonR_window atom z k small st' hr2).2.le
  have hs2b : (o.s2 : ℝ) ≤ 2 * scaleS k := by
    exact_mod_cast (commonS_window atom z k small st' hs2).2.le
  have hr1lo : scaleR k ≤ (o.r1 : ℝ) := by
    exact_mod_cast (commonR_window atom z k small st hr1).1
  have hr2lo : scaleR k ≤ (o.r2 : ℝ) := by
    exact_mod_cast (commonR_window atom z k small st' hr2).1
  have hs2lo : scaleS k ≤ (o.s2 : ℝ) := by
    exact_mod_cast (commonS_window atom z k small st' hs2).1
  have hblo : B.atom.U * scaleR k ≤ (packetB o : ℝ) := by
    unfold packetB
    push_cast
    exact mul_le_mul (nCarrier_lower B hn2) hr1lo hR.le (Nat.cast_nonneg _)
  have hclo : B.atom.U * scaleR k * scaleS k ≤ (packetC o : ℝ) := by
    unfold packetC
    push_cast
    gcongr
    exact nCarrier_lower B hn1
  have hb : (packetB o : ℝ) ≤ 4 * B.atom.U * scaleR k := by
    unfold packetB
    push_cast
    calc
      _ ≤ (2 * B.atom.U) * (2 * scaleR k) := by
        gcongr
        exact (nCarrier_bounds B hn2).2
      _ = _ := by ring
  have hc : (packetC o : ℝ) ≤ 8 * B.atom.U * scaleR k * scaleS k := by
    unfold packetC
    push_cast
    calc
      _ ≤ (2 * B.atom.U) * (2 * scaleR k) * (2 * scaleS k) := by
        gcongr
        exact (nCarrier_bounds B hn1).2
      _ = _ := by ring
  have hd : (1 : ℝ) ≤ B.d := by exact_mod_cast B.d_pos
  have hden : B.atom.Q1 ≤ B.atom.Q1 * B.d := by nlinarith
  have hfbound := (originalOuter_f_bound B atom z y k small R Br Bs st st' ho).trans
    (div_le_div_of_nonneg_left (by positivity) hQ hden)
  have hf := mem_signedWindow
    (originalOuter_f_ne_zero B atom z y k small R Br Bs st st' hx ho) hfbound
  have hcop : (packetB o).Coprime (packetC o) := by
    obtain ⟨s, hs, rfl⟩ := mem_image.mp ho
    exact (source_packet_inverse_licenses B atom z y k small R Br Bs st st' hs).1
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hblo, Nat.le_floor hb⟩,
    mem_product.mpr ⟨mem_Icc.mpr
      ⟨Nat.ceil_le.mpr hclo, Nat.le_floor hc⟩, hf⟩⟩, hcop⟩

def divisorPrefixEnergy (B : FixedBlock) (atom : MediumAtom) (z : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4) : ℝ :=
  ∑ v ∈ packetAmbient B k,
    (v.1.divisors.card * v.2.1.divisors.card ^ 2 : ℕ) *
      packetEnvelope B atom z k small R st st' e v ^ 2

/-- ONLY a positive sum is enlarged, after outer energy has retained
its 1/d. The enlarged f-window has both signs and radius 2U/Q. -/
theorem prefixEnergy_le_divisorPrefixEnergy (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) (hx : 1 < B.x) :
    prefixEnergy B atom z y k small R Br Bs st st' e ≤
      divisorPrefixEnergy B atom z k small R st st' e := by
  apply (prefixEnergy_le_divisor_image B atom z y k small R Br Bs st st' e hx).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro v hv
    obtain ⟨o, ho, rfl⟩ := mem_image.mp hv
    exact packetIndex_mem_ambient B atom z y k small R Br Bs st st' hx ho
  · intro v hv hnot
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem abelCauchyCharge_le_divisor_energy {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    abelCauchyCharge B atom z y k small R Br Bs st st' e f g ≤
      32 * normalizationP B k / Real.sqrt B.d *
        Real.sqrt (divisorPrefixEnergy B atom z k small R st st' e) := by
  apply (abelCauchyCharge_le_P B atom hA z y k small R Br Bs st st' e f g hx hU hQ).trans
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  apply mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt
      (prefixEnergy_le_divisorPrefixEnergy B atom z y k small R Br Bs st st' e hx))
  unfold normalizationP
  positivity

theorem frozenUpperPacket_norm_le_divisor_energy {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    ‖frozenUpperPacket B atom z y k small R Br Bs st st' e f g‖ ≤
      32 * normalizationP B k / Real.sqrt B.d *
        Real.sqrt (divisorPrefixEnergy B atom z k small R st st' e) :=
  (frozenUpperPacket_norm_le_abelCauchyCharge B atom z y k small R Br Bs st st' e f g).trans
    (abelCauchyCharge_le_divisor_energy B atom hA z y k small R Br Bs st st' e f g hx hU hQ)

/-- The favorable d^(-1/2) may now be dropped because d is an original
positive natural. It was not lost in the first energy count. -/
theorem frozenUpperPacket_norm_le_divisor_energy_drop_d {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    ‖frozenUpperPacket B atom z y k small R Br Bs st st' e f g‖ ≤
      32 * normalizationP B k *
        Real.sqrt (divisorPrefixEnergy B atom z k small R st st' e) := by
  apply (frozenUpperPacket_norm_le_divisor_energy B atom hA z y k small R Br Bs st st' e f g hx hU hQ).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hd : (1 : ℝ) ≤ B.d := by exact_mod_cast B.d_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  have hp : 0 ≤ 32 * normalizationP B k := by unfold normalizationP; positivity
  exact div_le_self hp (Real.one_le_sqrt.mpr hd)

end ImbalancedChen.Part3.OriginalMaskedDivisorEnergy20261102
