import ImbalancedChen.Part3OriginalMaskedDivisorEnergy
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Fixed-order divisor cost and the actual 64-label, two-smooth-label,
four-product-branch caller. No prefix or spectral estimate is a premise.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
open ImbalancedChen.Part3.OriginalReciprocalAbelCaller20261102
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalMaskedDivisorEnergy20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace ImbalancedChen.Part3.OriginalMaskedOuterCaller20261102

attribute [local instance] Classical.propDecidable

def packetCap (B : FixedBlock) (k : Key) : ℝ :=
  8 * B.atom.U * scaleR k * scaleS k

def unweightedPacketEnergy (B : FixedBlock) (atom : MediumAtom) (z : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4) : ℝ :=
  ∑ v ∈ packetAmbient B k, packetEnvelope B atom z k small R st st' e v ^ 2

private theorem factor_left_le {Q : ℝ} (hQ : 0 < Q) {r t : ℕ}
    (h : r * t ∈ factorCarrier Q) : (r : ℝ) ≤ 2 * Q := by
  obtain ⟨hl, hu⟩ := mem_Icc.mp h
  have hp : 0 < r * t := (Nat.ceil_pos.mpr hQ).trans_le hl
  have ht : 1 ≤ t := by
    by_contra ht
    have hz : t = 0 := by omega
    simp only [hz, mul_zero, lt_self_iff_false] at hp
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have huR : (r : ℝ) * t ≤ 2 * Q := by
    have hh : ((r * t : ℕ) : ℝ) ≤ Nat.floor (2 * Q) := by exact_mod_cast hu
    have hh' := hh.trans (Nat.floor_le (by positivity : 0 ≤ 2 * Q))
    simpa only [Nat.cast_mul] using hh'
  nlinarith

/-- Occupied ORIGINAL source keys force their rough dyadic lengths below
the physical Q3 and Q2 scales. No key-comparability premise is inserted. -/
theorem packetCap_le_scale_of_nonempty {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hAtom : B.atom = atom)
    (hA : MediumAdmissible b σ κ c0 atom) (hσ : 0 ≤ σ)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (hx : 1 < atom.scale)
    (hne : (originalOuter B atom z y k small R Br Bs st st').Nonempty) :
    packetCap B k ≤ 32 * atom.scale := by
  obtain ⟨o, ho⟩ := hne
  obtain ⟨_, _, hr1, hs2, _⟩ :=
    originalOuter_gate B atom z y k small R Br Bs st st' ho
  rcases hA with ⟨hU, hV, hQ1, hQ2, hQ3, hscale, haLo, haHi, hrange, hgeom, hrest⟩
  have hR : scaleR k ≤ 2 * atom.Q3 := by
    have hlo : scaleR k ≤ (o.r1 : ℝ) := by
      exact_mod_cast (commonR_window atom z k small st hr1).1
    exact hlo.trans (factor_left_le (by linarith : 0 < atom.Q3) (mem_filter.mp hr1).2)
  have hS : scaleS k ≤ 2 * atom.Q2 := by
    have hlo : scaleS k ≤ (o.s2 : ℝ) := by
      exact_mod_cast (commonS_window atom z k small st' hs2).1
    exact hlo.trans (factor_left_le (by linarith : 0 < atom.Q2) (mem_filter.mp hs2).2)
  have hR0 := scaleR_pos k
  have hS0 := scaleS_pos k
  have hpower : atom.scale ^ (1 - 8 * σ) ≤ atom.scale := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : 1 - 8 * σ ≤ (1 : ℝ))
  have hUR : 1 ≤ atom.U * atom.Q3 := one_le_mul hU hQ3
  have hURsq : atom.U * atom.Q3 ≤ (atom.U * atom.Q3) ^ 2 := by nlinarith
  have hphysical : atom.U * atom.Q2 * atom.Q3 ≤ atom.scale := by
    calc
      _ = (atom.U * atom.Q3) * atom.Q2 := by ring
      _ ≤ (atom.U * atom.Q3) ^ 2 * atom.Q2 :=
        mul_le_mul_of_nonneg_right hURsq (by linarith)
      _ = atom.U ^ 2 * atom.Q2 * atom.Q3 ^ 2 := by ring
      _ ≤ atom.scale := hgeom.le.trans hpower
  calc
    packetCap B k = 8 * atom.U * scaleR k * scaleS k := by rw [packetCap, hAtom]
    _ ≤ 8 * atom.U * (2 * atom.Q3) * (2 * atom.Q2) := by gcongr
    _ = 32 * (atom.U * atom.Q2 * atom.Q3) := by ring
    _ ≤ 32 * atom.scale := mul_le_mul_of_nonneg_left hphysical (by norm_num)

theorem frozenUpperPacket_eq_zero_of_outer_empty (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (he : originalOuter B atom z y k small R Br Bs st st' = ∅) :
    frozenUpperPacket B atom z y k small R Br Bs st st' e f g = 0 := by
  rw [frozenUpperPacket_eq_rows, he, sum_empty]

theorem packetAmbient_positive_bounds (B : FixedBlock) (k : Key)
    {v : PacketIndex} (hv : v ∈ packetAmbient B k) :
    0 < v.1 ∧ 0 < v.2.1 ∧ (v.1 : ℝ) ≤ packetCap B k ∧
      (v.2.1 : ℝ) ≤ packetCap B k := by
  have hU := B.U_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  have hS1 : 1 ≤ scaleS k := by
    unfold scaleS
    exact_mod_cast (Nat.one_le_pow k.u 2 (by norm_num))
  obtain ⟨hb, hc, hf⟩ := mem_product.mp (mem_filter.mp hv).1
  obtain ⟨hbl, hbu⟩ := mem_Icc.mp hb
  obtain ⟨hcl, hcu⟩ := mem_Icc.mp hc
  have hbp : 0 < v.1 := (Nat.ceil_pos.mpr (mul_pos hU hR)).trans_le hbl
  have hcp : 0 < v.2.1 := (Nat.ceil_pos.mpr (mul_pos (mul_pos hU hR) hS)).trans_le hcl
  have hbr : (v.1 : ℝ) ≤ 4 * B.atom.U * scaleR k :=
    (show (v.1 : ℝ) ≤ Nat.floor (4 * B.atom.U * scaleR k) by exact_mod_cast hbu).trans
      (Nat.floor_le (by positivity))
  have hcr : (v.2.1 : ℝ) ≤ packetCap B k :=
    (show (v.2.1 : ℝ) ≤ Nat.floor (packetCap B k) by exact_mod_cast hcu).trans
      (Nat.floor_le (by unfold packetCap; positivity))
  refine ⟨hbp, hcp, hbr.trans ?_, hcr⟩
  unfold packetCap
  have hUR : 0 < B.atom.U * scaleR k := mul_pos hU hR
  nlinarith

/-- The constant is chosen BEFORE B,k, the labels, rectangle and signed f.
This is a deduction from the installed fixed-order divisor theorem, not
a divisor-L2 or outer-normalization estimate supplied by a caller. -/
theorem divisorPrefixEnergy_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : FixedBlock) (atom : MediumAtom) (z : ℝ)
      (k : Key) (small : ℕ) (R : Rectangle) (st st' : ℕ × ℕ) (e : Fin 4),
      divisorPrefixEnergy B atom z k small R st st' e ≤
        C * packetCap B k ^ ε * unweightedPacketEnergy B atom z k small R st st' e := by
  obtain ⟨C, hC, hτ⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by omega) (show 0 < ε / 3 by positivity)
  refine ⟨C ^ 3, pow_pos hC _, ?_⟩
  intro B atom z k small R st st' e
  have hU := B.U_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  have hcap : 0 < packetCap B k := by unfold packetCap; positivity
  have hweight (v : PacketIndex) (hv : v ∈ packetAmbient B k) :
      ((v.1.divisors.card * v.2.1.divisors.card ^ 2 : ℕ) : ℝ) ≤
        C ^ 3 * packetCap B k ^ ε := by
    obtain ⟨hb, hc, hbcap, hccap⟩ := packetAmbient_positive_bounds B k hv
    have htb : (v.1.divisors.card : ℝ) ≤ C * packetCap B k ^ (ε / 3) := by
      calc
        _ = (fouvryTau 2 v.1 : ℝ) := by rw [fouvryTau_two]
        _ ≤ C * (v.1 : ℝ) ^ (ε / 3) := hτ v.1 hb
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hbcap (by positivity)) hC.le
    have htc : (v.2.1.divisors.card : ℝ) ≤ C * packetCap B k ^ (ε / 3) := by
      calc
        _ = (fouvryTau 2 v.2.1 : ℝ) := by rw [fouvryTau_two]
        _ ≤ C * (v.2.1 : ℝ) ^ (ε / 3) := hτ v.2.1 hc
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hccap (by positivity)) hC.le
    calc
      _ ≤ (C * packetCap B k ^ (ε / 3)) ^ 3 := by
        push_cast
        have hsq := pow_le_pow_left₀ (Nat.cast_nonneg v.2.1.divisors.card) htc 2
        have hm := mul_le_mul htb hsq (sq_nonneg _) (by positivity)
        nlinarith
      _ = C ^ 3 * packetCap B k ^ ε := by
        rw [mul_pow, ← Real.rpow_mul_natCast hcap.le]
        congr 2
        ring
  unfold divisorPrefixEnergy unweightedPacketEnergy
  rw [mul_sum]
  apply sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_right (hweight v hv) (sq_nonneg _)

theorem divisorPrefixEnergy_scale_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℕ} {σ κ c0 : ℝ}
      (B : FixedBlock) (atom : MediumAtom) (hAtom : B.atom = atom)
      (hA : MediumAdmissible b σ κ c0 atom) (hσ : 0 ≤ σ)
      (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
      (st st' : ℕ × ℕ) (e : Fin 4) (hx : 1 < atom.scale),
      (originalOuter B atom z y k small R Br Bs st st').Nonempty →
      divisorPrefixEnergy B atom z k small R st st' e ≤
        C * atom.scale ^ ε * unweightedPacketEnergy B atom z k small R st st' e := by
  obtain ⟨C, hC, hbound⟩ := divisorPrefixEnergy_subpower hε
  refine ⟨C * (32 : ℝ) ^ ε, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro b σ κ c0 B atom hAtom hA hσ z y k small R Br Bs st st' e hx hne
  have hU := B.U_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  have hcap : 0 ≤ packetCap B k := by unfold packetCap; positivity
  have hE : 0 ≤ unweightedPacketEnergy B atom z k small R st st' e :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hp := Real.rpow_le_rpow hcap
    (packetCap_le_scale_of_nonempty B atom hAtom hA hσ z y k small R Br Bs st st' hx hne) hε.le
  calc
    _ ≤ C * packetCap B k ^ ε * unweightedPacketEnergy B atom z k small R st st' e :=
      hbound B atom z k small R st st' e
    _ ≤ C * (32 * atom.scale) ^ ε * unweightedPacketEnergy B atom z k small R st st' e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) hE
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ atom.scale)]; ring

/-- All 64 ordered labels and BOTH independent smooth-label sums remain
literal. The four upper-product branches are handled by the theorem below. -/
def upperNormalizedCharge (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) : ℝ :=
  ∑ e : Fin 4, ∑ _f : Fin 4, ∑ _g : Fin 4,
    ∑ st ∈ smoothLabels atom z y k small,
      ∑ st' ∈ smoothLabels atom z y k small,
        32 * normalizationP B k / Real.sqrt B.d *
          Real.sqrt (divisorPrefixEnergy B atom z k small R st st' e)

theorem upperAbelCharge_le_normalized {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    upperAbelCharge B atom z y k small R Br Bs ≤
      upperNormalizedCharge B atom z y k small R := by
  unfold upperAbelCharge upperNormalizedCharge
  apply sum_le_sum
  intro e he
  apply sum_le_sum
  intro f hf
  apply sum_le_sum
  intro g hg
  apply sum_le_sum
  intro st hst
  apply sum_le_sum
  intro st' hst'
  exact abelCauchyCharge_le_divisor_energy B atom hA z y k small R Br Bs st st' e f g hx hU hQ

/-- Direct independently defined poissonAtlasBlock.rectangleSum caller.
The exact UU-LU-UL+LL identity is K's preceding source theorem; each of
its four positive charges receives the same proved normalization. -/
theorem actual_rectangleSum_norm_le_normalized
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (R : Rectangle) (hx : 1 < atom.scale) :
    let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
    ‖B.rectangleSum R‖ ≤ 4 * upperNormalizedCharge B atom z y k small R := by
  dsimp only
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let U := upperProductBound k
  let L := lowerProductBound k
  have hxB : 1 < B.x := hx
  have hUB : 1 ≤ B.atom.U := hA.1
  have hQB : 1 ≤ B.atom.Q1 := hA.2.2.1
  have hUU := upperAbelCharge_le_normalized B atom hA z y k small R U U hxB hUB hQB
  have hLU := upperAbelCharge_le_normalized B atom hA z y k small R L U hxB hUB hQB
  have hUL := upperAbelCharge_le_normalized B atom hA z y k small R U L hxB hUB hQB
  have hLL := upperAbelCharge_le_normalized B atom hA z y k small R L L hxB hUB hQB
  have hh := actual_rectangleSum_norm_le_four_Abel_charges atom z y k hA Csep j small hd negative R
  change ‖B.rectangleSum R‖ ≤
    upperAbelCharge B atom z y k small R U U +
    upperAbelCharge B atom z y k small R L U +
    upperAbelCharge B atom z y k small R U L +
    upperAbelCharge B atom z y k small R L L at hh
  change ‖B.rectangleSum R‖ ≤ 4 * upperNormalizedCharge B atom z y k small R
  linarith

end ImbalancedChen.Part3.OriginalMaskedOuterCaller20261102
