import ImbalancedChen.Part3OriginalReciprocalAbelCaller
import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Divisors

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT. All full targets remain OPEN.

Count the actual J/K outer IMAGE, not the much larger source carrier.
The signed quotient reconstructs n1, so the count has U^2/d rather than
Q*U^2. Only positive square sums are enlarged. The prefix energies and
all spectral inputs remain explicit. No outerL2 or P estimate is a premise.
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
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102

attribute [local instance] Classical.propDecidable

abbrev originalOuter (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ) :=
  (sourceCarrier B atom z y k small R Br Bs st st').image (outer B)

def scaleS (k : Key) : ℝ := (2 ^ k.u : ℕ)
def scaleR (k : Key) : ℝ := (2 ^ k.v : ℕ)

theorem scaleS_pos (k : Key) : 0 < scaleS k := by
  unfold scaleS
  positivity

theorem scaleR_pos (k : Key) : 0 < scaleR k := by
  unfold scaleR
  positivity

def signedWindow (T : ℝ) : Finset ℤ :=
  (Icc (-(Nat.floor T : ℤ)) (Nat.floor T : ℤ)).erase 0

/-- Both signs, no zero, and no spurious +1 in the count. -/
theorem signedWindow_card (T : ℝ) : (signedWindow T).card = 2 * Nat.floor T := by
  unfold signedWindow
  rw [card_erase_of_mem (by simp), Int.card_Icc]
  omega

theorem mem_signedWindow {T : ℝ} {f : ℤ} (hf : f ≠ 0)
    (hbound : |(f : ℝ)| ≤ T) : f ∈ signedWindow T := by
  have habs : (f.natAbs : ℝ) = |(f : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hn : f.natAbs ≤ Nat.floor T := Nat.le_floor (habs.symm ▸ hbound)
  have hi : |f| ≤ (Nat.floor T : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  exact mem_erase.mpr ⟨hf, mem_Icc.mpr (abs_le.mp hi)⟩

theorem signedWindow_mono {T V : ℝ} (hTV : T ≤ V) :
    signedWindow T ⊆ signedWindow V := by
  intro f hf
  obtain ⟨hf0, hf⟩ := mem_erase.mp hf
  obtain ⟨hl, hu⟩ := mem_Icc.mp hf
  have hfl : (Nat.floor T : ℤ) ≤ Nat.floor V := by
    exact_mod_cast Nat.floor_mono hTV
  exact mem_erase.mpr ⟨hf0, mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem signedWindow_card_le {T : ℝ} (hT : 0 ≤ T) :
    ((signedWindow T).card : ℝ) ≤ 2 * T := by
  rw [signedWindow_card, Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left (Nat.floor_le hT) (by norm_num)

theorem commonR_window (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) {r : ℕ} (hr : r ∈ commonR atom z k small st) :
    2 ^ k.v ≤ r ∧ r < 2 * 2 ^ k.v := by
  have hw := (mem_filter.mp (mem_filter.mp hr).1).1
  change r ∈ Icc (2 ^ k.v) (2 ^ (k.v + 1) - 1) at hw
  have hh := mem_Icc.mp hw
  rw [pow_succ] at hh
  omega

/-- The exact image has the original outer gates; existence of an inner
source point is used, not supplied as a new source-equality hypothesis. -/
theorem originalOuter_gate (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    {o : Outer} (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') :
    outerGate B atom z y k small R Bs st st' o := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ho
  have hi : inner s ∈ innerImage B atom z y k small R Br Bs st st' (outer B s) :=
    mem_image.mpr ⟨s, mem_filter.mpr ⟨hs, rfl⟩, rfl⟩
  exact ((mem_innerImage_separated B atom z y k small R Br Bs st st'
    (outer B s) (inner s).1 (inner s).2).mp hi).1

theorem originalOuter_equation (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    {o : Outer} (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') :
    ((o.q * B.d : ℕ) : ℤ) * o.f = (o.n1 : ℤ) - o.n2 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ho
  exact signedF_mul B (mem_filter.mp (mem_product.mp (mem_filter.mp hs).1).1).1

theorem originalOuter_f_ne_zero (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (hx : 1 < B.x) {o : Outer}
    (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') : o.f ≠ 0 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ho
  exact signedF_ne_zero B hx
    (mem_filter.mp (mem_product.mp (mem_filter.mp hs).1).1).1

theorem qCarrier_bounds (B : FixedBlock) {q : ℕ} (hq : q ∈ B.qCarrier) :
    B.atom.Q1 / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 4 * B.atom.Q1 := by
  obtain ⟨hl, hu⟩ := mem_Icc.mp hq
  have hl' : (B.qLo : ℝ) ≤ q := by exact_mod_cast hl
  have hu' : (q : ℝ) ≤ B.qHi := by exact_mod_cast hu
  constructor
  · exact B.q0_from_Q_lo.trans (B.qLo_block.trans hl')
  · have := B.qHi_block
    have := B.q0_from_Q_hi
    linarith

theorem originalOuter_f_bound (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    {o : Outer} (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') :
    |(o.f : ℝ)| ≤ 2 * B.atom.U / (B.atom.Q1 * B.d) := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ho
  have ht := (mem_filter.mp (mem_product.mp (mem_filter.mp hs).1).1).1
  have hq := (qCarrier_bounds B ((mem_original_carrier B s.1).mp ht).1).1
  have hb := signedF_original_bound B ht
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  have hmul : |(signedF B s.1 : ℝ)| * (B.atom.Q1 * B.d) ≤ 2 * B.atom.U := by
    have hh := mul_le_mul_of_nonneg_left hq
      (mul_nonneg (abs_nonneg (signedF B s.1 : ℝ)) hd.le)
    push_cast at hb
    nlinarith
  exact (le_div_iff₀ (mul_pos B.Q_pos hd)).mpr hmul

abbrev OuterCode := ℕ × ℕ × ℕ × ℕ × ℕ × ℤ
def outerCode (o : Outer) : OuterCode := (o.q, o.n2, o.r1, o.s2, o.r2, o.f)

/-- This is the missing multiplicity correction in the first Cauchy:
n1 is not an additional free index. -/
theorem outerCode_injOn (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ) :
    Set.InjOn outerCode (originalOuter B atom z y k small R Br Bs st st') := by
  intro o ho o' ho' he
  have hq := congrArg (fun v : OuterCode => v.1) he
  have hn2 := congrArg (fun v : OuterCode => v.2.1) he
  have hr1 := congrArg (fun v : OuterCode => v.2.2.1) he
  have hs2 := congrArg (fun v : OuterCode => v.2.2.2.1) he
  have hr2 := congrArg (fun v : OuterCode => v.2.2.2.2.1) he
  have hf := congrArg (fun v : OuterCode => v.2.2.2.2.2) he
  have hE := originalOuter_equation B atom z y k small R Br Bs st st' ho
  have hE' := originalOuter_equation B atom z y k small R Br Bs st st' ho'
  dsimp only [outerCode] at hq hn2 hr1 hs2 hr2 hf
  have hn1 : o.n1 = o'.n1 := by rw [hq, hn2, hf] at hE; omega
  cases o
  cases o'
  simp_all

def outerAmbient (B : FixedBlock) (k : Key) : Finset OuterCode :=
  B.qCarrier ×ˢ (B.nCarrier ×ˢ
    (Ico (2 ^ k.v) (2 * 2 ^ k.v) ×ˢ
    (Ico (2 ^ k.u) (2 * 2 ^ k.u) ×ˢ
    (Ico (2 ^ k.v) (2 * 2 ^ k.v) ×ˢ
      signedWindow (2 * B.atom.U / (B.atom.Q1 * B.d))))))

theorem outerCode_mem_ambient (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (hx : 1 < B.x) {o : Outer}
    (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') :
    outerCode o ∈ outerAmbient B k := by
  obtain ⟨_, _, hr1, hs2, hr2, hq, _, _, hn2, _⟩ :=
    originalOuter_gate B atom z y k small R Br Bs st st' ho
  have hf := mem_signedWindow
    (originalOuter_f_ne_zero B atom z y k small R Br Bs st st' hx ho)
    (originalOuter_f_bound B atom z y k small R Br Bs st st' ho)
  exact mem_product.mpr ⟨hq, mem_product.mpr ⟨hn2,
    mem_product.mpr ⟨mem_Ico.mpr (commonR_window atom z k small st hr1),
    mem_product.mpr ⟨mem_Ico.mpr (commonS_window atom z k small st' hs2),
    mem_product.mpr ⟨mem_Ico.mpr (commonR_window atom z k small st' hr2), hf⟩⟩⟩⟩⟩

theorem qCarrier_card_le (B : FixedBlock) (hQ : 1 ≤ B.atom.Q1) :
    (B.qCarrier.card : ℝ) ≤ 5 * B.atom.Q1 := by
  have hsub : B.qCarrier ⊆ range (Nat.floor (4 * B.atom.Q1) + 1) := by
    intro q hq
    have hh := Nat.le_floor (qCarrier_bounds B hq).2
    exact mem_range.mpr (by omega)
  have hc : (B.qCarrier.card : ℝ) ≤ Nat.floor (4 * B.atom.Q1) + 1 := by
    have hh := card_le_card hsub
    simp only [card_range] at hh
    exact_mod_cast hh
  have hf := Nat.floor_le (by positivity : 0 ≤ 4 * B.atom.Q1)
  linarith

theorem nCarrier_card_le (B : FixedBlock) (hU : 1 ≤ B.atom.U) :
    (B.nCarrier.card : ℝ) ≤ 3 * B.atom.U := by
  have hsub : B.nCarrier ⊆ range (Nat.floor (2 * B.atom.U) + 1) := by
    intro n hn
    have hh := (mem_Icc.mp (mem_filter.mp hn).1).2
    exact mem_range.mpr (by omega)
  have hc : (B.nCarrier.card : ℝ) ≤ Nat.floor (2 * B.atom.U) + 1 := by
    have hh := card_le_card hsub
    simp only [card_range] at hh
    exact_mod_cast hh
  have hf := Nat.floor_le (by positivity : 0 ≤ 2 * B.atom.U)
  linarith

/-- Every original mask is present on the left; only a nonnegative
cardinality is compared with the enclosing signed box on the right. -/
theorem originalOuter_card_le (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    ((originalOuter B atom z y k small R Br Bs st st').card : ℝ) ≤
      60 * B.atom.U ^ 2 * scaleR k ^ 2 * scaleS k / B.d := by
  have hc := card_le_card_of_injOn outerCode
    (fun o ho => outerCode_mem_ambient B atom z y k small R Br Bs st st' hx ho)
    (outerCode_injOn B atom z y k small R Br Bs st st')
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  have hf := signedWindow_card_le
    (by positivity : 0 ≤ 2 * B.atom.U / (B.atom.Q1 * B.d))
  have hr : (Ico (2 ^ k.v) (2 * 2 ^ k.v)).card = 2 ^ k.v := by simp; omega
  have hs : (Ico (2 ^ k.u) (2 * 2 ^ k.u)).card = 2 ^ k.u := by simp; omega
  calc
    _ ≤ (outerAmbient B k).card := by exact_mod_cast hc
    _ = (B.qCarrier.card : ℝ) * (B.nCarrier.card *
        (scaleR k * (scaleS k * (scaleR k *
          (signedWindow (2 * B.atom.U / (B.atom.Q1 * B.d))).card)))) := by
      simp only [outerAmbient, card_product, hr, hs, Nat.cast_mul, scaleR, scaleS]
    _ ≤ (5 * B.atom.Q1) * ((3 * B.atom.U) *
        (scaleR k * (scaleS k * (scaleR k *
          (2 * (2 * B.atom.U / (B.atom.Q1 * B.d))))))) := by
      gcongr
      · exact qCarrier_card_le B hQ
      · exact nCarrier_card_le B hU
      · exact hf
    _ = _ := by field_simp [B.Q_pos.ne', hd.ne']; ring

theorem outerCoefficient_norm_le {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) {o : Outer}
    (ho : o ∈ originalOuter B atom z y k small R Br Bs st st') :
    ‖outerCoefficient atom st st' e f g o‖ ≤
      2 / (B.atom.Q1 * scaleR k ^ 2 * scaleS k) := by
  have hQ := B.Q_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  obtain ⟨h2, h3, hn⟩ := actual_slots_one_bounded hA
  have hs := diagonal_norm_le_one _ _ e (h2 st.1) (h2 st'.1) o.s2
  have hr1 := diagonal_norm_le_one _ _ f (h3 st.2) (h3 st'.2) o.r1
  have hr2 := diagonal_norm_le_one _ _ f (h3 st.2) (h3 st'.2) o.r2
  have hn1 := diagonal_norm_le_one _ _ g hn hn o.n1
  have hn2 := diagonal_norm_le_one _ _ g hn hn o.n2
  have hnumer : ‖star (lambdaS atom st st' e o.s2) *
      (lambdaR atom st st' f o.r1 * star (lambdaR atom st st' f o.r2)) *
      (lambdaN atom g o.n1 * star (lambdaN atom g o.n2))‖ ≤ 1 := by
    simp only [norm_mul, norm_star]
    have hrr : ‖lambdaR atom st st' f o.r1‖ * ‖lambdaR atom st st' f o.r2‖ ≤ 1 := by
      exact (mul_le_mul hr1 hr2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hnn : ‖lambdaN atom g o.n1‖ * ‖lambdaN atom g o.n2‖ ≤ 1 := by
      exact (mul_le_mul hn1 hn2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hsr := mul_le_mul hs hrr (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    exact (mul_le_mul hsr hnn (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by ring)
  obtain ⟨_, _, hr1m, hs2m, hr2m, hqm, _⟩ :=
    originalOuter_gate B atom z y k small R Br Bs st st' ho
  have hq := (qCarrier_bounds B hqm).1
  have hr1b : scaleR k ≤ (o.r1 : ℝ) := by
    exact_mod_cast (commonR_window atom z k small st hr1m).1
  have hr2b : scaleR k ≤ (o.r2 : ℝ) := by
    exact_mod_cast (commonR_window atom z k small st' hr2m).1
  have hs2b : scaleS k ≤ (o.s2 : ℝ) := by
    exact_mod_cast (commonS_window atom z k small st' hs2m).1
  have hden : B.atom.Q1 * scaleR k ^ 2 * scaleS k / 2 ≤
      ((o.q * o.r1 * o.s2 * o.r2 : ℕ) : ℝ) := by
    calc
      _ = (B.atom.Q1 / 2) * scaleR k * scaleS k * scaleR k := by ring
      _ ≤ (o.q : ℝ) * o.r1 * o.s2 * o.r2 := by gcongr
      _ = _ := by push_cast; rfl
  have hbase : 0 < B.atom.Q1 * scaleR k ^ 2 * scaleS k := by
    positivity
  have hdenpos : (0 : ℝ) < (o.q * o.r1 * o.s2 * o.r2 : ℕ) :=
    (half_pos hbase).trans_le hden
  calc
    _ ≤ 1 / ((o.q * o.r1 * o.s2 * o.r2 : ℕ) : ℝ) := by
      rw [outerCoefficient, norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right hnumer hdenpos.le
    _ ≤ 1 / (B.atom.Q1 * scaleR k ^ 2 * scaleS k / 2) :=
      one_div_le_one_div_of_le (half_pos hbase) hden
    _ = _ := by field_simp [hbase.ne']; ring

def outerEnergy (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) : ℝ :=
  ∑ o ∈ originalOuter B atom z y k small R Br Bs st st',
    ‖outerCoefficient atom st st' e f g o‖ ^ 2

def prefixEnergy (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) : ℝ :=
  ∑ o ∈ originalOuter B atom z y k small R Br Bs st st',
    rowEnvelope B atom z k small R st st' e o ^ 2

theorem outerEnergy_le {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    outerEnergy B atom z y k small R Br Bs st st' e f g ≤
      240 * B.atom.U ^ 2 /
        (B.atom.Q1 ^ 2 * scaleR k ^ 2 * scaleS k * B.d) := by
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  calc
    _ ≤ ∑ _o ∈ originalOuter B atom z y k small R Br Bs st st',
        (2 / (B.atom.Q1 * scaleR k ^ 2 * scaleS k)) ^ 2 := by
      apply sum_le_sum
      intro o ho
      exact pow_le_pow_left₀ (norm_nonneg _)
        (outerCoefficient_norm_le B atom hA z y k small R Br Bs st st' e f g ho) 2
    _ = ((originalOuter B atom z y k small R Br Bs st st').card : ℝ) *
        (2 / (B.atom.Q1 * scaleR k ^ 2 * scaleS k)) ^ 2 := by simp
    _ ≤ (60 * B.atom.U ^ 2 * scaleR k ^ 2 * scaleS k / B.d) *
        (2 / (B.atom.Q1 * scaleR k ^ 2 * scaleS k)) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (originalOuter_card_le B atom z y k small R Br Bs st st' hx hU hQ) (sq_nonneg _)
    _ = _ := by field_simp [B.Q_pos.ne', hd.ne', hR.ne', hS.ne']; ring

/-- sqrt form of the manuscript S^(3/2), with R coming from Q3. -/
def normalizationP (B : FixedBlock) (k : Key) : ℝ :=
  B.atom.U / (B.atom.Q1 * scaleR k * scaleS k * Real.sqrt (scaleS k))

theorem normalizationP_eq_rpow (B : FixedBlock) (k : Key) :
    normalizationP B k = B.atom.U /
      (B.atom.Q1 * scaleR k * scaleS k ^ (3 / 2 : ℝ)) := by
  have he : scaleS k ^ (3 / 2 : ℝ) = scaleS k * Real.sqrt (scaleS k) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (scaleS_pos k), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [he, normalizationP]
  congr 1
  ring

theorem normalizationP_sq (B : FixedBlock) (k : Key) :
    normalizationP B k ^ 2 =
      B.atom.U ^ 2 / (B.atom.Q1 ^ 2 * scaleR k ^ 2 * scaleS k ^ 3) := by
  rw [normalizationP, div_pow]
  simp only [mul_pow, Real.sq_sqrt (scaleS_pos k).le]
  congr 1
  ring

theorem abelCauchyCharge_sq (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4) :
    abelCauchyCharge B atom z y k small R Br Bs st st' e f g ^ 2 =
      outerEnergy B atom z y k small R Br Bs st st' e f g *
        (4 / scaleS k ^ 2 * prefixEnergy B atom z y k small R Br Bs st st' e) := by
  unfold abelCauchyCharge
  rw [Real.sq_sqrt (mul_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _))]
  congr 1
  unfold prefixEnergy
  rw [mul_sum]
  apply sum_congr rfl
  intro o ho
  unfold scaleS
  ring

/-- The desired outside normalization is DERIVED from the source count.
The simultaneous prefix energy is not estimated or supplied as a premise. -/
theorem abelCauchyCharge_sq_le_P {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    abelCauchyCharge B atom z y k small R Br Bs st st' e f g ^ 2 ≤
      960 * normalizationP B k ^ 2 / B.d *
        prefixEnergy B atom z y k small R Br Bs st st' e := by
  have hE : 0 ≤ prefixEnergy B atom z y k small R Br Bs st st' e :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hQ0 := B.Q_pos
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  have hR := scaleR_pos k
  have hS := scaleS_pos k
  rw [abelCauchyCharge_sq]
  calc
    _ ≤ (240 * B.atom.U ^ 2 /
        (B.atom.Q1 ^ 2 * scaleR k ^ 2 * scaleS k * B.d)) *
        (4 / scaleS k ^ 2 * prefixEnergy B atom z y k small R Br Bs st st' e) :=
      mul_le_mul_of_nonneg_right
        (outerEnergy_le B atom hA z y k small R Br Bs st st' e f g hx hU hQ)
        (mul_nonneg (by positivity) hE)
    _ = _ := by
      rw [normalizationP_sq]
      field_simp [hQ0.ne', hd.ne', hR.ne', hS.ne']
      ring

theorem abelCauchyCharge_le_P {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    abelCauchyCharge B atom z y k small R Br Bs st st' e f g ≤
      32 * normalizationP B k / Real.sqrt B.d *
        Real.sqrt (prefixEnergy B atom z y k small R Br Bs st st' e) := by
  have hE : 0 ≤ prefixEnergy B atom z y k small R Br Bs st st' e :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hd : (0 : ℝ) < B.d := by exact_mod_cast B.d_pos
  have hU0 := B.U_pos
  have hQ0 := B.Q_pos
  have hR0 := scaleR_pos k
  have hS0 := scaleS_pos k
  have hP : 0 ≤ normalizationP B k := by
    unfold normalizationP
    positivity
  have hbound := abelCauchyCharge_sq_le_P B atom hA z y k small R Br Bs st st' e f g hx hU hQ
  have hright : (32 * normalizationP B k / Real.sqrt B.d *
      Real.sqrt (prefixEnergy B atom z y k small R Br Bs st st' e)) ^ 2 =
      1024 * normalizationP B k ^ 2 / B.d *
        prefixEnergy B atom z y k small R Br Bs st st' e := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hd.le, Real.sq_sqrt hE]
    norm_num
  have hgap : 0 ≤ normalizationP B k ^ 2 / B.d *
      prefixEnergy B atom z y k small R Br Bs st st' e := by positivity
  have hright0 : 0 ≤ 32 * normalizationP B k / Real.sqrt B.d *
      Real.sqrt (prefixEnergy B atom z y k small R Br Bs st st' e) := by positivity
  nlinarith

/-- Positive Cauchy has already happened inside K's theorem. -/
theorem frozenUpperPacket_norm_le_P {b : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e f g : Fin 4)
    (hx : 1 < B.x) (hU : 1 ≤ B.atom.U) (hQ : 1 ≤ B.atom.Q1) :
    ‖frozenUpperPacket B atom z y k small R Br Bs st st' e f g‖ ≤
      32 * normalizationP B k / Real.sqrt B.d *
        Real.sqrt (prefixEnergy B atom z y k small R Br Bs st st' e) :=
  (frozenUpperPacket_norm_le_abelCauchyCharge B atom z y k small R Br Bs st st' e f g).trans
    (abelCauchyCharge_le_P B atom hA z y k small R Br Bs st st' e f g hx hU hQ)

end ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
