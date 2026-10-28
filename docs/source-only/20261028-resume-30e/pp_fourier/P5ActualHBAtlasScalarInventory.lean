import ImbalancedChen.P5NativeFullQActualHBTail
import ImbalancedChen.P5ActualHBDyadicOccurrenceFamily
import ImbalancedChen.P5OriginalDyadicRankUnion

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The scalar inventory is the literal order-three HB choice (+3,-3,+1),
its existing actual unit/right-closed dyadic occurrence bank, the original
smooth prime-chart bank, and every original rank. It is not an arbitrary
finite piece family supplied with the desired scalar-mass conclusion.
Physical modulus marks have ALREADY been summed inside nativeRho; they
are never charged again as external marked-prime scalar multiplicities.
-/
namespace ImbalancedChen.P5Z.ActualHBAtlasScalarInventory
noncomputable section
open Classical
open scoped BigOperators
open NativeFullQActualHBTail ActualHBPostModulusLogCutoff CompleteProductTailDivisorBudgets
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ExactOriginalSmoothDyadicPartition OriginalDyadicRankUnion

abbrev Choice := Σ _ : ℕ, List Block

def hbSign (j : ℕ) : ℂ := (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ)) : ℂ)

def singleBank (cap : ℕ) : Finset Choice :=
  (Finset.range 3).sigma (fun j => blockWords cap (2 * (j + 1)))

def hbBank (cap : ℕ) : ℕ → Finset (List Choice)
  | 0 => {[]}
  | k + 1 => ((singleBank cap).product (hbBank cap k)).image (fun p => p.1 :: p.2)

def hbScalar : List Choice → ℂ
  | [] => 1
  | c :: cs => hbSign c.1 * hbScalar cs

def dimension : List Choice → ℕ
  | [] => 0
  | c :: cs => c.2.length + dimension cs

/-- The universal bank is fixed from cap, before any HB factor tuple.
It reconstructs the same actual rough roles, not just a family with a
convenient cardinality. The literal product n is unchanged. -/
theorem capped_actual_term_decomposition (z y : ℝ) (j n cap : ℕ) (hn : n ≤ cap) :
    (∑ ps ∈ LiteralHeathBrownOccurrenceWords.factorTuples (2 * (j + 1)) n,
      ActualRoughHeathBrownWords.roughTupleWeight z y (ActualRoughHeathBrownWords.roles j) ps) =
      ∑ bs ∈ blockWords cap (2 * (j + 1)), blockCoefficient z y j n bs := by
  calc
    _ = ∑ ps ∈ LiteralHeathBrownOccurrenceWords.factorTuples (2 * (j + 1)) n,
        ∑ bs ∈ blockWords cap (2 * (j + 1)),
          assignedWeight z y (ActualRoughHeathBrownWords.roles j) bs ps := by
      apply Finset.sum_congr rfl
      intro ps hps
      have hp (p : ℕ) (hpm : p ∈ ps) : 0 < p ∧ p ≤ cap := by
        have hb := actual_factor_bound hps hpm
        exact ⟨hb.1, hb.2.trans hn⟩
      simpa only [ActualRoughHeathBrownWords.roles_length] using
        (occurrence_reconstruct cap z y (ActualRoughHeathBrownWords.roles j) ps hp).symm
    _ = _ := Finset.sum_comm

theorem capped_actual_rough_HB_identity {z y : ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y)
    {n cap : ℕ} (hn : (n : ℝ) ≤ y ^ 3) (hcap : n ≤ cap) :
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ImbalancedChen.Part3.roughOneSlot z n =
      ∑ c ∈ singleBank cap, hbSign c.1 * blockCoefficient z y c.1 n c.2 := by
  rw [ActualRoughHeathBrownWords.actual_rough_order_three_identity hz hy hn]
  rw [singleBank, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, ← capped_actual_term_decomposition z y j n cap hcap]
  rfl

theorem hbBank_spec (cap : ℕ) : ∀ k : ℕ, ∀ cs ∈ hbBank cap k,
    cs.length = k ∧ (∀ c ∈ cs, c.1 < 3 ∧ c.2.length = 2 * (c.1 + 1)) ∧
      dimension cs ≤ 6 * k := by
  intro k
  induction k with
  | zero =>
    intro cs hcs
    have heq : cs = [] := by simpa only [hbBank, Finset.mem_singleton] using hcs
    subst cs
    simp [dimension]
  | succ k ih =>
    intro cs hcs
    obtain ⟨⟨c, ds⟩, hcd, rfl⟩ := Finset.mem_image.mp hcs
    obtain ⟨hc, hds⟩ := Finset.mem_product.mp hcd
    obtain ⟨hj, hbs⟩ := Finset.mem_sigma.mp hc
    have hj3 : c.1 < 3 := Finset.mem_range.mp hj
    have hlen := (blockWords_spec cap (2 * (c.1 + 1)) c.2 hbs).1
    obtain ⟨hdlen, hdspec, hdim⟩ := ih ds hds
    refine ⟨by simp [hdlen], ?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨hj3, hlen⟩
      · exact hdspec d hd
    · simp only [dimension]
      omega

theorem singleBank_scalar_mass_le (cap : ℕ) :
    (∑ c ∈ singleBank cap, ‖hbSign c.1‖) ≤
      7 * (Nat.log2 (cap - 1) + 2 : ℕ) ^ (6 : ℕ) := by
  let B : ℝ := (Nat.log2 (cap - 1) + 2 : ℕ)
  have hB : 1 ≤ B := by dsimp [B]; norm_cast; omega
  have h2 : B ^ 2 ≤ B ^ 6 := pow_le_pow_right₀ hB (by omega)
  have h4 : B ^ 4 ≤ B ^ 6 := pow_le_pow_right₀ hB (by omega)
  have hsum : (∑ c ∈ singleBank cap, ‖hbSign c.1‖) =
      3 * B ^ 2 + 3 * B ^ 4 + B ^ 6 := by
    rw [singleBank, Finset.sum_sigma]
    simp only [Finset.sum_const, nsmul_eq_mul, blockWords_card]
    norm_num [Finset.sum_range_succ, hbSign, Complex.norm_real, Real.norm_eq_abs, B]
  rw [hsum]
  change _ ≤ 7 * B ^ 6
  linarith

theorem hbBank_scalar_mass_le (cap : ℕ) : ∀ k : ℕ,
    (∑ cs ∈ hbBank cap k, ‖hbScalar cs‖) ≤
      (7 * (Nat.log2 (cap - 1) + 2 : ℕ) ^ (6 : ℕ) : ℝ) ^ k := by
  intro k
  induction k with
  | zero => simp [hbBank, hbScalar]
  | succ k ih =>
    have hinj : Function.Injective (fun p : Choice × List Choice => p.1 :: p.2) := by
      intro p q hpq
      exact Prod.ext (List.cons.inj hpq).1 (List.cons.inj hpq).2
    rw [hbBank, Finset.sum_image]
    · simp only [Finset.sum_product, hbScalar, norm_mul]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      exact (mul_le_mul (singleBank_scalar_mass_le cap) ih
        (Finset.sum_nonneg (fun cs hcs => norm_nonneg _)) (by positivity)).trans_eq (by
          rw [pow_succ]
          ring)
    · intro p hp q hq heq
      exact hinj heq

/-- A literal occurrence-position dictionary, including repeated values.
Each head group occupies its own consecutive Fin block, never a product
image or a sorted quotient. Unit blocks keep their own position. -/
def pieceOwner : (cs : List Choice) → Fin (dimension cs) → Fin cs.length
  | [], a => Fin.elim0 a
  | _c :: cs => Fin.addCases (fun _ => 0) (fun a => (pieceOwner cs a).succ)

def pieceBlocks : (cs : List Choice) → Fin (dimension cs) → Block
  | [], a => Fin.elim0 a
  | c :: cs => Fin.addCases (fun a => c.2.get a) (pieceBlocks cs)

def pieceRoles : (cs : List Choice) → Fin (dimension cs) → ActualRoughHeathBrownWords.Role
  | [], a => Fin.elim0 a
  | c :: cs => Fin.addCases
      (fun a => (ActualRoughHeathBrownWords.roles c.1).getD a.val .one) (pieceRoles cs)

def rankOwner {cs : List Choice} {k : ℕ} (h : cs.length = k) :
    Fin (dimension cs) → Fin k := fun a => Fin.cast h (pieceOwner cs a)

/-- Genuine canonical original smooth prime-chart scales; no length is
measured from the residual quotient. getD only totalizes unused data. -/
def originalR (js : List ℕ) (k : ℕ) (i : Fin k) : ℝ := (2 : ℝ) ^ js.getD i.val 0

theorem originalR_pos (js : List ℕ) (k : ℕ) (i : Fin k) : 0 < originalR js k i := by
  unfold originalR
  positivity

def occurrenceCutoff {cs : List Choice} {k : ℕ} (hlen : cs.length = k)
    (js : List ℕ) (a : Fin (dimension cs)) : ℝ :=
  (2 * originalR js k (rankOwner hlen a)) ^ (1 / 3 : ℝ)

theorem occurrenceCutoff_pos {cs : List Choice} {k : ℕ} (hlen : cs.length = k)
    (js : List ℕ) (a : Fin (dimension cs)) : 0 < occurrenceCutoff hlen js a := by
  exact Real.rpow_pos_of_pos (mul_pos (by norm_num) (originalR_pos js k _)) _

def dyadicConstant : ℝ := 2 + 1 / Real.log 2

theorem dyadicConstant_pos : 0 < dyadicConstant := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dyadicConstant
  positivity

/-- Finite exact logarithmic count, including cap=0 and the two unit/
endpoint paddings. This is proved from 2^log2(n)<=n, not an assumed
polylogarithmic family cardinality. -/
theorem log2_count_le {X : ℝ} (hX : 1 ≤ X) (n : ℕ) (hn : (n : ℝ) ≤ 6 * X) :
    ((Nat.log2 n + 2 : ℕ) : ℝ) ≤ dyadicConstant * logScale X := by
  have hL : 1 ≤ logScale X := logScale_one_le hX
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hz : n = 0
  · subst n
    simp only [Nat.log2_zero, Nat.zero_add, Nat.cast_ofNat]
    have hC : 2 ≤ dyadicConstant := by
      unfold dyadicConstant
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) h2.le]
    exact hC.trans (le_mul_of_one_le_right dyadicConstant_pos.le hL)
  · have hp : (2 : ℕ) ^ Nat.log2 n ≤ n := (Nat.le_log2 hz).mp le_rfl
    have hpR : (2 : ℝ) ^ Nat.log2 n ≤ 7 * X :=
      (show (2 : ℝ) ^ Nat.log2 n ≤ (n : ℝ) by exact_mod_cast hp).trans (by linarith)
    have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpR
    rw [Real.log_pow] at hl
    have hj : (Nat.log2 n : ℝ) ≤ Real.log (7 * X) / Real.log 2 :=
      (le_div_iff₀ h2).mpr (by simpa only [mul_comm] using hl)
    simp only [Nat.cast_add, Nat.cast_ofNat]
    unfold dyadicConstant logScale at *
    have hxlog : 0 ≤ Real.log (7 * X) := Real.log_nonneg (by linarith)
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) h2.le]

def inventoryConstant (kStar : ℕ) : ℝ :=
  (kStar + 1 : ℕ) * (7 : ℝ) ^ kStar * dyadicConstant ^ (7 * kStar)

theorem inventoryConstant_nonneg (kStar : ℕ) : 0 ≤ inventoryConstant kStar := by
  have := dyadicConstant_pos
  unfold inventoryConstant
  positivity

/-- All genuine HB ranks, the signed coefficients +3, -3, +1, every actual
unit/right-closed occurrence block and every original smooth dyadic
label. The exponent 7*kStar is fixed before cap, X and Fourier accuracy. -/
theorem complete_inventory_mass_le (kStar cap : ℕ) {X : ℝ} (hX : 1 ≤ X)
    (hcap : (cap : ℝ) ≤ 6 * X) :
    (∑ k : Fin (kStar + 1), ∑ _js ∈ chartBank cap k.val,
      ∑ cs ∈ hbBank cap k.val, ‖hbScalar cs‖) ≤
      inventoryConstant kStar * logScale X ^ (7 * kStar) := by
  let L := dyadicConstant * logScale X
  have hL : 1 ≤ L := by
    have hC : 1 ≤ dyadicConstant := by
      have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      unfold dyadicConstant
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) h2.le]
    exact one_le_mul hC (logScale_one_le hX)
  have hc := log2_count_le hX cap hcap
  have hb := log2_count_le hX (cap - 1)
    ((show ((cap - 1 : ℕ) : ℝ) ≤ (cap : ℝ) by exact_mod_cast Nat.sub_le cap 1).trans hcap)
  have hlocal (k : Fin (kStar + 1)) :
      (∑ _js ∈ chartBank cap k.val, ∑ cs ∈ hbBank cap k.val, ‖hbScalar cs‖) ≤
        (7 : ℝ) ^ kStar * L ^ (7 * kStar) := by
    have hk : k.val ≤ kStar := by omega
    calc
      _ = ((cutoffIndex cap + 1 : ℕ) : ℝ) ^ k.val *
          (∑ cs ∈ hbBank cap k.val, ‖hbScalar cs‖) := by
        rw [Finset.sum_const, nsmul_eq_mul, actual_chartBank_card, Nat.cast_pow]
      _ ≤ L ^ k.val * (7 * L ^ 6) ^ k.val := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by positivity) (by simpa only [cutoffIndex, Nat.add_assoc] using hc) _
        · exact (hbBank_scalar_mass_le cap k.val).trans
            (pow_le_pow_left₀ (by positivity)
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 6) (by norm_num)) _)
        · exact Finset.sum_nonneg (fun cs hcs => norm_nonneg _)
        · positivity
      _ = (7 : ℝ) ^ k.val * L ^ (7 * k.val) := by
        rw [mul_pow, ← pow_mul]
        calc
          _ = (7 : ℝ) ^ k.val * (L ^ k.val * L ^ (6 * k.val)) := by ring
          _ = _ := by rw [← pow_add]; congr 2; omega
      _ ≤ (7 : ℝ) ^ kStar * L ^ (7 * kStar) :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hk)
          (pow_le_pow_right₀ hL (Nat.mul_le_mul_left 7 hk)) (by positivity) (by positivity)
  calc
    _ ≤ ∑ _k : Fin (kStar + 1), (7 : ℝ) ^ kStar * L ^ (7 * kStar) :=
      Finset.sum_le_sum (fun k hk => hlocal k)
    _ = inventoryConstant kStar * logScale X ^ (7 * kStar) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold inventoryConstant L
      rw [mul_pow]
      ring

end
end ImbalancedChen.P5Z.ActualHBAtlasScalarInventory
