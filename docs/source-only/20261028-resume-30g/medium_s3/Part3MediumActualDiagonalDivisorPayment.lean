import ImbalancedChen.Part3MediumLiteralS3Stages
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.Part3TransposedPrimitiveUPayment
import ImbalancedChen.Part3OriginalSamePsiS1OwnedAtlas
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The diagonal below is the actual E doubly-deleted S3 diagonal. Nonzero
deleted indicators, rather than a restoration model, force q,d,r,s into
the divisors of ONE NONZERO signed shift. Thus its four-coordinate fibre
costs tau(shift)^4, and its two actual lambdaTrim factors cost tau(shift)^2.
No shifted-Shiu estimate or desired S3 error bound is a premise.
-/
namespace ImbalancedChen.Part3.MediumActualDiagonalDivisorPayment20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumDeletedIndicatorShift20261028 MediumActualPreliminaryCauchy20261028
open MediumActualPsiPreliminaryDispersion20261028 MediumPrimitivePsiSource20261028
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open OriginalMediumS1SeparatedDivisorMean OriginalGevreyFinalPsi20261028
open OriginalGevreyPoissonPacket20261028 OriginalGevreySharedRowDictionary20261028
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def actualDiagonal (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ t ∈ diagonalCarrier atom k, S3DeletedTerm atom z y k t

def activeDiagonal (atom : MediumAtom) (z y : ℝ) (k : Key) : Finset PairIndex :=
  (diagonalCarrier atom k).filter (fun t => S3DeletedTerm atom z y k t ≠ 0)

def diagonalMN (t : PairIndex) : ℕ × ℕ := (t.1.2.2, t.2.1.2)

def actualMN (atom : MediumAtom) : Finset (ℕ × ℕ) :=
  paperPsiNaturalCarrier atom.V ×ˢ atom.alphaCarrier

def shiftAbs (atom : MediumAtom) (p : ℕ × ℕ) : ℕ :=
  (((p.2 * p.1 : ℕ) : ℤ) - atom.residue).natAbs

def modulusCode (t : PairIndex) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((t.1.1, t.1.2.1), (t.2.1.1, t.2.2.1))

theorem activeDiagonal_maps (atom : MediumAtom) (z y : ℝ) (k : Key)
    {t : PairIndex} (ht : t ∈ activeDiagonal atom z y k) :
    diagonalMN t ∈ actualMN atom := by
  have hp := (mem_filter.mp (mem_filter.mp ht).1).1
  have ho := (mem_filter.mp (mem_product.mp hp).1).1
  have hi := (mem_product.mp (mem_product.mp hp).2).1
  exact mem_product.mpr ⟨(mem_product.mp (mem_product.mp ho).2).2,
    (mem_product.mp hi).2⟩

/-- Both literal deleted gates force the same nonzero shift on the
diagonal. In particular there is no tau(0) convention in this proof. -/
theorem activeDiagonal_shift {atom : MediumAtom} {z y : ℝ} {k : Key}
    {t : PairIndex} (ht : t ∈ activeDiagonal atom z y k) :
    shiftAbs atom (diagonalMN t) ≠ 0 ∧
      (t.1.1 * t.1.2.1) * t.2.1.1 ∣ shiftAbs atom (diagonalMN t) ∧
      (t.1.1 * t.1.2.1) * t.2.2.1 ∣ shiftAbs atom (diagonalMN t) := by
  have hn := (mem_filter.mp ht).2
  have hdiag := (mem_filter.mp (mem_filter.mp ht).1).2
  have hfirst : firstDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro h
    exact hn (by simp [S3DeletedTerm, h])
  have hsecond : secondDeleted atom.residue (oldIndex t) ≠ 0 := by
    intro h
    exact hn (by simp [S3DeletedTerm, h])
  obtain ⟨hz, hleft⟩ := deletedIndicator_nonzero_data hfirst
  obtain ⟨_, hright⟩ := deletedIndicator_nonzero_data hsecond
  change t.2.1.2 = t.2.2.2 at hdiag
  refine ⟨Int.natAbs_ne_zero.mpr hz, ?_, ?_⟩
  · exact Int.natCast_dvd.mp hleft
  · simpa only [oldIndex, ← hdiag, shiftAbs, diagonalMN] using
      (Int.natCast_dvd.mp hright)

theorem activeDiagonal_divisor_code {atom : MediumAtom} {z y : ℝ} {k : Key}
    {t : PairIndex} (ht : t ∈ activeDiagonal atom z y k) :
    modulusCode t ∈
      ((shiftAbs atom (diagonalMN t)).divisors ×ˢ
        (shiftAbs atom (diagonalMN t)).divisors) ×ˢ
      ((shiftAbs atom (diagonalMN t)).divisors ×ˢ
        (shiftAbs atom (diagonalMN t)).divisors) := by
  obtain ⟨hw, hl, hr⟩ := activeDiagonal_shift ht
  have hq : t.1.1 ∣ shiftAbs atom (diagonalMN t) :=
    dvd_trans (dvd_mul_right _ _) (dvd_trans (dvd_mul_right _ _) hl)
  have hd : t.1.2.1 ∣ shiftAbs atom (diagonalMN t) :=
    dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) hl)
  have hdr : t.2.1.1 ∣ shiftAbs atom (diagonalMN t) :=
    dvd_trans (dvd_mul_left _ _) hl
  have hds : t.2.2.1 ∣ shiftAbs atom (diagonalMN t) :=
    dvd_trans (dvd_mul_left _ _) hr
  exact mem_product.mpr ⟨mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hq, hw⟩,
    Nat.mem_divisors.mpr ⟨hd, hw⟩⟩,
    mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hdr, hw⟩,
      Nat.mem_divisors.mpr ⟨hds, hw⟩⟩⟩

theorem modulusCode_injective_on_MN (atom : MediumAtom) (z y : ℝ)
    (k : Key) (p : ℕ × ℕ) :
    Set.InjOn modulusCode
      ((activeDiagonal atom z y k).filter (fun t => diagonalMN t = p)) := by
  intro t ht u hu htu
  have htD := (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).2
  have huD := (mem_filter.mp (mem_filter.mp (mem_filter.mp hu).1).1).2
  have hmn := (mem_filter.mp ht).2.trans (mem_filter.mp hu).2.symm
  have hq := congrArg (fun v : (ℕ × ℕ) × (ℕ × ℕ) => v.1.1) htu
  have hd := congrArg (fun v : (ℕ × ℕ) × (ℕ × ℕ) => v.1.2) htu
  have hr := congrArg (fun v : (ℕ × ℕ) × (ℕ × ℕ) => v.2.1) htu
  have hs := congrArg (fun v : (ℕ × ℕ) × (ℕ × ℕ) => v.2.2) htu
  have hm := congrArg Prod.fst hmn
  have hn := congrArg Prod.snd hmn
  change t.2.1.2 = t.2.2.2 at htD
  change u.2.1.2 = u.2.2.2 at huD
  exact Prod.ext (Prod.ext hq (Prod.ext hd hm))
    (Prod.ext (Prod.ext hr hn) (Prod.ext hs (htD.symm.trans (hn.trans huD))))

/-- A genuine physical fibre count, not an abstract deletion envelope. -/
theorem activeDiagonal_fibre_card_le (atom : MediumAtom) (z y : ℝ)
    (k : Key) (p : ℕ × ℕ) :
    (((activeDiagonal atom z y k).filter (fun t => diagonalMN t = p)).card : ℝ) ≤
      tauR (shiftAbs atom p) ^ 4 := by
  let F := (activeDiagonal atom z y k).filter (fun t => diagonalMN t = p)
  let D := (shiftAbs atom p).divisors
  have hs : F.image modulusCode ⊆ (D ×ˢ D) ×ˢ (D ×ˢ D) := by
    intro code hc
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hc
    have hp := (mem_filter.mp ht).2
    simpa only [hp] using activeDiagonal_divisor_code (mem_filter.mp ht).1
  have hn : F.card ≤ ((D ×ˢ D) ×ˢ (D ×ˢ D)).card := by
    rw [← card_image_iff.mpr (modulusCode_injective_on_MN atom z y k p)]
    exact card_le_card hs
  have hh : F.card ≤ D.card ^ 4 := by
    calc
      _ ≤ ((D ×ˢ D) ×ˢ (D ×ˢ D)).card := hn
      _ = _ := by simp only [card_product]; ring
  change (F.card : ℝ) ≤ (D.card : ℝ) ^ 4
  exact_mod_cast hh

theorem tauR_mono_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    tauR a ≤ tauR b := by
  apply Nat.cast_le.mpr
  apply card_le_card
  intro d hd
  exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.mem_divisors.mp hd).1 hab, hb⟩

theorem actualDiagonal_eq_active (atom : MediumAtom) (z y : ℝ) (k : Key) :
    actualDiagonal atom z y k =
      ∑ t ∈ activeDiagonal atom z y k, S3DeletedTerm atom z y k t := by
  symm
  apply sum_subset (filter_subset _ _)
  intro t ht hnot
  by_contra hn
  exact hnot (mem_filter.mpr ⟨ht, hn⟩)

theorem activeDiagonal_term_le_tau {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key)
    {t : PairIndex} (ht : t ∈ activeDiagonal atom z y k) :
    ‖S3DeletedTerm atom z y k t‖ ≤ tauR (shiftAbs atom (diagonalMN t)) ^ 2 := by
  obtain ⟨hw, hl, hr⟩ := activeDiagonal_shift ht
  have hp := (mem_filter.mp (mem_filter.mp ht).1).1
  have hi := mem_product.mp (mem_product.mp hp).2
  have hα := hA
  rcases hα with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hα, _⟩
  have hψ : ‖(jointPsi atom t.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (jointPsi_nonneg atom t.1)]
    exact mul_le_one₀ (paperPsi_le_one _) (paperPsi_nonneg _) (paperPsi_le_one _)
  have hdr : t.1.2.1 * t.2.1.1 ∣ shiftAbs atom (diagonalMN t) := by
    apply dvd_trans _ hl
    exact ⟨t.1.1, by ring⟩
  have hds : t.1.2.1 * t.2.2.1 ∣ shiftAbs atom (diagonalMN t) := by
    apply dvd_trans _ hr
    exact ⟨t.1.1, by ring⟩
  have hλr := (lambdaTrim_norm_le_tau atom z y k t.1.2.1 t.2.1.1 hA).trans
    (tauR_mono_dvd hw hdr)
  have hλs := (lambdaTrim_norm_le_tau atom z y k t.1.2.1 t.2.2.1 hA).trans
    (tauR_mono_dvd hw hds)
  unfold S3DeletedTerm pairCoefficient
  simp only [norm_mul, norm_star]
  calc
    _ ≤ 1 * tauR (shiftAbs atom (diagonalMN t)) *
        tauR (shiftAbs atom (diagonalMN t)) * 1 * 1 * 1 * 1 := by
      gcongr
      · exact hψ
      · exact hλr
      · exact hλs
      · exact hα _ (mem_product.mp hi.1).2
      · exact hα _ (mem_product.mp hi.2).2
      · exact deletedIndicator_norm_le_one _ _ _ _
      · exact deletedIndicator_norm_le_one _ _ _ _
    _ = _ := by ring

/-- Actual diagonal payment from a uniform *ordinary divisor* envelope.
The next theorem supplies this envelope from the original residue range;
it is not a hypothesis asserting a desired diagonal estimate. -/
theorem actualDiagonal_le_divisor_envelope {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key)
    {T : ℝ} (hT : 0 ≤ T)
    (hτ : ∀ p ∈ actualMN atom, shiftAbs atom p ≠ 0 → tauR (shiftAbs atom p) ≤ T) :
    ‖actualDiagonal atom z y k‖ ≤ (actualMN atom).card * T ^ 6 := by
  have hc : ((activeDiagonal atom z y k).card : ℝ) ≤ (actualMN atom).card * T ^ 4 := by
    have hf : (activeDiagonal atom z y k).card =
        ∑ p ∈ actualMN atom, ((activeDiagonal atom z y k).filter (fun t => diagonalMN t = p)).card :=
      card_eq_sum_card_fiberwise
      (fun t ht => activeDiagonal_maps atom z y k ht)
    rw [hf, Nat.cast_sum]
    calc
      _ ≤ ∑ _p ∈ actualMN atom, T ^ 4 := by
        apply sum_le_sum
        intro p hp
        by_cases hzero : shiftAbs atom p = 0
        · have hempty : (activeDiagonal atom z y k).filter (fun t => diagonalMN t = p) = ∅ := by
            apply eq_empty_iff_forall_not_mem.mpr
            intro t ht
            have hs := (activeDiagonal_shift (mem_filter.mp ht).1).1
            exact hs (by rw [(mem_filter.mp ht).2, hzero])
          simp only [hempty, card_empty, Nat.cast_zero]
          positivity
        · exact (activeDiagonal_fibre_card_le atom z y k p).trans
            (pow_le_pow_left₀ (by dsimp [tauR]; positivity) (hτ p hp hzero) 4)
      _ = _ := by simp
  rw [actualDiagonal_eq_active]
  calc
    _ ≤ ∑ t ∈ activeDiagonal atom z y k, ‖S3DeletedTerm atom z y k t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ activeDiagonal atom z y k, T ^ 2 := by
      apply sum_le_sum
      intro t ht
      exact (activeDiagonal_term_le_tau hA z y k ht).trans
        (pow_le_pow_left₀ (by dsimp [tauR]; positivity)
          (hτ _ (activeDiagonal_maps atom z y k ht) (activeDiagonal_shift ht).1) 2)
    _ = ((activeDiagonal atom z y k).card : ℝ) * T ^ 2 := by simp
    _ ≤ ((actualMN atom).card * T ^ 4) * T ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg T)
    _ = _ := by ring

theorem actualMN_real_bounds {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) {p : ℕ × ℕ} (hp : p ∈ actualMN atom) :
    (p.1 : ℝ) ≤ 5 * atom.V / 2 ∧ (p.2 : ℝ) ≤ 2 * atom.U := by
  obtain ⟨hm, hn⟩ := mem_product.mp hp
  have hnI := (mem_filter.mp hn).1
  constructor
  · exact (show (p.1 : ℝ) ≤ (Nat.floor (5 * atom.V / 2) : ℝ) by
      exact_mod_cast (mem_Icc.mp hm).2).trans (Nat.floor_le (by linarith [hA.2.1]))
  · exact (show (p.2 : ℝ) ≤ (Nat.floor (2 * atom.U) : ℝ) by
      exact_mod_cast (mem_Icc.mp hnI).2).trans (Nat.floor_le (by linarith [hA.1]))

/-- The original moving signed residue has a FIXED polynomial bound.
The smooth m endpoint is 5M/2, not the old dyadic bump's endpoint. -/
theorem actual_shift_polynomial {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) {p : ℕ × ℕ} (hp : p ∈ actualMN atom) :
    (shiftAbs atom p : ℝ) ≤ 6 * atom.scale ^ (max 1 (1 + κ)) := by
  have hx : 1 ≤ atom.scale := by
    unfold MediumAtom.scale
    nlinarith [hA.1, hA.2.1]
  have hκ : (atom.residue.natAbs : ℝ) ≤ atom.scale ^ (1 + κ) := hA.2.2.2.2.2.2.2.1
  have hxK : atom.scale ≤ atom.scale ^ (max 1 (1 + κ)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (le_max_left (1 : ℝ) (1 + κ))
  have haK : |(atom.residue : ℝ)| ≤ atom.scale ^ (max 1 (1 + κ)) := by
    have ha : |(atom.residue : ℝ)| ≤ atom.scale ^ (1 + κ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hκ
    exact ha.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + κ)))
  obtain ⟨hm, hn⟩ := actualMN_real_bounds hA hp
  have hprod : (p.2 : ℝ) * p.1 ≤ 5 * atom.scale := by
    calc
      _ ≤ (2 * atom.U) * (5 * atom.V / 2) :=
        mul_le_mul hn hm (Nat.cast_nonneg _) (by linarith [hA.1])
      _ = _ := by unfold MediumAtom.scale; ring
  have hid : (shiftAbs atom p : ℝ) = |(p.2 : ℝ) * p.1 - atom.residue| := by
    simp only [shiftAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Nat.cast_mul]
  rw [hid]
  calc
    _ ≤ |(p.2 : ℝ) * p.1| + |(atom.residue : ℝ)| := abs_sub _ _
    _ = (p.2 : ℝ) * p.1 + |(atom.residue : ℝ)| := by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    _ ≤ _ := by linarith

theorem actualMN_card_le {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) :
    ((actualMN atom).card : ℝ) ≤ 12 * atom.scale := by
  have hM : ((paperPsiNaturalCarrier atom.V).card : ℝ) ≤ 4 * atom.V := by
    have hs : paperPsiNaturalCarrier atom.V ⊆ range (Nat.floor (5 * atom.V / 2) + 1) := by
      intro m hm
      exact mem_range.mpr (by have := (mem_Icc.mp hm).2; omega)
    have hc := card_le_card hs
    simp only [card_range] at hc
    have hcR : ((paperPsiNaturalCarrier atom.V).card : ℝ) ≤
        (Nat.floor (5 * atom.V / 2) : ℝ) + 1 := by exact_mod_cast hc
    have hf := Nat.floor_le (show 0 ≤ 5 * atom.V / 2 by linarith [hA.2.1])
    linarith [hA.2.1]
  have hN : (atom.alphaCarrier.card : ℝ) ≤ 3 * atom.U := by
    have hs : atom.alphaCarrier ⊆ range (Nat.floor (2 * atom.U) + 1) := by
      intro n hn
      exact mem_range.mpr (by have := (mem_Icc.mp (mem_filter.mp hn).1).2; omega)
    have hc := card_le_card hs
    simp only [card_range] at hc
    have hcR : (atom.alphaCarrier.card : ℝ) ≤ (Nat.floor (2 * atom.U) : ℝ) + 1 := by
      exact_mod_cast hc
    have hf := Nat.floor_le (show 0 ≤ 2 * atom.U by linarith [hA.1])
    linarith [hA.1]
  unfold actualMN
  rw [card_product, Nat.cast_mul]
  calc
    _ ≤ (4 * atom.V) * (3 * atom.U) :=
      mul_le_mul hM hN (Nat.cast_nonneg _) (by linarith [hA.2.1])
    _ = _ := by unfold MediumAtom.scale; ring

/-- Constants precede every atom, dyadic key, coefficient fibre and
moving residue. This is the actual divisor supplier used below. -/
theorem exists_actual_shift_tau_envelope (κ ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ (B : ℕ) (σ c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → ∀ p ∈ actualMN atom,
      shiftAbs atom p ≠ 0 → tauR (shiftAbs atom p) ≤ T * atom.scale ^ (ε / 6) := by
  let K : ℝ := max 1 (1 + κ)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let η : ℝ := (ε / 6) / K
  have hη : 0 < η := div_pos (by positivity) hK
  obtain ⟨C, hC, htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) hη
  refine ⟨C * (6 : ℝ)^η, by positivity, ?_⟩
  intro B σ c0 atom hA p hp hw
  have hx : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  have hτ : tauR (shiftAbs atom p) ≤ C * (shiftAbs atom p : ℝ)^η := by
    simpa only [tauR, fouvryTau_two] using htau _ (Nat.pos_of_ne_zero hw)
  calc
    _ ≤ C * (shiftAbs atom p : ℝ)^η := hτ
    _ ≤ C * (6 * atom.scale ^ K)^η := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (actual_shift_polynomial hA hp) hη.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg hx.le K),
        ← Real.rpow_mul hx.le]
      have hKη : K * η = ε / 6 := by dsimp [η]; field_simp [hK.ne']
      rw [hKη]
      ring

/-- The actual deleted diagonal costs C_epsilon*x^(1+epsilon), uniformly
over all actual lambdaTrim keys and signed polynomially moving residues.
This is a genuine power payment, stronger than the earlier finite kernel.
-/
theorem exists_actual_deleted_diagonal_subpower (κ ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (σ c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → ∀ (z y : ℝ) (k : Key),
      ‖actualDiagonal atom z y k‖ ≤ C * atom.scale ^ (1 + ε) := by
  obtain ⟨T, hT, hτ⟩ := exists_actual_shift_tau_envelope κ ε hε
  refine ⟨12 * T ^ 6, by positivity, ?_⟩
  intro B σ c0 atom hA z y k
  have hx : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  calc
    _ ≤ (actualMN atom).card * (T * atom.scale ^ (ε / 6)) ^ 6 :=
      actualDiagonal_le_divisor_envelope hA z y k (by positivity) (hτ B σ c0 atom hA)
    _ ≤ (12 * atom.scale) * (T * atom.scale ^ (ε / 6)) ^ 6 :=
      mul_le_mul_of_nonneg_right (actualMN_card_le hA) (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hx.le,
        show (ε / 6) * ((6 : ℕ) : ℝ) = ε by norm_num; ring]
      rw [show 1 + ε = ε + 1 by ring, Real.rpow_add_one hx.ne']
      ring

def actualVScale (atom : MediumAtom) (k : Key) : ℝ :=
  atom.V * atom.U ^ 2 / keyY atom k

theorem keyY_positive {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (k : Key) : 0 < keyY atom k := by
  unfold keyY keyD
  exact mul_pos (zero_lt_one.trans_le hA.2.2.1) (by positivity)

/-- This is exactly the preliminary geometry Y<=N*x^(-delta) in (9),
not a bound on the S3 correction. -/
theorem diagonal_scale_ge_power {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (δ : ℝ) (k : Key)
    (hgeom : keyY atom k ≤ atom.U * atom.scale ^ (-δ)) :
    atom.scale ^ (1 + δ) ≤ actualVScale atom k := by
  have hx : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  apply (le_div_iff₀ (keyY_positive hA k)).mpr
  calc
    atom.scale ^ (1 + δ) * keyY atom k ≤
        atom.scale ^ (1 + δ) * (atom.U * atom.scale ^ (-δ)) :=
      mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg hx.le _)
    _ = atom.U * atom.scale := by
      rw [mul_left_comm, ← Real.rpow_add hx,
        show (1 + δ) + -δ = (1 : ℝ) by ring, Real.rpow_one]
    _ = atom.V * atom.U ^ 2 := by unfold MediumAtom.scale; ring

/-- Arbitrary-log payment of the TRUE deleted diagonal. Constants and
one common threshold precede every atom, original receiver, trim and key.
No compiler claim is made; rough-gcd/close-pair corrections are separate.
-/
theorem exists_actual_deleted_diagonal_log_payment (κ δ A : ℝ) (hδ : 0 < δ) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (σ c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → x0 ≤ atom.scale →
      ∀ (z y : ℝ) (k : Key), keyY atom k ≤ atom.U * atom.scale ^ (-δ) →
      ‖actualDiagonal atom z y k‖ ≤ actualVScale atom k / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, hdiag⟩ := exists_actual_deleted_diagonal_subpower κ (δ / 2) (by positivity)
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow C A hC.le
      (show 0 < δ / 2 by positivity))
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro B σ c0 atom hA hx z y k hgeom
  have hx1' : x1 ≤ atom.scale :=
    (le_max_left x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx)
  have hx2' : x2 ≤ atom.scale :=
    (le_max_right x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx)
  have hlog : 0 < Real.log atom.scale := lt_of_lt_of_le zero_lt_one (hx2 _ hx2')
  have hxp : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hA.1, hA.2.1]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog A)).mpr
  calc
    _ ≤ (C * atom.scale ^ (1 + δ / 2)) * Real.log atom.scale ^ A :=
      mul_le_mul_of_nonneg_right (hdiag B σ c0 atom hA z y k)
        (Real.rpow_nonneg hlog.le A)
    _ = atom.scale ^ (1 + δ / 2) * (C * Real.log atom.scale ^ A) := by ring
    _ ≤ atom.scale ^ (1 + δ / 2) * atom.scale ^ (δ / 2) :=
      mul_le_mul_of_nonneg_left (hx1 _ hx1') (Real.rpow_nonneg hxp.le _)
    _ = atom.scale ^ (1 + δ) := by
      rw [← Real.rpow_add hxp]
      congr 1
      ring
    _ ≤ _ := diagonal_scale_ge_power hA δ k hgeom

end
end ImbalancedChen.Part3.MediumActualDiagonalDivisorPayment20261028
