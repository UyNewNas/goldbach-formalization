import ImbalancedChen.Part3ActualSeparatedRowFiniteMatcher
import ImbalancedChen.Part3CompactCoordinateFourier
import ImbalancedChen.Part3SharedFirstFactorGeneralDRowAdapter

set_option maxErrors 1000

/-!
SOURCEONLY / UNCOMPILED / HOLD.
Companion to P3CompactCoordinateSourceOnly, SHA933d9458, loaded FIRST.
Add these imports at the top of the eventual combined qualification unit:
  Mathlib.MeasureTheory.Integral.Prod
  Mathlib.Analysis.PSeries
  Mathlib.Analysis.Normed.Ring.InfiniteSum
  Mathlib.Topology.Algebra.InfiniteSum.Ring
  Mathlib.Topology.Algebra.InfiniteSum.Constructions
No radial iteratedFDeriv bound is used: only actual (0,0),(2,0),(0,2),(2,2).
The physical joint G is unchanged. Period64 replaces period24 only as the
fixed separation basis; G is supported in [-8,4]^2, inside [-16,16]^2.
-/
noncomputable section
open Set MeasureTheory Complex
open scoped Interval BigOperators

namespace P3TwoLogMixed22SourceOnly
open P3CompactCoordinateSourceOnly

local instance period_pos : Fact (0 < (32 : ℝ) - (-32)) := ⟨by norm_num⟩

def basis (n : ℤ) (x : ℝ) : ℂ :=
  fourier n (x : AddCircle ((32 : ℝ) - (-32)))

def C2 (G : ℝ → ℝ → ℂ) (m n : ℤ) : ℂ :=
  coeff64 (fun x => coeff64 (G x) n) m

def dx2 (G : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  iteratedDeriv 2 (fun z => G z y) x

def dy2 (G : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ := iteratedDeriv 2 (G x) y

/-- Regularity facts about ACTUAL partial derivatives, not independent jets. -/
structure MixedC2 (G : ℝ → ℝ → ℂ) : Prop where
  joint : Continuous (Function.uncurry G)
  in_x : ∀ y, ContDiff ℝ 2 (fun x => G x y)
  in_y : ∀ x, ContDiff ℝ 2 (G x)
  joint20 : Continuous (Function.uncurry (dx2 G))
  in_y20 : ∀ x, ContDiff ℝ 2 (dx2 G x)

/-- True support geometry; the actual rho(eta)rho(v) symbol has this property. -/
def InBox (G : ℝ → ℝ → ℂ) : Prop :=
  Function.support (Function.uncurry G) ⊆
    Icc (-16 : ℝ) 16 ×ˢ Icc (-16 : ℝ) 16

structure MixedBounds (G : ℝ → ℝ → ℂ) (M : ℝ) : Prop where
  b00 : ∀ x ∈ Icc (-32 : ℝ) 32, ∀ y ∈ Icc (-32 : ℝ) 32, ‖G x y‖ ≤ M
  b20 : ∀ x ∈ Icc (-32 : ℝ) 32, ∀ y ∈ Icc (-32 : ℝ) 32, ‖dx2 G x y‖ ≤ M
  b02 : ∀ x ∈ Icc (-32 : ℝ) 32, ∀ y ∈ Icc (-32 : ℝ) 32, ‖dy2 G x y‖ ≤ M
  b22 : ∀ x ∈ Icc (-32 : ℝ) 32, ∀ y ∈ Icc (-32 : ℝ) 32, ‖dy2 (dx2 G) x y‖ ≤ M

lemma zero_off_x {G : ℝ → ℝ → ℂ} (hs : InBox G) {x y : ℝ}
    (hx : x ∉ Icc (-16 : ℝ) 16) : G x y = 0 := by
  by_contra hn
  exact hx (hs (show (x, y) ∈ Function.support (Function.uncurry G) from hn)).1

lemma zero_off_y {G : ℝ → ℝ → ℂ} (hs : InBox G) {x y : ℝ}
    (hy : y ∉ Icc (-16 : ℝ) 16) : G x y = 0 := by
  by_contra hn
  exact hy (hs (show (x, y) ∈ Function.support (Function.uncurry G) from hn)).2

lemma x_tsupport16 {G : ℝ → ℝ → ℂ} (hs : InBox G) (y : ℝ) :
    tsupport (fun x => G x y) ⊆ Icc (-16 : ℝ) 16 := by
  change closure (Function.support (fun x => G x y)) ⊆ _
  exact closure_minimal (fun x hx => (hs (show (x, y) ∈ Function.support (Function.uncurry G) from hx)).1) isClosed_Icc

lemma y_tsupport16 {G : ℝ → ℝ → ℂ} (hs : InBox G) (x : ℝ) :
    tsupport (G x) ⊆ Icc (-16 : ℝ) 16 := by
  change closure (Function.support (G x)) ⊆ _
  exact closure_minimal (fun y hy => (hs (show (x, y) ∈ Function.support (Function.uncurry G) from hy)).2) isClosed_Icc

lemma box16_inside64 : Icc (-16 : ℝ) 16 ⊆ Ioo (-32 : ℝ) 32 := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma dx2_inBox {G : ℝ → ℝ → ℂ} (hs : InBox G) : InBox (dx2 G) := by
  intro p hp
  constructor
  · exact x_tsupport16 hs p.2
      (jet_tsupport_subset (fun x => G x p.2) 2 (subset_tsupport _ hp))
  · by_contra hy
    apply hp
    have he : (fun x => G x p.2) = (fun _ => (0 : ℂ)) :=
      funext (fun x => zero_off_y hs hy)
    change iteratedDeriv 2 (fun x => G x p.2) p.1 = 0
    rw [he]
    simp

lemma coeff64_const_mul (f : ℝ → ℂ) (z : ℂ) (n : ℤ) :
    coeff64 (fun x => z * f x) n = z * coeff64 f n := by
  unfold coeff64
  exact fourierCoeffOn.const_mul _ _ _ _

lemma coeff64_zero (n : ℤ) : coeff64 (fun _ => (0 : ℂ)) n = 0 := by
  simp [coeff64, fourierCoeffOn_eq_integral]

lemma coeff64_integral (f : ℝ → ℂ) (n : ℤ) :
    coeff64 f n = (1 / 64 : ℂ) *
      ∫ x in (-32 : ℝ)..32, basis (-n) x * f x := by
  rw [coeff64, fourierCoeffOn_eq_integral]
  change (1 / ((32 : ℝ) - (-32))) •
      (∫ x in (-32 : ℝ)..32, basis (-n) x • f x) = _
  rw [show (1 / ((32 : ℝ) - (-32))) = 1 / 64 by norm_num]
  simp only [Complex.real_smul, smul_eq_mul]
  norm_num

lemma C2_integral (G : ℝ → ℝ → ℂ) (m n : ℤ) :
    C2 G m n = (1 / 64 : ℂ)^2 *
      ∫ x in (-32 : ℝ)..32, ∫ y in (-32 : ℝ)..32,
        basis (-m) x * (basis (-n) y * G x y) := by
  unfold C2
  rw [coeff64_integral]
  simp_rw [coeff64_integral]
  have hi (x : ℝ) :
      basis (-m) x * ((1 / 64 : ℂ) *
        ∫ y in (-32 : ℝ)..32, basis (-n) y * G x y) =
      (1 / 64 : ℂ) * ∫ y in (-32 : ℝ)..32,
        basis (-m) x * (basis (-n) y * G x y) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma basis_continuous (n : ℤ) : Continuous (basis n) :=
  (fourier n).continuous.comp (AddCircle.continuous_mk' _)

/-- Actual finite-box Fubini, proved from continuity/integrability. -/
lemma C2_swap (G : ℝ → ℝ → ℂ) (hG : Continuous (Function.uncurry G)) (m n : ℤ) :
    C2 G m n = C2 (fun y x => G x y) n m := by
  let F : ℝ → ℝ → ℂ := fun x y => basis (-m) x * (basis (-n) y * G x y)
  have hF : Continuous (Function.uncurry F) :=
    ((basis_continuous (-m)).comp continuous_fst).mul
      (((basis_continuous (-n)).comp continuous_snd).mul hG)
  have hIcc : IntegrableOn (Function.uncurry F)
      (Icc (-32 : ℝ) 32 ×ˢ Icc (-32 : ℝ) 32) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hF.continuousOn
  have hIoc : IntegrableOn (Function.uncurry F)
      (uIoc (-32 : ℝ) 32 ×ˢ uIoc (-32 : ℝ) 32) := by
    simp only [uIoc_of_le (show (-32 : ℝ) ≤ 32 by norm_num)]
    exact hIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [C2_integral, C2_integral]
  have hswap := intervalIntegral_intervalIntegral_swap hIoc
  change (1 / 64 : ℂ)^2 * (∫ x in (-32 : ℝ)..32, ∫ y in (-32 : ℝ)..32, F x y) = _
  rw [hswap]
  congr 1
  congr 1
  funext y
  congr 1
  funext x
  dsimp [F]
  ring

lemma C2_const_mul (G : ℝ → ℝ → ℂ) (z : ℂ) (m n : ℤ) :
    C2 (fun x y => z * G x y) m n = z * C2 G m n := by
  simp only [C2, coeff64_const_mul]

/-- Two IBPs in v only. Support/jet endpoints are generated, not assumed. -/
lemma C2_ibp_y (G : ℝ → ℝ → ℂ)
    (hy : ∀ x, ContDiff ℝ 2 (G x)) (hs : InBox G)
    (m n : ℤ) (hn : n ≠ 0) :
    C2 G m n = (ibpScale64 n)^2 * C2 (dy2 G) m n := by
  have he : (fun x => coeff64 (G x) n) =
      (fun x => (ibpScale64 n)^2 * coeff64 (dy2 G x) n) := by
    funext x
    exact coeff64_iterated_ibp (G x) 2 (hy x)
      ((y_tsupport16 hs x).trans box16_inside64) n hn
  unfold C2
  rw [he]
  exact coeff64_const_mul _ _ _

/-- Two IBPs in eta, using Fubini rather than differentiating unknown coefficients. -/
lemma C2_ibp_x (G : ℝ → ℝ → ℂ) (hG : Continuous (Function.uncurry G))
    (hx : ∀ y, ContDiff ℝ 2 (fun x => G x y))
    (h20 : Continuous (Function.uncurry (dx2 G))) (hs : InBox G)
    (m n : ℤ) (hm : m ≠ 0) :
    C2 G m n = (ibpScale64 m)^2 * C2 (dx2 G) m n := by
  have hswapbox : InBox (fun y x => G x y) := by
    intro p hp
    exact ⟨(hs (show (p.2, p.1) ∈ Function.support (Function.uncurry G) from hp)).2,
      (hs (show (p.2, p.1) ∈ Function.support (Function.uncurry G) from hp)).1⟩
  calc
    _ = C2 (fun y x => G x y) n m := C2_swap G hG m n
    _ = (ibpScale64 m)^2 * C2 (fun y x => dx2 G x y) n m :=
      C2_ibp_y (fun y x => G x y) hx hswapbox n m hm
    _ = _ := congrArg (fun z : ℂ => (ibpScale64 m)^2 * z)
      (C2_swap (dx2 G) h20 m n).symm

lemma norm_C2_le (G : ℝ → ℝ → ℂ) (m n : ℤ) (M : ℝ)
    (hb : ∀ x ∈ Icc (-32 : ℝ) 32, ∀ y ∈ Icc (-32 : ℝ) 32, ‖G x y‖ ≤ M) :
    ‖C2 G m n‖ ≤ M := by
  apply norm_coeff64_le _ m M
  intro x hx
  exact norm_coeff64_le (G x) n M (hb x hx)

def loss (n : ℤ) : ℝ :=
  if n = 0 then 1 else (64 / (2 * Real.pi * |(n : ℝ)|))^2

def fixedCost : ℝ := 4 * (1 + (64 / (2 * Real.pi))^2)

def decay (n : ℤ) : ℝ := 1 / (1 + |(n : ℝ)|)^2

lemma loss_nonneg (n : ℤ) : 0 ≤ loss n := by
  unfold loss
  split_ifs <;> positivity

lemma fixedCost_nonneg : 0 ≤ fixedCost := by unfold fixedCost; positivity

/-- The FOUR actual mixed norms are the only quantitative hypotheses. -/
theorem norm_C2_mixed_loss (G : ℝ → ℝ → ℂ) (hc : MixedC2 G) (hs : InBox G)
    (M : ℝ) (hM : 0 ≤ M) (hb : MixedBounds G M) (m n : ℤ) :
    ‖C2 G m n‖ ≤ loss m * loss n * M := by
  by_cases hm : m = 0
  · subst m
    by_cases hn : n = 0
    · subst n
      simpa only [loss, if_true, one_mul] using
        le_of_max_le_left (max_le (norm_C2_le G 0 0 M hb.b00) hM)
    · rw [C2_ibp_y G hc.in_y hs 0 n hn, norm_mul, norm_pow, norm_ibpScale64]
      simpa only [loss, if_true, if_neg hn, one_mul] using
        mul_le_mul_of_nonneg_left (norm_C2_le (dy2 G) 0 n M hb.b02)
          (sq_nonneg (64 / (2 * Real.pi * |(n : ℝ)|)))
  · by_cases hn : n = 0
    · subst n
      rw [C2_ibp_x G hc.joint hc.in_x hc.joint20 hs m 0 hm,
        norm_mul, norm_pow, norm_ibpScale64]
      simpa only [loss, if_neg hm, if_true, mul_one] using
        mul_le_mul_of_nonneg_left (norm_C2_le (dx2 G) m 0 M hb.b20)
          (sq_nonneg (64 / (2 * Real.pi * |(m : ℝ)|)))
    · rw [C2_ibp_x G hc.joint hc.in_x hc.joint20 hs m n hm,
        C2_ibp_y (dx2 G) hc.in_y20 (dx2_inBox hs) m n hn,
        norm_mul, norm_pow, norm_mul, norm_pow, norm_ibpScale64, norm_ibpScale64]
      simpa only [loss, if_neg hm, if_neg hn, mul_assoc] using
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_C2_le (dy2 (dx2 G)) m n M hb.b22)
            (sq_nonneg (64 / (2 * Real.pi * |(n : ℝ)|))))
          (sq_nonneg (64 / (2 * Real.pi * |(m : ℝ)|)))

lemma loss_weight (n : ℤ) : (1 + |(n : ℝ)|)^2 * loss n ≤ fixedCost := by
  by_cases hn : n = 0
  · subst n
    simp only [loss, if_true, Int.cast_zero, abs_zero, add_zero, one_pow, mul_one]
    unfold fixedCost
    nlinarith [sq_nonneg (64 / (2 * Real.pi))]
  · have hnat : (1 : ℕ) ≤ n.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn)
    have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← habs]; exact_mod_cast hnat
    have hpos : 0 < |(n : ℝ)| := by linarith
    have hw : (1 + |(n : ℝ)|)^2 ≤ (2 * |(n : ℝ)|)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [loss, if_neg hn]
    calc
      _ ≤ (2 * |(n : ℝ)|)^2 * (64 / (2 * Real.pi * |(n : ℝ)|))^2 :=
        mul_le_mul_of_nonneg_right hw (by positivity)
      _ = 4 * (64 / (2 * Real.pi))^2 := by
        field_simp [hpos.ne', Real.pi_ne_zero]; ring
      _ ≤ fixedCost := by unfold fixedCost; linarith

theorem C2_product_weight_bound (G : ℝ → ℝ → ℂ) (hc : MixedC2 G) (hs : InBox G)
    (M : ℝ) (hM : 0 ≤ M) (hb : MixedBounds G M) (m n : ℤ) :
    (1 + |(m : ℝ)|)^2 * (1 + |(n : ℝ)|)^2 * ‖C2 G m n‖ ≤ fixedCost^2 * M := by
  calc
    _ ≤ (1 + |(m : ℝ)|)^2 * (1 + |(n : ℝ)|)^2 * (loss m * loss n * M) :=
      mul_le_mul_of_nonneg_left (norm_C2_mixed_loss G hc hs M hM hb m n) (by positivity)
    _ = ((1 + |(m : ℝ)|)^2 * loss m) * ((1 + |(n : ℝ)|)^2 * loss n) * M := by ring
    _ ≤ fixedCost * fixedCost * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (loss_weight m) (loss_weight n)
          (mul_nonneg (by positivity) (loss_nonneg n)) fixedCost_nonneg) hM
    _ = _ := by ring

theorem C2_product_decay (G : ℝ → ℝ → ℂ) (hc : MixedC2 G) (hs : InBox G)
    (M : ℝ) (hM : 0 ≤ M) (hb : MixedBounds G M) (m n : ℤ) :
    ‖C2 G m n‖ ≤ (fixedCost^2 * M) * decay m * decay n := by
  have hw := C2_product_weight_bound G hc hs M hM hb m n
  have hm0 : 0 < (1 + |(m : ℝ)|)^2 := by positivity
  have hn0 : 0 < (1 + |(n : ℝ)|)^2 := by positivity
  calc
    _ ≤ (fixedCost^2 * M) / ((1 + |(m : ℝ)|)^2 * (1 + |(n : ℝ)|)^2) :=
      (le_div_iff₀ (mul_pos hm0 hn0)).mpr (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hw)
    _ = _ := by unfold decay; field_simp [hm0.ne', hn0.ne']

lemma summable_decay : Summable decay := by
  have hnat : Summable (fun n : ℕ => 1 / (1 + (n : ℝ))^2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (2 : ℝ)).2 (by norm_num)
    apply h.congr
    intro n
    rw [abs_of_nonneg (by positivity), Real.rpow_two]
    simp only [add_comm]
  apply Summable.of_nat_of_neg
  · convert! hnat using 1
    funext n
    simp only [decay, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  · convert! hnat using 1
    funext n
    simp only [decay, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

def seriesCost : ℝ := (∑' n : ℤ, decay n)^2

/-- Absolute l1 is an OUTPUT of actual mixed derivative bounds. -/
theorem C2_l1 (G : ℝ → ℝ → ℂ) (hc : MixedC2 G) (hs : InBox G)
    (M : ℝ) (hM : 0 ≤ M) (hb : MixedBounds G M) :
    Summable (fun p : ℤ × ℤ => ‖C2 G p.1 p.2‖) ∧
      (∑' p : ℤ × ℤ, ‖C2 G p.1 p.2‖) ≤ fixedCost^2 * M * seriesCost := by
  have hdec := summable_decay
  have hprod : Summable (fun p : ℤ × ℤ => decay p.1 * decay p.2) :=
    hdec.mul_of_nonneg hdec (fun n => by unfold decay; positivity)
      (fun n => by unfold decay; positivity)
  have hmajor := hprod.mul_left (fixedCost^2 * M)
  have hbound (p : ℤ × ℤ) : ‖C2 G p.1 p.2‖ ≤
      (fixedCost^2 * M) * (decay p.1 * decay p.2) := by
    simpa only [mul_assoc] using C2_product_decay G hc hs M hM hb p.1 p.2
  have habs := hmajor.of_nonneg_of_le (fun p => norm_nonneg _) hbound
  refine ⟨habs, (hasSum_le hbound habs.hasSum hmajor.hasSum).trans_eq ?_⟩
  rw [hprod.tsum_mul_left, ← hdec.tsum_mul_tsum hdec hprod]
  unfold seriesCost
  ring

/-- The actual coefficient of the x-slice, as a function of its y parameter. -/
def coeffX (G : ℝ → ℝ → ℂ) (m : ℤ) (y : ℝ) : ℂ :=
  coeff64 (fun x => G x y) m

lemma coeffX_continuousOn (G : ℝ → ℝ → ℂ)
    (hG : Continuous (Function.uncurry G)) (m : ℤ) :
    ContinuousOn (coeffX G m) (Icc (-32 : ℝ) 32) := by
  let K : C(ℝ × Icc (-32 : ℝ) 32, ℂ) :=
    ⟨fun p => G p.1 p.2,
      hG.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun y : Icc (-32 : ℝ) 32 =>
    coeff64 (fun x => G x y) m)
  exact continuous_coeff64_other_slice K m

lemma coeffX_coeff (G : ℝ → ℝ → ℂ) (hG : Continuous (Function.uncurry G))
    (m n : ℤ) : coeff64 (coeffX G m) n = C2 G m n :=
  (C2_swap G hG m n).symm

lemma coeffX_endpoint (G : ℝ → ℝ → ℂ) (hs : InBox G) (m : ℤ) :
    coeffX G m (-32) = coeffX G m 32 := by
  have hleft : (fun x => G x (-32)) = (fun _ => (0 : ℂ)) :=
    funext (fun x => zero_off_y hs (by norm_num))
  have hright : (fun x => G x 32) = (fun _ => (0 : ℂ)) :=
    funext (fun x => zero_off_y hs (by norm_num))
  simp only [coeffX, hleft, hright]

/-- Actual continuous compact endpoint lift; native inversion is reused. -/
lemma hasSum_coeff64 (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc (-32 : ℝ) 32)) (he : f (-32) = f 32)
    (hs : Summable (coeff64 f)) (x : ℝ) (hx : x ∈ Ioc (-32 : ℝ) 32) :
    HasSum (fun n : ℤ => coeff64 f n * basis n x) (f x) := by
  let F : C(AddCircle ((32 : ℝ) - (-32)), ℂ) :=
    ⟨AddCircle.liftIoc ((32 : ℝ) - (-32)) (-32) f, by
      apply AddCircle.liftIoc_continuous
      · convert he using 1; norm_num
      · convert hf using 1; norm_num⟩
  have hcoef : fourierCoeff F = coeff64 f := rfl
  have hx' : x ∈ Ioc (-32 : ℝ) ((-32) + (32 - (-32))) := by
    convert hx using 1; norm_num
  have heval : F (x : AddCircle ((32 : ℝ) - (-32))) = f x :=
    AddCircle.liftIoc_coe_apply hx'
  have hnative := has_pointwise_sum_fourier_series_of_summable
    (f := F) (by simpa only [hcoef] using hs)
    (x : AddCircle ((32 : ℝ) - (-32)))
  simpa only [hcoef, heval, basis, smul_eq_mul] using hnative

lemma norm_basis (n : ℤ) (x : ℝ) : ‖basis n x‖ = 1 := Circle.norm_coe _

/-- Direct reconstruction of the SAME real G, not an abstract free coefficient family.
Both coordinate values are inside the actual period cell; in particular this
covers the complete physical eta,v range. Only the already proved mixed22 l1
output is used. No derivative of order3 or4 in one coordinate is introduced. -/
theorem C2_hasSum (G : ℝ → ℝ → ℂ) (hc : MixedC2 G) (hs : InBox G)
    (M : ℝ) (hM : 0 ≤ M) (hb : MixedBounds G M)
    (x y : ℝ) (hx : x ∈ Ioc (-32 : ℝ) 32) (hy : y ∈ Ioc (-32 : ℝ) 32) :
    HasSum (fun p : ℤ × ℤ => C2 G p.1 p.2 * basis p.1 x * basis p.2 y) (G x y) := by
  have hnorm := (C2_l1 G hc hs M hM hb).1
  have hC : Summable (fun p : ℤ × ℤ => C2 G p.1 p.2) :=
    hnorm.of_norm_bounded (fun p => le_rfl)
  have hm (m : ℤ) : Summable (coeff64 (coeffX G m)) := by
    have h := hC.prod_factor m
    simpa only [← coeffX_coeff G hc.joint] using h
  have hinner (m : ℤ) :
      HasSum (fun n : ℤ => C2 G m n * basis n y) (coeffX G m y) := by
    simpa only [coeffX_coeff G hc.joint] using
      hasSum_coeff64 (coeffX G m) (coeffX_continuousOn G hc.joint m)
        (coeffX_endpoint G hs m) (hm m) y hy
  have hinnerSeries : Summable (fun p : ℤ × ℤ => C2 G p.1 p.2 * basis p.2 y) :=
    hnorm.of_norm_bounded (fun p => by
      simp only [norm_mul, norm_basis, mul_one]
      exact le_rfl)
  have hsliced : Summable (fun m : ℤ => coeffX G m y) :=
    hinnerSeries.prod.congr (fun m => (hinner m).tsum_eq)
  have hsliceEndpoint : G (-32) y = G 32 y := by
    rw [zero_off_x hs (by norm_num), zero_off_x hs (by norm_num)]
  have houter : HasSum (fun m : ℤ => coeffX G m y * basis m x) (G x y) := by
    exact hasSum_coeff64 (fun z => G z y) (hc.in_x y).continuous.continuousOn
      hsliceEndpoint hsliced x hx
  have hseries : Summable
      (fun p : ℤ × ℤ => C2 G p.1 p.2 * basis p.1 x * basis p.2 y) :=
    hnorm.of_norm_bounded (fun p => by
      simp only [norm_mul, norm_basis, mul_one]
      exact le_rfl)
  have hinner' (m : ℤ) :
      HasSum (fun n : ℤ => C2 G m n * basis m x * basis n y)
        (coeffX G m y * basis m x) := by
    convert! (hinner m).mul_right (basis m x) using 1
    funext n
    ring
  have hsum : (∑' p : ℤ × ℤ, C2 G p.1 p.2 * basis p.1 x * basis p.2 y) = G x y := by
    rw [hseries.tsum_prod]
    simp_rw [(hinner' _).tsum_eq]
    exact houter.tsum_eq
  simpa only [hsum] using hseries.hasSum

/-- The complete local output, with no coefficient-decay or l1 premise. -/
theorem compact_joint_symbol_supplier
    (G : ℝ → ℝ → ℂ) (hc : MixedC2 G) (hs : InBox G)
    (M : ℝ) (hM : 0 ≤ M) (hb : MixedBounds G M) :
    (∀ m n : ℤ, ‖C2 G m n‖ ≤ (fixedCost^2 * M) * decay m * decay n) ∧
      Summable (fun p : ℤ × ℤ => ‖C2 G p.1 p.2‖) ∧
      ((∑' p : ℤ × ℤ, ‖C2 G p.1 p.2‖) ≤ fixedCost^2 * M * seriesCost) ∧
      (∀ x y : ℝ, x ∈ Ioc (-32 : ℝ) 32 → y ∈ Ioc (-32 : ℝ) 32 →
        HasSum (fun p : ℤ × ℤ => C2 G p.1 p.2 * basis p.1 x * basis p.2 y) (G x y)) := by
  obtain ⟨hl1, hbudget⟩ := C2_l1 G hc hs M hM hb
  exact ⟨C2_product_decay G hc hs M hM hb, hl1, hbudget,
    fun x y hx hy => C2_hasSum G hc hs M hM hb x y hx hy⟩
end P3TwoLogMixed22SourceOnly
end

/-!
SOURCEONLY / UNCOMPILED / HOLD.
Actual U*V, N1-window and moving-residue facts for the retained WHOLE slow phase.
The joint two-log-variable Fourier symbol is proved mathematically in its
companion report; its C^2/summability formal supplier is NOT asserted here.
-/
namespace ImbalancedChen.Part3.GeneralDSlowPhaseParametersSourceOnly
noncomputable section
open Classical Finset

/-- Atom-dependent but outer-label-independent signed phase parameter. -/
def movingRatio (d : MediumAtom) : ℝ := (d.residue : ℝ) / d.scale

theorem actual_transposed_N1_window
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {N1 : ℕ}
    (hN1 : N1 ∈ d.transposedAtom.betaCarrier) :
    d.U ≤ (N1 : ℝ) ∧ (N1 : ℝ) ≤ 2 * d.U := by
  change N1 ∈ factorCarrier d.U at hN1
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hN1
  constructor
  · exact (Nat.le_ceil d.U).trans (by exact_mod_cast hlo)
  · exact (show (N1 : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith [hd.1] : 0 ≤ 2 * d.U))

theorem actual_movingRatio_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    |movingRatio d| ≤ d.scale ^ kappa := by
  obtain ⟨hU, hV, hQ, hS, hR, hlarge, halower, haup, hrest⟩ := hd
  have hx : 0 < d.scale := by
    dsimp [MediumAtom.scale]
    exact mul_pos (by linarith) (by linarith)
  have habs : (d.residue.natAbs : ℝ) = |(d.residue : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [habs] at haup
  have hp : d.scale ^ (1 + kappa) = d.scale * d.scale ^ kappa := by
    rw [Real.rpow_add hx, Real.rpow_one]
  rw [hp] at haup
  unfold movingRatio
  rw [abs_div, abs_of_pos hx]
  exact (div_le_iff₀ hx).mpr (by simpa only [mul_comm] using haup)

/-- Actual N1>=U makes the original row's local phase ratio no larger. -/
theorem actual_local_slow_ratio_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {N1 : ℕ}
    (hN1 : N1 ∈ d.transposedAtom.betaCarrier) :
    |(d.residue : ℝ) / ((N1 : ℝ) * d.V)| ≤ d.scale ^ kappa := by
  have hN := (actual_transposed_N1_window hd hN1).1
  have hM : 0 < d.V := by linarith [hd.2.1]
  have hN0 : 0 < (N1 : ℝ) := by linarith [hd.1]
  have hx : 0 < d.scale := by
    dsimp [MediumAtom.scale]
    exact mul_pos (by linarith [hd.1]) hM
  have hden : d.scale ≤ (N1 : ℝ) * d.V := by
    exact mul_le_mul_of_nonneg_right hN hM.le
  rw [abs_div, abs_of_pos (mul_pos hN0 hM)]
  calc
    _ ≤ |(d.residue : ℝ)| / d.scale :=
      div_le_div_of_nonneg_left (abs_nonneg _) hx hden
    _ = |movingRatio d| := by rw [movingRatio, abs_div, abs_of_pos hx]
    _ ≤ _ := actual_movingRatio_bound hd

/-- Exact factorization with T=M/L; signs of a and h are unchanged. -/
theorem actual_slow_argument_eq_local
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {N1 L : ℕ}
    (hN1 : N1 ∈ d.transposedAtom.betaCarrier) (hL : 0 < L) (h : ℤ) :
    (d.residue : ℝ) * (h : ℝ) / ((N1 : ℝ) * (L : ℝ)) =
      ((d.residue : ℝ) / ((N1 : ℝ) * d.V)) *
        ((d.V / (L : ℝ)) * (h : ℝ)) := by
  have hN := (actual_transposed_N1_window hd hN1).1
  have hN0 : (N1 : ℝ) ≠ 0 := ne_of_gt (by linarith [hd.1])
  have hM0 : d.V ≠ 0 := ne_of_gt (by linarith [hd.2.1])
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  field_simp [hN0, hM0, hL0]

/-- The only new outer log coordinate is N1/U; movingRatio is COMMON. -/
theorem actual_slow_argument_eq_common_ratio
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {N1 L : ℕ}
    (hN1 : N1 ∈ d.transposedAtom.betaCarrier) (hL : 0 < L) (h : ℤ) :
    (d.residue : ℝ) * (h : ℝ) / ((N1 : ℝ) * (L : ℝ)) =
      movingRatio d * (d.U / (N1 : ℝ)) *
        ((d.V / (L : ℝ)) * (h : ℝ)) := by
  have hN := (actual_transposed_N1_window hd hN1).1
  have hN0 : (N1 : ℝ) ≠ 0 := ne_of_gt (by linarith [hd.1])
  have hU0 : d.U ≠ 0 := ne_of_gt (by linarith [hd.1])
  have hM0 : d.V ≠ 0 := ne_of_gt (by linarith [hd.2.1])
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  unfold movingRatio MediumAtom.scale
  field_simp [hN0, hU0, hM0, hL0]

/-- The mixed-C^2 symbol's fourth power fits the ORIGINAL five-kappa debit.
No second such charge is introduced by this algebraic lemma. -/
theorem actual_joint_symbol_debit_le_original_five
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hkappa : 0 ≤ kappa) :
    (1 + |movingRatio d|) ^ 4 ≤ 16 * d.scale ^ (5 * kappa) := by
  have hx1 : 1 ≤ d.scale := by
    dsimp [MediumAtom.scale]
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 (by norm_num) (by linarith [hd.1])
  have hp : 1 ≤ d.scale ^ kappa := Real.one_le_rpow hx1 hkappa
  have hq := actual_movingRatio_bound hd
  have hs : 1 + |movingRatio d| ≤ 2 * d.scale ^ kappa := by linarith
  calc
    _ ≤ (2 * d.scale ^ kappa) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hs 4
    _ = 16 * (d.scale ^ kappa) ^ 4 := by ring
    _ ≤ 16 * (d.scale ^ kappa) ^ 5 := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [pow_succ (d.scale ^ kappa) 4]
      exact le_mul_of_one_le_right (by positivity) hp
    _ = _ := by
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx1)]
      congr 1
      ring

end
end ImbalancedChen.Part3.GeneralDSlowPhaseParametersSourceOnly
/-!
SOURCEONLY / UNCOMPILED / HOLD -- 2026-10-23.
Load the frozen compact-coordinate source SHA933d9458 FIRST, followed by the
frozen two-log mixed22 source SHAb907e76, then this fragment. Move the imports
below to the head of the eventual combined qualification unit.
For actual_atom_doubleCoeff_l1 also load the frozen actual-parameter/debit
source SHAbf836248 before this fragment (no changes to that frozen source).

The actual symbol is rho(eta) rho(v) Phi(epsilon*lambda*exp v)
  chi(epsilon*lambda*exp v/Z) exp(2*pi*i*xi*epsilon*lambda*exp(v-eta)).
chi is literally poissonSmoothLowPass; Phi is literally the Fourier transform
of dyadicCutoffSchwartz. No target MixedBounds/derivative/l1 estimate is an
input of the actual instance. Quantitative derivatives are only G, dx2 G,
dy2 G, dy2(dx2 G); the phase polynomials have degree at most four.
No compilation, Lean/lake/typechecker/CI, or original source edit.
-/


noncomputable section
open Set MeasureTheory Complex
open scoped ContDiff SchwartzMap FourierTransform BigOperators Interval

namespace P3ActualJointGSourceOnly
open ImbalancedChen.Part3 ImbalancedChen.Part3.CommonSmoothCutoff
open P3CompactCoordinateSourceOnly P3TwoLogMixed22SourceOnly

/- The original low-pass facts have private visibility. Reprove them from the
same fixed bump; no arbitrary smooth cutoff is substituted. -/
lemma chi_contDiff : ContDiff ℝ ∞ poissonSmoothLowPass := by
  exact dyadicBump.contDiff.comp (contDiff_const.add (contDiff_id.div_const 2))

lemma chi_zero {u : ℝ} (hu : 2 ≤ |u|) : poissonSmoothLowPass u = 0 := by
  apply dyadicBump.zero_of_le_dist
  change (1 : ℝ) ≤ |(3 / 2 + u / 2) - 3 / 2|
  rw [show (3 / 2 + u / 2) - 3 / 2 = u / 2 by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)

lemma chi_nonzero {u : ℝ} (hu : poissonSmoothLowPass u ≠ 0) : |u| < 2 := by
  by_contra h
  exact hu (chi_zero (le_of_not_gt h))

lemma chi_one {u : ℝ} (hu : |u| ≤ 1) : poissonSmoothLowPass u = 1 := by
  apply dyadicBump.one_of_mem_closedBall
  change |(3 / 2 + u / 2) - 3 / 2| ≤ 1 / 2
  rw [abs_le] at hu ⊢
  constructor <;> linarith [hu.1, hu.2]

lemma chi_tsupport : tsupport poissonSmoothLowPass ⊆ Icc (-2 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have h := chi_nonzero hu
  exact ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

lemma chi_compact : HasCompactSupport poissonSmoothLowPass :=
  isCompact_Icc.of_isClosed_subset isClosed_closure chi_tsupport

def chiS : 𝓢(ℝ, ℂ) :=
  (chi_compact.comp_left (g := Complex.ofRealCLM) (map_zero _)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp chi_contDiff)

@[simp] lemma chiS_apply (u : ℝ) : chiS u = (poissonSmoothLowPass u : ℂ) := rfl

def rhoReal (v : ℝ) : ℝ := poissonSmoothLowPass ((v + 2) / 3)

lemma rhoReal_contDiff : ContDiff ℝ ∞ rhoReal :=
  chi_contDiff.comp ((contDiff_id.add contDiff_const).div_const 3)

lemma rhoReal_nonzero {v : ℝ} (hv : rhoReal v ≠ 0) : v ∈ Icc (-8 : ℝ) 4 := by
  have h := abs_lt.mp (chi_nonzero hv)
  constructor <;> linarith [h.1, h.2]

lemma rhoReal_tsupport : tsupport rhoReal ⊆ Icc (-8 : ℝ) 4 := by
  exact closure_minimal (fun _ h => rhoReal_nonzero h) isClosed_Icc

lemma rhoReal_compact : HasCompactSupport rhoReal :=
  isCompact_Icc.of_isClosed_subset isClosed_closure rhoReal_tsupport

def rhoS : 𝓢(ℝ, ℂ) :=
  (rhoReal_compact.comp_left (g := Complex.ofRealCLM) (map_zero _)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp rhoReal_contDiff)

@[simp] lemma rhoS_apply (v : ℝ) : rhoS v = (rhoReal v : ℂ) := rfl

lemma rho_one {v : ℝ} (hv : v ∈ Icc (-5 : ℝ) 1) : rhoS v = 1 := by
  have h : |(v + 2) / 3| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hv.1, hv.2]
  simp only [rhoS_apply, rhoReal, chi_one h, Complex.ofReal_one]

lemma rho_tsupport : tsupport (rhoS : ℝ → ℂ) ⊆ Icc (-8 : ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply rhoReal_nonzero
  intro hz
  apply hv
  simp only [rhoS_apply, hz, Complex.ofReal_zero]

def rhoJ (j : ℕ) (v : ℝ) : ℂ := iteratedDeriv j rhoS v
def Phi : 𝓢(ℝ, ℂ) := 𝓕 dyadicCutoffSchwartz

lemma smooth_jet (f : 𝓢(ℝ, ℂ)) (j : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv j f) := by
  simpa only [iteratedDeriv_eq_iterate] using! ContDiff.iterate_deriv j f.smooth'

lemma jet_hasDerivAt (f : 𝓢(ℝ, ℂ)) (j : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
  simpa only [iteratedDeriv_succ] using!
    ((smooth_jet f j).differentiable (by simp) x).hasDerivAt

lemma rhoJ_zero_off (j : ℕ) {v : ℝ} (hv : v ∉ Icc (-8 : ℝ) 4) : rhoJ j v = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hv (rho_tsupport (jet_tsupport_subset (rhoS : ℝ → ℂ) j h))

/- Each constant is constructed from finitely many actual Schwartz seminorms.
The two scalar weights of Phi have derivative order exactly j, never a radial
fourth-order norm of G. -/
def cost3 (p : ℕ → ℝ) : ℝ := 1 + ∑ j ∈ Finset.range 3, |p j|

lemma cost3_one (p : ℕ → ℝ) : 1 ≤ cost3 p := by
  have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range 3) => abs_nonneg (p j))
  dsimp [cost3]
  linarith

lemma cost3_le (p : ℕ → ℝ) {j : ℕ} (hj : j ≤ 2) : p j ≤ cost3 p := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.range 3) => abs_nonneg (p i))
    (Finset.mem_range.mpr (by omega : j < 3))
  exact (le_abs_self _).trans (h.trans (by dsimp [cost3]; linarith))

def weightedJetCost (f : 𝓢(ℝ, ℂ)) (b j : ℕ) : ℝ :=
  2 ^ b * (|SchwartzMap.seminorm ℝ j j f| + |SchwartzMap.seminorm ℝ (b + j) j f|)

lemma weighted_jet_from_actual_seminorm (f : 𝓢(ℝ, ℂ)) (b j : ℕ) (x : ℝ) :
    (1 + |x|) ^ b * (|x| ^ j * ‖iteratedDeriv j f x‖) ≤ weightedJetCost f b j := by
  have h0 := (SchwartzMap.le_seminorm' ℝ j j f x).trans (le_abs_self _)
  have h1 := (SchwartzMap.le_seminorm' ℝ (b + j) j f x).trans (le_abs_self _)
  by_cases hx : |x| ≤ 1
  · have hp : (1 + |x|) ^ b ≤ (2 : ℝ) ^ b :=
      pow_le_pow_left₀ (by positivity) (by linarith) b
    calc
      _ ≤ 2 ^ b * (|x| ^ j * ‖iteratedDeriv j f x‖) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ 2 ^ b * |SchwartzMap.seminorm ℝ j j f| :=
        mul_le_mul_of_nonneg_left h0 (by positivity)
      _ ≤ weightedJetCost f b j := by
        unfold weightedJetCost
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _))
          (by positivity)
  · have hp : (1 + |x|) ^ b ≤ (2 : ℝ) ^ b * |x| ^ b := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith [le_of_not_ge hx]) b
    calc
      _ ≤ (2 ^ b * |x| ^ b) * (|x| ^ j * ‖iteratedDeriv j f x‖) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = 2 ^ b * (|x| ^ (b + j) * ‖iteratedDeriv j f x‖) := by rw [pow_add]; ring
      _ ≤ 2 ^ b * |SchwartzMap.seminorm ℝ (b + j) j f| :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ weightedJetCost f b j := by
        unfold weightedJetCost
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _))
          (by positivity)

def rhoCost : ℝ := cost3 (fun j => SchwartzMap.seminorm ℝ 0 j rhoS)
def chiCost : ℝ := cost3 (fun j => SchwartzMap.seminorm ℝ j j chiS)
def phiCost (b : ℕ) : ℝ := cost3 (weightedJetCost Phi b)

lemma rhoCost_one : 1 ≤ rhoCost := cost3_one _
lemma chiCost_one : 1 ≤ chiCost := cost3_one _
lemma phiCost_one (b : ℕ) : 1 ≤ phiCost b := cost3_one _

lemma rhoJ_bound {j : ℕ} (hj : j ≤ 2) (v : ℝ) : ‖rhoJ j v‖ ≤ rhoCost := by
  have hjet : ‖rhoJ j v‖ ≤ SchwartzMap.seminorm ℝ 0 j rhoS := by
    simpa only [rhoJ, pow_zero, one_mul] using! SchwartzMap.le_seminorm' ℝ 0 j rhoS v
  exact hjet.trans (cost3_le (fun i => SchwartzMap.seminorm ℝ 0 i rhoS) hj)

def eulerJet (f : 𝓢(ℝ, ℂ)) (j : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ j * iteratedDeriv j f u

lemma eulerJet_norm (f : 𝓢(ℝ, ℂ)) (j : ℕ) (u : ℝ) :
    ‖eulerJet f j u‖ = |u| ^ j * ‖iteratedDeriv j f u‖ := by
  simp only [eulerJet, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

lemma chi_euler_bound {j : ℕ} (hj : j ≤ 2) (r : ℝ) : ‖eulerJet chiS j r‖ ≤ chiCost := by
  rw [eulerJet_norm]
  exact (SchwartzMap.le_seminorm' ℝ j j chiS r).trans
    (cost3_le (fun i => SchwartzMap.seminorm ℝ i i chiS) hj)

lemma phi_euler_weighted (b : ℕ) {j : ℕ} (hj : j ≤ 2) (u : ℝ) :
    (1 + |u|) ^ b * ‖eulerJet Phi j u‖ ≤ phiCost b := by
  rw [eulerJet_norm]
  exact (weighted_jet_from_actual_seminorm Phi b j u).trans
    (cost3_le (weightedJetCost Phi b) hj)

def xval (epsilon lambda v : ℝ) : ℝ := epsilon * lambda * Real.exp v

lemma xval_hasDerivAt (epsilon lambda v : ℝ) :
    HasDerivAt (xval epsilon lambda) (xval epsilon lambda v) v := by
  exact (Real.hasDerivAt_exp v).const_mul (epsilon * lambda)

lemma ratio_hasDerivAt (epsilon lambda Z v : ℝ) :
    HasDerivAt (fun t => xval epsilon lambda t / Z) (xval epsilon lambda v / Z) v :=
  (xval_hasDerivAt epsilon lambda v).div_const Z

lemma euler0_hasDerivAt (f : 𝓢(ℝ, ℂ)) {u : ℝ → ℝ} {v : ℝ}
    (hu : HasDerivAt u (u v) v) :
    HasDerivAt (fun t => eulerJet f 0 (u t)) (eulerJet f 1 (u v)) v := by
  simpa only [eulerJet, iteratedDeriv_zero, pow_zero, pow_one, one_mul,
    Complex.real_smul] using! (jet_hasDerivAt f 0 (u v)).scomp v hu

lemma euler1_hasDerivAt (f : 𝓢(ℝ, ℂ)) {u : ℝ → ℝ} {v : ℝ}
    (hu : HasDerivAt u (u v) v) :
    HasDerivAt (fun t => eulerJet f 1 (u t))
      (eulerJet f 1 (u v) + eulerJet f 2 (u v)) v := by
  have hf := (jet_hasDerivAt f 1 (u v)).scomp v hu
  simpa only [eulerJet, pow_one, pow_two, Function.comp_apply,
    Complex.real_smul, mul_assoc] using! hu.ofReal_comp.mul hf

def rawAmp (epsilon lambda Z : ℝ) (v : ℝ) : ℂ :=
  Phi (xval epsilon lambda v) * chiS (xval epsilon lambda v / Z)

def rawAmp1 (epsilon lambda Z : ℝ) (v : ℝ) : ℂ :=
  eulerJet Phi 1 (xval epsilon lambda v) * eulerJet chiS 0 (xval epsilon lambda v / Z) +
  eulerJet Phi 0 (xval epsilon lambda v) * eulerJet chiS 1 (xval epsilon lambda v / Z)

def rawAmp2 (epsilon lambda Z : ℝ) (v : ℝ) : ℂ :=
  (eulerJet Phi 1 (xval epsilon lambda v) + eulerJet Phi 2 (xval epsilon lambda v)) *
      eulerJet chiS 0 (xval epsilon lambda v / Z) +
    2 * eulerJet Phi 1 (xval epsilon lambda v) * eulerJet chiS 1 (xval epsilon lambda v / Z) +
    eulerJet Phi 0 (xval epsilon lambda v) *
      (eulerJet chiS 1 (xval epsilon lambda v / Z) + eulerJet chiS 2 (xval epsilon lambda v / Z))

lemma rawAmp_hasDerivAt (epsilon lambda Z v : ℝ) :
    HasDerivAt (rawAmp epsilon lambda Z) (rawAmp1 epsilon lambda Z v) v := by
  simpa only [rawAmp, rawAmp1, eulerJet, pow_zero, one_mul, iteratedDeriv_zero] using!
    (euler0_hasDerivAt Phi (xval_hasDerivAt epsilon lambda v)).mul
      (euler0_hasDerivAt chiS (ratio_hasDerivAt epsilon lambda Z v))

lemma rawAmp1_hasDerivAt (epsilon lambda Z v : ℝ) :
    HasDerivAt (rawAmp1 epsilon lambda Z) (rawAmp2 epsilon lambda Z v) v := by
  have hp0 := euler0_hasDerivAt Phi (xval_hasDerivAt epsilon lambda v)
  have hp1 := euler1_hasDerivAt Phi (xval_hasDerivAt epsilon lambda v)
  have hc0 := euler0_hasDerivAt chiS (ratio_hasDerivAt epsilon lambda Z v)
  have hc1 := euler1_hasDerivAt chiS (ratio_hasDerivAt epsilon lambda Z v)
  convert! (hp1.mul hc0).add (hp0.mul hc1) using 1
  unfold rawAmp2
  ring

def amp (epsilon lambda Z : ℝ) (v : ℝ) : ℂ := rhoS v * rawAmp epsilon lambda Z v
def amp1 (epsilon lambda Z : ℝ) (v : ℝ) : ℂ :=
  rhoJ 1 v * rawAmp epsilon lambda Z v + rhoS v * rawAmp1 epsilon lambda Z v
def amp2 (epsilon lambda Z : ℝ) (v : ℝ) : ℂ :=
  rhoJ 2 v * rawAmp epsilon lambda Z v +
    2 * rhoJ 1 v * rawAmp1 epsilon lambda Z v + rhoS v * rawAmp2 epsilon lambda Z v

lemma amp_hasDerivAt (epsilon lambda Z v : ℝ) :
    HasDerivAt (amp epsilon lambda Z) (amp1 epsilon lambda Z v) v := by
  have hr0 := jet_hasDerivAt rhoS 0 v
  rw [iteratedDeriv_zero] at hr0
  simpa only [amp, amp1, rhoJ] using! hr0.mul (rawAmp_hasDerivAt epsilon lambda Z v)

lemma amp1_hasDerivAt (epsilon lambda Z v : ℝ) :
    HasDerivAt (amp1 epsilon lambda Z) (amp2 epsilon lambda Z v) v := by
  have hr0 := jet_hasDerivAt rhoS 0 v
  have hr1 := jet_hasDerivAt rhoS 1 v
  have ha0 := rawAmp_hasDerivAt epsilon lambda Z v
  have ha1 := rawAmp1_hasDerivAt epsilon lambda Z v
  rw [iteratedDeriv_zero] at hr0
  convert! (hr1.mul ha0).add (hr0.mul ha1) using 1
  unfold amp2 rhoJ
  ring

lemma second_of_jets {f f1 f2 : ℝ → ℂ}
    (h0 : ∀ v, HasDerivAt f (f1 v) v) (h1 : ∀ v, HasDerivAt f1 (f2 v) v) (v : ℝ) :
    iteratedDeriv 2 f v = f2 v := by
  have he : deriv f = f1 := funext (fun t => (h0 t).deriv)
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, he]
  exact (h1 v).deriv

lemma amp2_actual (epsilon lambda Z v : ℝ) :
    iteratedDeriv 2 (amp epsilon lambda Z) v = amp2 epsilon lambda Z v :=
  second_of_jets (amp_hasDerivAt epsilon lambda Z) (amp1_hasDerivAt epsilon lambda Z) v

lemma amp_contDiff (epsilon lambda Z : ℝ) : ContDiff ℝ ∞ (amp epsilon lambda Z) := by
  unfold amp rawAmp xval
  exact rhoS.smooth'.mul ((Phi.smooth'.comp (contDiff_const.mul Real.contDiff_exp)).mul
    (chiS.smooth'.comp ((contDiff_const.mul Real.contDiff_exp).div_const Z)))

/- Two finite algebra estimates, later applied only with the actual jets. -/
def firstProduct (f0 f1 g0 g1 : ℂ) : ℂ := f1 * g0 + f0 * g1
def secondProduct (f0 f1 f2 g0 g1 g2 : ℂ) : ℂ :=
  f2 * g0 + 2 * (f1 * g1) + f0 * g2

lemma norm_product_bound {f g : ℂ} {F G : ℝ} (hf : ‖f‖ ≤ F) (hg : ‖g‖ ≤ G) :
    ‖f * g‖ ≤ F * G := by
  rw [norm_mul]
  exact mul_le_mul hf hg (norm_nonneg _) ((norm_nonneg _).trans hf)

lemma norm_firstProduct_bound {f0 f1 g0 g1 : ℂ} {F G : ℝ}
    (hf0 : ‖f0‖ ≤ F) (hf1 : ‖f1‖ ≤ F) (hg0 : ‖g0‖ ≤ G) (hg1 : ‖g1‖ ≤ G) :
    ‖firstProduct f0 f1 g0 g1‖ ≤ 2 * F * G := by
  exact (norm_add_le _ _).trans
    ((add_le_add (norm_product_bound hf1 hg0) (norm_product_bound hf0 hg1)).trans_eq (by ring))

lemma norm_secondProduct_bound {f0 f1 f2 g0 g1 g2 : ℂ} {F G : ℝ}
    (hf0 : ‖f0‖ ≤ F) (hf1 : ‖f1‖ ≤ F) (hf2 : ‖f2‖ ≤ F)
    (hg0 : ‖g0‖ ≤ G) (hg1 : ‖g1‖ ≤ G) (hg2 : ‖g2‖ ≤ G) :
    ‖secondProduct f0 f1 f2 g0 g1 g2‖ ≤ 4 * F * G := by
  have htwo : ‖(2 : ℂ) * (f1 * g1)‖ ≤ 2 * (F * G) := by
    calc
      ‖(2 : ℂ) * (f1 * g1)‖ = (2 : ℝ) * ‖f1 * g1‖ := by
        rw [norm_mul]
        norm_num
      _ ≤ 2 * (F * G) :=
        mul_le_mul_of_nonneg_left (norm_product_bound hf1 hg1) (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ (‖f2 * g0‖ + ‖(2 : ℂ) * (f1 * g1)‖) + ‖f0 * g2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (F * G + 2 * (F * G)) + F * G :=
      add_le_add (add_le_add (norm_product_bound hf2 hg0) htwo)
        (norm_product_bound hf0 hg2)
    _ = _ := by ring

lemma rawAmp_common_bound (s : ℕ) (epsilon lambda Z v : ℝ) :
    let p : ℝ := phiCost s / (1 + |xval epsilon lambda v|) ^ s
    ‖rawAmp epsilon lambda Z v‖ ≤ 16 * p * chiCost ∧
    ‖rawAmp1 epsilon lambda Z v‖ ≤ 16 * p * chiCost ∧
    ‖rawAmp2 epsilon lambda Z v‖ ≤ 16 * p * chiCost := by
  dsimp only
  let x := xval epsilon lambda v
  let r := x / Z
  let p := phiCost s / (1 + |x|) ^ s
  have hp : 0 ≤ p := div_nonneg (zero_le_one.trans (phiCost_one s)) (by positivity)
  have hc : 0 ≤ chiCost := zero_le_one.trans chiCost_one
  have hP (j : ℕ) (hj : j ≤ 2) : ‖eulerJet Phi j x‖ ≤ p := by
    exact (le_div_iff₀ (by positivity)).mpr (by
      simpa only [mul_comm] using phi_euler_weighted s hj x)
  have hC (j : ℕ) (hj : j ≤ 2) : ‖eulerJet chiS j r‖ ≤ chiCost := chi_euler_bound hj r
  have hraw0 : ‖rawAmp epsilon lambda Z v‖ ≤ p * chiCost := by
    simpa only [rawAmp, x, r, eulerJet, pow_zero, one_mul, iteratedDeriv_zero] using
      norm_product_bound (hP 0 (by omega)) (hC 0 (by omega))
  have hraw1 : ‖rawAmp1 epsilon lambda Z v‖ ≤ 2 * p * chiCost :=
    norm_firstProduct_bound (hP 0 (by omega)) (hP 1 (by omega))
      (hC 0 (by omega)) (hC 1 (by omega))
  have hP' (j : ℕ) (hj : j ≤ 2) : ‖eulerJet Phi j x‖ ≤ 2 * p :=
    (hP j hj).trans (by linarith)
  have hC' (j : ℕ) (hj : j ≤ 2) : ‖eulerJet chiS j r‖ ≤ 2 * chiCost :=
    (hC j hj).trans (by linarith)
  have hPs : ‖eulerJet Phi 1 x + eulerJet Phi 2 x‖ ≤ 2 * p :=
    (norm_add_le _ _).trans ((add_le_add (hP 1 (by omega)) (hP 2 (by omega))).trans_eq (by ring))
  have hCs : ‖eulerJet chiS 1 r + eulerJet chiS 2 r‖ ≤ 2 * chiCost :=
    (norm_add_le _ _).trans ((add_le_add (hC 1 (by omega)) (hC 2 (by omega))).trans_eq (by ring))
  have hraw2 : ‖rawAmp2 epsilon lambda Z v‖ ≤ 16 * p * chiCost := by
    have h := norm_secondProduct_bound (hP' 0 (by omega)) (hP' 1 (by omega)) hPs
      (hC' 0 (by omega)) (hC' 1 (by omega)) hCs
    have heq : rawAmp2 epsilon lambda Z v = secondProduct
        (eulerJet Phi 0 x) (eulerJet Phi 1 x) (eulerJet Phi 1 x + eulerJet Phi 2 x)
        (eulerJet chiS 0 r) (eulerJet chiS 1 r) (eulerJet chiS 1 r + eulerJet chiS 2 r) := by
      dsimp only [rawAmp2, secondProduct, x, r]
      ring
    rw [heq]
    exact h.trans_eq (by ring)
  refine ⟨hraw0.trans ?_, hraw1.trans ?_, hraw2⟩ <;> nlinarith [mul_nonneg hp hc]

def ampJ (j : ℕ) (epsilon lambda Z v : ℝ) : ℂ :=
  match j with
  | 0 => amp epsilon lambda Z v
  | 1 => amp1 epsilon lambda Z v
  | _ => amp2 epsilon lambda Z v

lemma ampJ_zero_off {v : ℝ} (hv : v ∉ Icc (-8 : ℝ) 4) (j : ℕ)
    (epsilon lambda Z : ℝ) : ampJ j epsilon lambda Z v = 0 := by
  have h0 : rhoS v = 0 := by simpa only [rhoJ, iteratedDeriv_zero] using rhoJ_zero_off 0 hv
  have h1 := rhoJ_zero_off 1 hv
  have h2 := rhoJ_zero_off 2 hv
  cases j with
  | zero => simp only [ampJ, amp, h0, zero_mul]
  | succ j => cases j with
    | zero => simp only [ampJ, amp1, h0, h1, zero_mul, add_zero]
    | succ j => simp only [ampJ, amp2, h0, h1, h2, zero_mul, mul_zero, add_zero]

lemma ampJ_common_bound (s : ℕ) {j : ℕ} (hj : j ≤ 2) (epsilon lambda Z v : ℝ) :
    ‖ampJ j epsilon lambda Z v‖ ≤
      64 * rhoCost * chiCost * phiCost s / (1 + |xval epsilon lambda v|) ^ s := by
  let p := phiCost s / (1 + |xval epsilon lambda v|) ^ s
  let q := 16 * p * chiCost
  have hp : 0 ≤ p := div_nonneg (zero_le_one.trans (phiCost_one s)) (by positivity)
  have hq : 0 ≤ q := mul_nonneg (mul_nonneg (by norm_num) hp) (zero_le_one.trans chiCost_one)
  have hR : 0 ≤ rhoCost := zero_le_one.trans rhoCost_one
  obtain ⟨ha0, ha1, ha2⟩ := rawAmp_common_bound s epsilon lambda Z v
  have hr0 : ‖rhoS v‖ ≤ rhoCost := by
    simpa only [rhoJ, iteratedDeriv_zero] using rhoJ_bound (j := 0) (by omega) v
  have hr1 := rhoJ_bound (j := 1) (by omega) v
  have hr2 := rhoJ_bound (j := 2) (by omega) v
  have h0 : ‖amp epsilon lambda Z v‖ ≤ rhoCost * q := norm_product_bound hr0 ha0
  have h1 : ‖amp1 epsilon lambda Z v‖ ≤ 2 * rhoCost * q :=
    norm_firstProduct_bound hr0 hr1 ha0 ha1
  have h2 : ‖amp2 epsilon lambda Z v‖ ≤ 4 * rhoCost * q := by
    have h := norm_secondProduct_bound hr0 hr1 hr2 ha0 ha1 ha2
    have heq : amp2 epsilon lambda Z v = secondProduct (rhoS v) (rhoJ 1 v) (rhoJ 2 v)
        (rawAmp epsilon lambda Z v) (rawAmp1 epsilon lambda Z v) (rawAmp2 epsilon lambda Z v) := by
      dsimp only [amp2, secondProduct]
      ring
    rw [heq]
    exact h
  have h : ‖ampJ j epsilon lambda Z v‖ ≤ 4 * rhoCost * q := by
    interval_cases j
    · exact h0.trans (by nlinarith [mul_nonneg hR hq])
    · exact h1.trans (by nlinarith [mul_nonneg hR hq])
    · exact h2
  refine h.trans_eq ?_
  dsimp only [q, p]
  ring

def ampCost (s : ℕ) : ℝ := 64 * rhoCost * chiCost * phiCost s * (Real.exp 8) ^ s

lemma ampCost_nonneg (s : ℕ) : 0 ≤ ampCost s := by
  unfold ampCost
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans rhoCost_one))
      (zero_le_one.trans chiCost_one)) (zero_le_one.trans (phiCost_one s))) (by positivity)

lemma xval_abs {epsilon lambda : ℝ} (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (v : ℝ) :
    |xval epsilon lambda v| = lambda * Real.exp v := by
  simp only [xval, abs_mul, hepsilon, one_mul, abs_of_nonneg hlambda,
    abs_of_pos (Real.exp_pos v)]

lemma lambda_weight_on_support {epsilon lambda v : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (hv : v ∈ Icc (-8 : ℝ) 4) :
    1 + lambda ≤ Real.exp 8 * (1 + |xval epsilon lambda v|) := by
  have he1 : 1 ≤ Real.exp 8 := Real.one_le_exp_iff.mpr (by norm_num)
  have he : Real.exp (-v) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith [hv.1])
  have hmul : Real.exp (-v) * |xval epsilon lambda v| = lambda := by
    rw [xval_abs hepsilon hlambda]
    calc
      _ = lambda * (Real.exp (-v) * Real.exp v) := by ring
      _ = lambda := by rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_right he (abs_nonneg (xval epsilon lambda v))
  rw [hmul] at h
  nlinarith

/-- Uniform for every Z>0; the proof in fact also covers Lean's value at Z=0.
The r^j chi^(j)(r) factors were bounded by the actual fixed chi seminorms,
so no power of 1/Z has been independently estimated. -/
lemma actual_amp_uniform_weighted (s : ℕ) {epsilon lambda : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (Z v : ℝ)
    {j : ℕ} (hj : j ≤ 2) :
    (1 + lambda) ^ s * ‖ampJ j epsilon lambda Z v‖ ≤ ampCost s := by
  by_cases hv : v ∈ Icc (-8 : ℝ) 4
  · have hp : (1 + lambda) ^ s ≤ (Real.exp 8) ^ s *
        (1 + |xval epsilon lambda v|) ^ s := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (lambda_weight_on_support hepsilon hlambda hv) s
    have hA := ampJ_common_bound s hj epsilon lambda Z v
    have hw : 0 < (1 + |xval epsilon lambda v|) ^ s := by positivity
    calc
      _ ≤ ((Real.exp 8) ^ s * (1 + |xval epsilon lambda v|) ^ s) *
          ‖ampJ j epsilon lambda Z v‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ ((Real.exp 8) ^ s * (1 + |xval epsilon lambda v|) ^ s) *
          (64 * rhoCost * chiCost * phiCost s / (1 + |xval epsilon lambda v|) ^ s) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ = ampCost s := by unfold ampCost; field_simp [hw.ne']
  · rw [ampJ_zero_off hv]
    simpa only [norm_zero, mul_zero] using ampCost_nonneg s

lemma actual_amp_uniform (s : ℕ) {epsilon lambda : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (Z v : ℝ)
    {j : ℕ} (hj : j ≤ 2) :
    ‖ampJ j epsilon lambda Z v‖ ≤ ampCost s / (1 + lambda) ^ s := by
  exact (le_div_iff₀ (by positivity)).mpr (by
    simpa only [mul_comm] using actual_amp_uniform_weighted s hepsilon hlambda Z v hj)

/- Explicit Euler polynomials of the oscillatory factor. The index here counts
the mixed word in the phase only; no fourth x- or fourth y-derivative of G is
estimated or supplied to the Fourier theorem. -/
def phasePoly : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, z => z
  | 2, z => z + z ^ 2
  | 3, z => z + 3 * z ^ 2 + z ^ 3
  | _, z => z + 7 * z ^ 2 + 6 * z ^ 3 + z ^ 4

def phaseArg (xi epsilon lambda eta v : ℝ) : ℂ :=
  ((2 * Real.pi * xi * epsilon * lambda * Real.exp (v - eta) : ℝ) : ℂ) * Complex.I

def phaseJet (j : ℕ) (xi epsilon lambda eta v : ℝ) : ℂ :=
  phasePoly j (phaseArg xi epsilon lambda eta v) *
    Complex.exp (phaseArg xi epsilon lambda eta v)

lemma phasePoly_step {z : ℝ → ℂ} {c : ℂ} {t : ℝ}
    (hz : HasDerivAt z (c * z t) t) {j : ℕ} (hj : j < 4) :
    HasDerivAt (fun u => phasePoly j (z u) * Complex.exp (z u))
      (c * (phasePoly (j + 1) (z t) * Complex.exp (z t))) t := by
  have he := hz.cexp
  interval_cases j
  · simp only [phasePoly, one_mul]
    convert! he using 1
    ring
  · simp only [phasePoly]
    convert! hz.mul he using 1
    ring
  · simp only [phasePoly]
    convert! (hz.add (hz.pow 2)).mul he using 1
    simp only [Pi.add_apply, Pi.pow_apply]
    ring
  · simp only [phasePoly]
    convert! ((hz.add ((hz.pow 2).const_mul 3)).add (hz.pow 3)).mul he using 1
    simp only [Pi.add_apply, Pi.pow_apply]
    ring

lemma phaseArg_v (xi epsilon lambda eta v : ℝ) :
    HasDerivAt (phaseArg xi epsilon lambda eta) (phaseArg xi epsilon lambda eta v) v := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (u - eta)) (Real.exp (v - eta)) v := by
    simpa only [Function.comp_apply, mul_one] using!
      (Real.hasDerivAt_exp (v - eta)).comp v ((hasDerivAt_id v).sub_const eta)
  convert! ((he.const_mul (2 * Real.pi * xi * epsilon * lambda)).ofReal_comp).mul_const
    Complex.I using 1

lemma phaseArg_eta (xi epsilon lambda eta v : ℝ) :
    HasDerivAt (fun u => phaseArg xi epsilon lambda u v)
      (-phaseArg xi epsilon lambda eta v) eta := by
  have he := (Real.hasDerivAt_exp (v - eta)).comp eta ((hasDerivAt_id eta).const_sub v)
  convert! ((he.const_mul (2 * Real.pi * xi * epsilon * lambda)).ofReal_comp).mul_const
    Complex.I using 1
  unfold phaseArg
  push_cast
  ring

lemma phaseJet_v (xi epsilon lambda eta v : ℝ) {j : ℕ} (hj : j < 4) :
    HasDerivAt (phaseJet j xi epsilon lambda eta) (phaseJet (j + 1) xi epsilon lambda eta v) v := by
  have hz : HasDerivAt (phaseArg xi epsilon lambda eta)
      ((1 : ℂ) * phaseArg xi epsilon lambda eta v) v := by
    simpa only [one_mul] using phaseArg_v xi epsilon lambda eta v
  simpa only [phaseJet, one_mul] using! phasePoly_step hz hj

lemma phaseJet_eta (xi epsilon lambda eta v : ℝ) {j : ℕ} (hj : j < 4) :
    HasDerivAt (fun u => phaseJet j xi epsilon lambda u v)
      (-phaseJet (j + 1) xi epsilon lambda eta v) eta := by
  have hz : HasDerivAt (fun u => phaseArg xi epsilon lambda u v)
      ((-1 : ℂ) * phaseArg xi epsilon lambda eta v) eta := by
    simpa only [neg_one_mul] using phaseArg_eta xi epsilon lambda eta v
  simpa only [phaseJet, neg_one_mul] using! phasePoly_step hz hj

lemma phaseArg_contDiff (xi epsilon lambda : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (phaseArg xi epsilon lambda)) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_snd.sub contDiff_fst)))).mul
      contDiff_const

lemma phasePoly_contDiff (j : ℕ) : ContDiff ℝ ∞ (phasePoly j) := by
  rcases j with _ | j
  · exact contDiff_const
  rcases j with _ | j
  · exact contDiff_id
  rcases j with _ | j
  · change ContDiff ℝ ∞ (fun z : ℂ => z + z ^ 2)
    fun_prop
  rcases j with _ | j
  · change ContDiff ℝ ∞ (fun z : ℂ => z + 3 * z ^ 2 + z ^ 3)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : ℂ => z + 7 * z ^ 2 + 6 * z ^ 3 + z ^ 4)
    fun_prop

lemma phaseJet_contDiff (j : ℕ) (xi epsilon lambda : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (phaseJet j xi epsilon lambda)) :=
  ((phasePoly_contDiff j).comp (phaseArg_contDiff xi epsilon lambda)).mul
    (Complex.contDiff_exp.comp (phaseArg_contDiff xi epsilon lambda))

lemma norm_phase_exp (xi epsilon lambda eta v : ℝ) :
    ‖Complex.exp (phaseArg xi epsilon lambda eta v)‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [phaseArg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, Real.exp_zero]

lemma phasePoly_norm_bound {z : ℂ} {t : ℝ} (ht : 1 ≤ t) (hz : ‖z‖ ≤ t)
    {j : ℕ} (hj : j ≤ 4) : ‖phasePoly j z‖ ≤ 15 * t ^ 4 := by
  have h04 : 1 ≤ t ^ 4 := one_le_pow₀ ht
  have h14 : t ≤ t ^ 4 := by simpa only [pow_one] using pow_le_pow_right₀ ht (by decide : 1 ≤ 4)
  have h24 : t ^ 2 ≤ t ^ 4 := pow_le_pow_right₀ ht (by decide : 2 ≤ 4)
  have h34 : t ^ 3 ≤ t ^ 4 := pow_le_pow_right₀ ht (by decide : 3 ≤ 4)
  have hz2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hz3 := pow_le_pow_left₀ (norm_nonneg z) hz 3
  have hz4 := pow_le_pow_left₀ (norm_nonneg z) hz 4
  have h3 : ‖z + 3 * z ^ 2 + z ^ 3‖ ≤ ‖z‖ + 3 * ‖z‖ ^ 2 + ‖z‖ ^ 3 := by
    calc
      _ ≤ (‖z‖ + ‖(3 : ℂ) * z ^ 2‖) + ‖z ^ 3‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [norm_mul, norm_pow]; norm_num
  have h4 : ‖z + 7 * z ^ 2 + 6 * z ^ 3 + z ^ 4‖ ≤
      ‖z‖ + 7 * ‖z‖ ^ 2 + 6 * ‖z‖ ^ 3 + ‖z‖ ^ 4 := by
    calc
      _ ≤ ((‖z‖ + ‖(7 : ℂ) * z ^ 2‖) + ‖(6 : ℂ) * z ^ 3‖) + ‖z ^ 4‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ = _ := by simp only [norm_mul, norm_pow]; norm_num
  interval_cases j
  · simp only [phasePoly, norm_one]; nlinarith
  · simp only [phasePoly]; nlinarith
  · have h := norm_add_le z (z ^ 2)
    simp only [norm_pow] at h
    change ‖z + z ^ 2‖ ≤ 15 * t ^ 4
    nlinarith
  · change ‖z + 3 * z ^ 2 + z ^ 3‖ ≤ 15 * t ^ 4
    nlinarith
  · change ‖z + 7 * z ^ 2 + 6 * z ^ 3 + z ^ 4‖ ≤ 15 * t ^ 4
    nlinarith

def phaseBase : ℝ := 1 + 2 * Real.pi * Real.exp 64
def phaseCost : ℝ := 15 * phaseBase ^ 4

lemma phaseBase_one : 1 ≤ phaseBase := by
  have h : 0 ≤ 2 * Real.pi * Real.exp 64 := by positivity
  unfold phaseBase
  linarith
lemma phaseCost_nonneg : 0 ≤ phaseCost := by unfold phaseCost; positivity

lemma phaseArg_bound {xi epsilon lambda eta v : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda)
    (heta : eta ∈ Icc (-32 : ℝ) 32) (hv : v ∈ Icc (-32 : ℝ) 32) :
    ‖phaseArg xi epsilon lambda eta v‖ ≤ phaseBase * (1 + |xi|) * (1 + lambda) := by
  have hnorm : ‖phaseArg xi epsilon lambda eta v‖ =
      2 * Real.pi * |xi| * lambda * Real.exp (v - eta) := by
    simp only [phaseArg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hepsilon, abs_of_nonneg hlambda,
      abs_of_pos (Real.exp_pos (v - eta)), abs_of_pos Real.pi_pos]
    norm_num
  have he : Real.exp (v - eta) ≤ Real.exp 64 :=
    Real.exp_le_exp.mpr (by linarith [hv.2, heta.1])
  have hC : 2 * Real.pi * Real.exp 64 ≤ phaseBase := by unfold phaseBase; linarith
  have hB : 0 ≤ phaseBase := zero_le_one.trans phaseBase_one
  calc
    _ = 2 * Real.pi * |xi| * lambda * Real.exp (v - eta) := hnorm
    _ ≤ 2 * Real.pi * |xi| * lambda * Real.exp 64 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (2 * Real.pi * Real.exp 64) * |xi| * lambda := by ring
    _ ≤ phaseBase * (1 + |xi|) * (1 + lambda) :=
      mul_le_mul
        (mul_le_mul hC (by linarith : |xi| ≤ 1 + |xi|) (abs_nonneg _) hB)
        (by linarith : lambda ≤ 1 + lambda) hlambda (by positivity)

lemma phaseJet_bound {xi epsilon lambda eta v : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda)
    (heta : eta ∈ Icc (-32 : ℝ) 32) (hv : v ∈ Icc (-32 : ℝ) 32)
    {j : ℕ} (hj : j ≤ 4) :
    ‖phaseJet j xi epsilon lambda eta v‖ ≤
      phaseCost * (1 + |xi|) ^ 4 * (1 + lambda) ^ 4 := by
  have ht : 1 ≤ phaseBase * (1 + |xi|) * (1 + lambda) := by
    have hB : 0 ≤ phaseBase := zero_le_one.trans phaseBase_one
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ phaseBase * (1 + |xi|) * (1 + lambda) :=
        mul_le_mul
          (mul_le_mul phaseBase_one (by linarith [abs_nonneg xi]) zero_le_one hB)
          (by linarith : 1 ≤ 1 + lambda) zero_le_one (by positivity)
  rw [phaseJet, norm_mul, norm_phase_exp, mul_one]
  refine (phasePoly_norm_bound ht (phaseArg_bound hepsilon hlambda heta hv) hj).trans_eq ?_
  unfold phaseCost
  ring

def jointG (xi epsilon lambda Z eta v : ℝ) : ℂ :=
  rhoS eta * amp epsilon lambda Z v * phaseJet 0 xi epsilon lambda eta v

lemma jointG_literal (xi epsilon lambda Z eta v : ℝ) :
    jointG xi epsilon lambda Z eta v =
      rhoS eta * rhoS v * Phi (xval epsilon lambda v) *
        (poissonSmoothLowPass (xval epsilon lambda v / Z) : ℂ) *
          Complex.exp (phaseArg xi epsilon lambda eta v) := by
  simp only [jointG, amp, rawAmp, phaseJet, phasePoly, one_mul, chiS_apply]
  ring

lemma actual_phase_normalization (xi epsilon lambda eta v : ℝ) :
    Complex.exp (phaseArg xi epsilon lambda eta v) =
      fourier (1 : ℤ) ((xi * epsilon * lambda * Real.exp (v - eta) : ℝ) : UnitAddCircle) := by
  simp only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
  congr 1
  unfold phaseArg
  push_cast
  ring

lemma jointG_on_physical_log_cell (xi epsilon lambda Z eta v : ℝ)
    (heta : eta ∈ Icc (-5 : ℝ) 1) (hv : v ∈ Icc (-5 : ℝ) 1) :
    jointG xi epsilon lambda Z eta v = Phi (xval epsilon lambda v) *
      (poissonSmoothLowPass (xval epsilon lambda v / Z) : ℂ) *
        Complex.exp (phaseArg xi epsilon lambda eta v) := by
  rw [jointG_literal, rho_one heta, rho_one hv]
  ring

lemma jointG_support (xi epsilon lambda Z : ℝ) :
    Function.support (Function.uncurry (jointG xi epsilon lambda Z)) ⊆
      Icc (-8 : ℝ) 4 ×ˢ Icc (-8 : ℝ) 4 := by
  intro p hp
  have h0 : rhoS p.1 ≠ 0 := by
    intro h
    apply hp
    change jointG xi epsilon lambda Z p.1 p.2 = 0
    simp only [jointG, h, zero_mul]
  have h1 : rhoS p.2 ≠ 0 := by
    intro h
    apply hp
    change jointG xi epsilon lambda Z p.1 p.2 = 0
    simp only [jointG, amp, h, zero_mul, mul_zero]
  exact ⟨rho_tsupport (subset_tsupport _ h0), rho_tsupport (subset_tsupport _ h1)⟩

lemma actual_InBox (xi epsilon lambda Z : ℝ) : InBox (jointG xi epsilon lambda Z) := by
  intro p hp
  obtain ⟨heta, hv⟩ := jointG_support xi epsilon lambda Z hp
  exact ⟨⟨by linarith [heta.1], by linarith [heta.2]⟩,
    ⟨by linarith [hv.1], by linarith [hv.2]⟩⟩

lemma secondProduct_actual {f f1 f2 g g1 g2 : ℝ → ℂ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hg : ∀ t, HasDerivAt g (g1 t) t) (hg1 : ∀ t, HasDerivAt g1 (g2 t) t) (v : ℝ) :
    iteratedDeriv 2 (fun t => f t * g t) v =
      secondProduct (f v) (f1 v) (f2 v) (g v) (g1 v) (g2 v) := by
  apply second_of_jets (f1 := fun t => firstProduct (f t) (f1 t) (g t) (g1 t))
  · intro t
    exact (hf t).mul (hg t)
  · intro t
    convert! ((hf1 t).mul (hg t)).add ((hf t).mul (hg1 t)) using 1
    unfold secondProduct
    ring

def phaseAmp (j : ℕ) (xi epsilon lambda Z eta v : ℝ) : ℂ :=
  amp epsilon lambda Z v * phaseJet j xi epsilon lambda eta v

def phaseAmp2 (j : ℕ) (xi epsilon lambda Z eta v : ℝ) : ℂ :=
  secondProduct (amp epsilon lambda Z v) (amp1 epsilon lambda Z v) (amp2 epsilon lambda Z v)
    (phaseJet j xi epsilon lambda eta v) (phaseJet (j + 1) xi epsilon lambda eta v)
      (phaseJet (j + 2) xi epsilon lambda eta v)

def joint20 (xi epsilon lambda Z eta v : ℝ) : ℂ :=
  secondProduct (rhoS eta) (rhoJ 1 eta) (rhoJ 2 eta)
    (phaseAmp 0 xi epsilon lambda Z eta v) (-phaseAmp 1 xi epsilon lambda Z eta v)
      (phaseAmp 2 xi epsilon lambda Z eta v)

def joint02 (xi epsilon lambda Z eta v : ℝ) : ℂ :=
  rhoS eta * phaseAmp2 0 xi epsilon lambda Z eta v

def joint22 (xi epsilon lambda Z eta v : ℝ) : ℂ :=
  secondProduct (rhoS eta) (rhoJ 1 eta) (rhoJ 2 eta)
    (phaseAmp2 0 xi epsilon lambda Z eta v) (-phaseAmp2 1 xi epsilon lambda Z eta v)
      (phaseAmp2 2 xi epsilon lambda Z eta v)

lemma actual_dx2 (xi epsilon lambda Z eta v : ℝ) :
    dx2 (jointG xi epsilon lambda Z) eta v = joint20 xi epsilon lambda Z eta v := by
  have hr0 (t : ℝ) : HasDerivAt (rhoS : ℝ → ℂ) (rhoJ 1 t) t := by
    simpa only [rhoJ, iteratedDeriv_zero] using jet_hasDerivAt rhoS 0 t
  have hr1 (t : ℝ) : HasDerivAt (rhoJ 1) (rhoJ 2 t) t := jet_hasDerivAt rhoS 1 t
  have he0 (t : ℝ) : HasDerivAt (fun u => phaseJet 0 xi epsilon lambda u v)
      (-phaseJet 1 xi epsilon lambda t v) t := phaseJet_eta xi epsilon lambda t v (by decide)
  have he1 (t : ℝ) : HasDerivAt (fun u => -phaseJet 1 xi epsilon lambda u v)
      (phaseJet 2 xi epsilon lambda t v) t := by
    simpa only [neg_neg] using! (phaseJet_eta xi epsilon lambda t v (j := 1) (by decide)).neg
  have hfun : (fun t => jointG xi epsilon lambda Z t v) =
      (fun t => amp epsilon lambda Z v * (rhoS t * phaseJet 0 xi epsilon lambda t v)) := by
    funext t
    unfold jointG
    ring
  rw [dx2, hfun, iteratedDeriv_const_mul_field, secondProduct_actual hr0 hr1 he0 he1]
  unfold joint20 secondProduct phaseAmp
  ring

lemma actual_phaseAmp2 (xi epsilon lambda Z eta v : ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv 2 (phaseAmp j xi epsilon lambda Z eta) v =
      phaseAmp2 j xi epsilon lambda Z eta v := by
  exact secondProduct_actual (amp_hasDerivAt epsilon lambda Z) (amp1_hasDerivAt epsilon lambda Z)
    (fun t => phaseJet_v xi epsilon lambda eta t (by omega : j < 4))
    (fun t => phaseJet_v xi epsilon lambda eta t (by omega : j + 1 < 4)) v

lemma actual_dy2 (xi epsilon lambda Z eta v : ℝ) :
    dy2 (jointG xi epsilon lambda Z) eta v = joint02 xi epsilon lambda Z eta v := by
  have hfun : jointG xi epsilon lambda Z eta =
      (fun t => rhoS eta * phaseAmp 0 xi epsilon lambda Z eta t) := by
    funext t
    unfold jointG phaseAmp
    ring
  rw [dy2, hfun, iteratedDeriv_const_mul_field, actual_phaseAmp2 xi epsilon lambda Z eta v (by decide)]
  rfl

lemma jointG_contDiff (xi epsilon lambda Z : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (jointG xi epsilon lambda Z)) :=
  ((rhoS.smooth'.comp contDiff_fst).mul ((amp_contDiff epsilon lambda Z).comp contDiff_snd)).mul
    (phaseJet_contDiff 0 xi epsilon lambda)

lemma phaseAmp_contDiff (j : ℕ) (xi epsilon lambda Z : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (phaseAmp j xi epsilon lambda Z)) :=
  ((amp_contDiff epsilon lambda Z).comp contDiff_snd).mul
    (phaseJet_contDiff j xi epsilon lambda)

lemma joint20_contDiff (xi epsilon lambda Z : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (joint20 xi epsilon lambda Z)) := by
  have hr0 := rhoS.smooth'.comp (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1))
  have hr1 := (smooth_jet rhoS 1).comp (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1))
  have hr2 := (smooth_jet rhoS 2).comp (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1))
  exact ((hr2.mul (phaseAmp_contDiff 0 xi epsilon lambda Z)).add
    (contDiff_const.mul (hr1.mul (phaseAmp_contDiff 1 xi epsilon lambda Z).neg))).add
      (hr0.mul (phaseAmp_contDiff 2 xi epsilon lambda Z))

/-- All MixedC2 fields are proved for the actual function and actual x-second
derivative. Infinite regularity is used qualitatively only; no radial norm or
coordinate derivative of order three or four is charged. -/
lemma actual_MixedC2 (xi epsilon lambda Z : ℝ) : MixedC2 (jointG xi epsilon lambda Z) := by
  have hG := jointG_contDiff xi epsilon lambda Z
  have h20 := joint20_contDiff xi epsilon lambda Z
  have heq : dx2 (jointG xi epsilon lambda Z) = joint20 xi epsilon lambda Z :=
    funext (fun eta => funext (fun v => actual_dx2 xi epsilon lambda Z eta v))
  refine ⟨hG.continuous, ?_, ?_, ?_, ?_⟩
  · intro v
    exact (hG.comp (contDiff_id.prodMk contDiff_const)).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  · intro eta
    exact (hG.comp (contDiff_const.prodMk contDiff_id)).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  · rw [heq]
    exact h20.continuous
  · intro eta
    rw [heq]
    exact (h20.comp (contDiff_const.prodMk contDiff_id)).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

lemma secondProduct_const_d2 {f0 f1 f2 : ℝ → ℂ}
    (hf0 : ContDiff ℝ 2 f0) (hf1 : ContDiff ℝ 2 f1) (hf2 : ContDiff ℝ 2 f2)
    (a0 a1 a2 : ℂ) (v : ℝ) :
    iteratedDeriv 2 (fun t => secondProduct a0 a1 a2 (f0 t) (f1 t) (f2 t)) v =
      secondProduct a0 a1 a2 (iteratedDeriv 2 f0 v) (iteratedDeriv 2 f1 v)
        (iteratedDeriv 2 f2 v) := by
  unfold secondProduct
  rw [iteratedDeriv_fun_add
      (((contDiff_const.mul hf0).add (contDiff_const.mul (contDiff_const.mul hf1))).contDiffAt)
      (contDiff_const.mul hf2).contDiffAt,
    iteratedDeriv_fun_add (contDiff_const.mul hf0).contDiffAt
      (contDiff_const.mul (contDiff_const.mul hf1)).contDiffAt]
  simp only [iteratedDeriv_const_mul_field]

lemma actual_dy2_dx2 (xi epsilon lambda Z eta v : ℝ) :
    dy2 (dx2 (jointG xi epsilon lambda Z)) eta v = joint22 xi epsilon lambda Z eta v := by
  have hfun : dx2 (jointG xi epsilon lambda Z) eta = joint20 xi epsilon lambda Z eta :=
    funext (fun t => actual_dx2 xi epsilon lambda Z eta t)
  have hs (j : ℕ) : ContDiff ℝ 2 (phaseAmp j xi epsilon lambda Z eta) :=
    ((phaseAmp_contDiff j xi epsilon lambda Z).comp
      (contDiff_const.prodMk contDiff_id)).of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [dy2, hfun]
  unfold joint20
  rw [secondProduct_const_d2 (hs 0) (hs 1).neg (hs 2), iteratedDeriv_fun_neg,
    actual_phaseAmp2 xi epsilon lambda Z eta v (j := 0) (by decide),
    actual_phaseAmp2 xi epsilon lambda Z eta v (j := 1) (by decide),
    actual_phaseAmp2 xi epsilon lambda Z eta v (j := 2) (by decide)]
  rfl

def jointCost (b : ℕ) : ℝ := 16 * rhoCost * phaseCost * ampCost (b + 4)
def jointBudget (b : ℕ) (xi lambda : ℝ) : ℝ :=
  jointCost b * (1 + |xi|) ^ 4 / (1 + lambda) ^ b

lemma jointCost_nonneg (b : ℕ) : 0 ≤ jointCost b :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans rhoCost_one))
    phaseCost_nonneg) (ampCost_nonneg _)

lemma jointBudget_nonneg (b : ℕ) (xi : ℝ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    0 ≤ jointBudget b xi lambda :=
  div_nonneg (mul_nonneg (jointCost_nonneg b) (by positivity)) (by positivity)

/-- The quantitative actual instance. The extra FOUR Schwartz weights in
ampCost(b+4) cancel the fourth phase power; the only varying residue cost is
(1+|xi|)^4. Every Z is quantified after the fixed constants. -/
theorem actual_MixedBounds (b : ℕ) (xi : ℝ) {epsilon lambda : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (Z : ℝ) :
    MixedBounds (jointG xi epsilon lambda Z) (jointBudget b xi lambda) := by
  let A : ℝ := ampCost (b + 4) / (1 + lambda) ^ (b + 4)
  let E : ℝ := phaseCost * (1 + |xi|) ^ 4 * (1 + lambda) ^ 4
  have hA : 0 ≤ A := div_nonneg (ampCost_nonneg _) (by positivity)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg phaseCost_nonneg (by positivity)) (by positivity)
  have hR : 0 ≤ rhoCost := zero_le_one.trans rhoCost_one
  have hRAE : 0 ≤ rhoCost * (A * E) := mul_nonneg hR (mul_nonneg hA hE)
  have hnormal : 16 * rhoCost * (A * E) = jointBudget b xi lambda := by
    have hne : 1 + lambda ≠ 0 := ne_of_gt (by linarith : 0 < 1 + lambda)
    dsimp only [A, E, jointBudget, jointCost]
    rw [pow_add]
    field_simp [hne]
  have hbounds (eta : ℝ) (heta : eta ∈ Icc (-32 : ℝ) 32)
      (v : ℝ) (hv : v ∈ Icc (-32 : ℝ) 32) :
      ‖jointG xi epsilon lambda Z eta v‖ ≤ jointBudget b xi lambda ∧
      ‖joint20 xi epsilon lambda Z eta v‖ ≤ jointBudget b xi lambda ∧
      ‖joint02 xi epsilon lambda Z eta v‖ ≤ jointBudget b xi lambda ∧
      ‖joint22 xi epsilon lambda Z eta v‖ ≤ jointBudget b xi lambda := by
    have ha0 : ‖amp epsilon lambda Z v‖ ≤ A :=
      actual_amp_uniform (b + 4) hepsilon hlambda Z v (j := 0) (by decide)
    have ha1 : ‖amp1 epsilon lambda Z v‖ ≤ A :=
      actual_amp_uniform (b + 4) hepsilon hlambda Z v (j := 1) (by decide)
    have ha2 : ‖amp2 epsilon lambda Z v‖ ≤ A :=
      actual_amp_uniform (b + 4) hepsilon hlambda Z v (j := 2) (by decide)
    have he (j : ℕ) (hj : j ≤ 4) : ‖phaseJet j xi epsilon lambda eta v‖ ≤ E :=
      phaseJet_bound hepsilon hlambda heta hv hj
    have hp (j : ℕ) (hj : j ≤ 2) : ‖phaseAmp j xi epsilon lambda Z eta v‖ ≤ A * E :=
      norm_product_bound ha0 (he j (by omega))
    have hp2 (j : ℕ) (hj : j ≤ 2) :
        ‖phaseAmp2 j xi epsilon lambda Z eta v‖ ≤ 4 * A * E :=
      norm_secondProduct_bound ha0 ha1 ha2 (he j (by omega))
        (he (j + 1) (by omega)) (he (j + 2) (by omega))
    have hr0 : ‖rhoS eta‖ ≤ rhoCost := by
      simpa only [rhoJ, iteratedDeriv_zero] using rhoJ_bound (j := 0) (by decide) eta
    have hr1 := rhoJ_bound (j := 1) (by decide) eta
    have hr2 := rhoJ_bound (j := 2) (by decide) eta
    have h00 : ‖jointG xi epsilon lambda Z eta v‖ ≤ rhoCost * (A * E) := by
      have heq : jointG xi epsilon lambda Z eta v = rhoS eta *
          phaseAmp 0 xi epsilon lambda Z eta v := by unfold jointG phaseAmp; ring
      rw [heq]
      exact norm_product_bound hr0 (hp 0 (by decide))
    have h20 : ‖joint20 xi epsilon lambda Z eta v‖ ≤ 4 * rhoCost * (A * E) :=
      norm_secondProduct_bound hr0 hr1 hr2 (hp 0 (by decide))
        (by simpa only [norm_neg] using hp 1 (by decide)) (hp 2 (by decide))
    have h02 : ‖joint02 xi epsilon lambda Z eta v‖ ≤ rhoCost * (4 * A * E) :=
      norm_product_bound hr0 (hp2 0 (by decide))
    have h22 : ‖joint22 xi epsilon lambda Z eta v‖ ≤ 16 * rhoCost * (A * E) := by
      unfold joint22
      exact (norm_secondProduct_bound hr0 hr1 hr2 (hp2 0 (by decide))
        (by simpa only [norm_neg] using hp2 1 (by decide))
        (hp2 2 (by decide))).trans_eq (by ring)
    simp only [← hnormal]
    exact ⟨h00.trans (by nlinarith), h20.trans (by nlinarith),
      h02.trans (by nlinarith), h22⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro eta heta v hv
    exact (hbounds eta heta v hv).1
  · intro eta heta v hv
    rw [actual_dx2]
    exact (hbounds eta heta v hv).2.1
  · intro eta heta v hv
    rw [actual_dy2]
    exact (hbounds eta heta v hv).2.2.1
  · intro eta heta v hv
    rw [actual_dy2_dx2]
    exact (hbounds eta heta v hv).2.2.2

/-- These are the parent's actual normalized double integral coefficients;
there is no independently chosen coefficient family. -/
def actualDoubleCoeff (xi epsilon lambda Z : ℝ) (m n : ℤ) : ℂ :=
  C2 (jointG xi epsilon lambda Z) m n

lemma actualDoubleCoeff_integral (xi epsilon lambda Z : ℝ) (m n : ℤ) :
    actualDoubleCoeff xi epsilon lambda Z m n = (1 / 64 : ℂ) ^ 2 *
      ∫ eta in (-32 : ℝ)..32, ∫ v in (-32 : ℝ)..32,
        basis (-m) eta * (basis (-n) v * jointG xi epsilon lambda Z eta v) :=
  C2_integral (jointG xi epsilon lambda Z) m n

def fourierCost (b : ℕ) : ℝ := fixedCost ^ 2 * jointCost b * seriesCost

lemma fourierCost_nonneg (b : ℕ) : 0 ≤ fourierCost b := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (jointCost_nonneg b))
    (by unfold seriesCost; positivity)

/-- Real uniform-Z l1, obtained by filling all three actual inputs of the
frozen mixed22 supplier. No derivative/coefficient/l1 hypothesis remains. -/
theorem actual_doubleCoeff_l1 (b : ℕ) (xi : ℝ) {epsilon lambda : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (Z : ℝ) (_hZ : 0 < Z) :
    Summable (fun p : ℤ × ℤ => ‖actualDoubleCoeff xi epsilon lambda Z p.1 p.2‖) ∧
      (∑' p : ℤ × ℤ, ‖actualDoubleCoeff xi epsilon lambda Z p.1 p.2‖) ≤
        fourierCost b * (1 + |xi|) ^ 4 / (1 + lambda) ^ b := by
  have h := C2_l1 (jointG xi epsilon lambda Z) (actual_MixedC2 xi epsilon lambda Z)
    (actual_InBox xi epsilon lambda Z) (jointBudget b xi lambda)
    (jointBudget_nonneg b xi hlambda) (actual_MixedBounds b xi hepsilon hlambda Z)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  unfold jointBudget fourierCost
  ring

/-- Actual MediumAtom residue, with the ORIGINAL five-kappa debit used once.
This is an alternative upper bound on the same coefficient norm, not a second
factor to multiply into the fourth-power estimate. -/
theorem actual_atom_doubleCoeff_l1 (b : ℕ)
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hkappa : 0 ≤ kappa)
    {epsilon lambda : ℝ} (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda)
    (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun p : ℤ × ℤ => ‖actualDoubleCoeff
      (GeneralDSlowPhaseParametersSourceOnly.movingRatio d) epsilon lambda Z p.1 p.2‖) ∧
      (∑' p : ℤ × ℤ, ‖actualDoubleCoeff
        (GeneralDSlowPhaseParametersSourceOnly.movingRatio d) epsilon lambda Z p.1 p.2‖) ≤
        16 * fourierCost b * d.scale ^ (5 * kappa) / (1 + lambda) ^ b := by
  have h := actual_doubleCoeff_l1 b (GeneralDSlowPhaseParametersSourceOnly.movingRatio d)
    hepsilon hlambda Z hZ
  have hdebit := GeneralDSlowPhaseParametersSourceOnly.actual_joint_symbol_debit_le_original_five
    hd hkappa
  refine ⟨h.1, h.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (mul_le_mul_of_nonneg_left hdebit (fourierCost_nonneg b)).trans_eq (by ring)

theorem actual_doubleCoeff_decay (b : ℕ) (xi : ℝ) {epsilon lambda : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (Z : ℝ) (m n : ℤ) :
    ‖actualDoubleCoeff xi epsilon lambda Z m n‖ ≤
      (fixedCost ^ 2 * jointBudget b xi lambda) * decay m * decay n :=
  C2_product_decay (jointG xi epsilon lambda Z) (actual_MixedC2 xi epsilon lambda Z)
    (actual_InBox xi epsilon lambda Z) (jointBudget b xi lambda)
    (jointBudget_nonneg b xi hlambda) (actual_MixedBounds b xi hepsilon hlambda Z) m n

theorem actual_doubleCoeff_hasSum (b : ℕ) (xi : ℝ) {epsilon lambda : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (Z eta v : ℝ)
    (heta : eta ∈ Ioc (-32 : ℝ) 32) (hv : v ∈ Ioc (-32 : ℝ) 32) :
    HasSum (fun p : ℤ × ℤ => actualDoubleCoeff xi epsilon lambda Z p.1 p.2 *
      basis p.1 eta * basis p.2 v) (jointG xi epsilon lambda Z eta v) :=
  C2_hasSum (jointG xi epsilon lambda Z) (actual_MixedC2 xi epsilon lambda Z)
    (actual_InBox xi epsilon lambda Z) (jointBudget b xi lambda)
    (jointBudget_nonneg b xi hlambda) (actual_MixedBounds b xi hepsilon hlambda Z) eta v heta hv

theorem actual_physical_reconstruction (b : ℕ) (xi : ℝ) {epsilon lambda : ℝ}
    (hepsilon : |epsilon| = 1) (hlambda : 0 ≤ lambda) (Z eta v : ℝ)
    (heta : eta ∈ Icc (-5 : ℝ) 1) (hv : v ∈ Icc (-5 : ℝ) 1) :
    HasSum (fun p : ℤ × ℤ => actualDoubleCoeff xi epsilon lambda Z p.1 p.2 *
      basis p.1 eta * basis p.2 v)
      (Phi (xval epsilon lambda v) *
        (poissonSmoothLowPass (xval epsilon lambda v / Z) : ℂ) *
          Complex.exp (phaseArg xi epsilon lambda eta v)) := by
  rw [← jointG_on_physical_log_cell xi epsilon lambda Z eta v heta hv]
  exact actual_doubleCoeff_hasSum b xi hepsilon hlambda Z eta v
    ⟨by linarith [heta.1], by linarith [heta.2]⟩
    ⟨by linarith [hv.1], by linarith [hv.2]⟩

/- Exact remaining integration boundary: the atom's xi=a/(U*M) and original
N1 interval/debit are proved in the frozen actual-parameter companion.
Substitute epsilon=sign(h), lambda=T0*H and eta=log(N1/U) only after the
literal signed dyadic/log-coordinate adapter has supplied its exact algebra.
This source does not move gamma2 through Re, conjugate gamma2, remove any
arithmetic gate, alter the shared Fourier index, or assert the spectral return.
The norm factor (1+|xi|)^4 fits the original single 5*kappa charge via that
companion; it must not be charged a second time in the row adapter.
-/

end P3ActualJointGSourceOnly
end



/-!
SOURCEONLY / UNCOMPILED / HOLD -- 2026-10-23.
Load the frozen compact-coordinate SHA933d9458 and mixed22 SHAb907e76,
the actual six parameters SHAbf836248 and actual jointG SHA53ccf3cc FIRST.
Collect the genuine imports from these fragments at the eventual unit head.
No parent is copied or changed. ROOT alone owns the qualification queue.

The actual amplitude and the WHOLE original positive slow character are used.
All coordinates below are constructed from the literal finite factor carriers.
No amplitude identity, log-range, support, l1 or spectral estimate is a premise.
The frequency blocks are exact fibres of the ORIGINAL signed shortened window.
-/

noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators ContDiff SchwartzMap FourierTransform

namespace P3ActualLogAdapterSourceOnly
open ImbalancedChen.Part3 ImbalancedChen.Part3.CommonSmoothCutoff
open P3TwoLogMixed22SourceOnly P3ActualJointGSourceOnly
open ImbalancedChen.Part3.GeneralDSlowPhaseParametersSourceOnly

/-- D is an EXTERNAL fixed feature, not recomputed inside the coefficients.
The fields are literal source-carrier licences and the original actual gcd gate.
There is no new real support assumption or analytic estimate in this record. -/
structure Cell (d : MediumAtom) (D : ℕ) where
  p : ℕ
  r : ℕ
  s : ℕ
  r' : ℕ
  s' : ℕ
  N1 : ℕ
  hp : p ∈ d.primitiveFirstFactorCarrier
  hr : r ∈ factorCarrier d.Q3
  hs : s ∈ factorCarrier d.Q2
  hr' : r' ∈ factorCarrier d.Q3
  hs' : s' ∈ factorCarrier d.Q2
  hN1 : N1 ∈ d.transposedAtom.betaCarrier
  hgcd : (r * s).gcd (r' * s') = D

def Cell.w {d : MediumAtom} {D : ℕ} (c : Cell d D) : ℕ := c.r' * c.s'
def Cell.L {d : MediumAtom} {D : ℕ} (c : Cell d D) : ℕ :=
  (c.p * (c.r * c.s)).lcm (c.p * c.w)

/-- Extract the literal finite-carrier licences; no real rectangle is inserted. -/
lemma original_outer_memberships (d : MediumAtom)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ))
    (ho : o ∈ d.smallCoreSquaredOuterCarrier) :
    o.1.1 ∈ d.primitiveFirstFactorCarrier ∧ o.1.2.1 ∈ d.transposedAtom.betaCarrier ∧
      o.2.1.1 ∈ factorCarrier d.Q3 ∧ o.2.1.2.1 ∈ factorCarrier d.Q3 ∧
      o.2.1.2.2 ∈ factorCarrier d.Q2 := by
  change o ∈ ((d.primitiveFirstFactorCarrier ×ˢ
    (d.transposedAtom.betaCarrier ×ˢ d.transposedAtom.betaCarrier)).filter
      (fun t => t.2.1 ≠ t.2.2 ∧ Nat.ModEq t.1 t.2.1 t.2.2)) ×ˢ
    ((factorCarrier d.Q3) ×ˢ ((factorCarrier d.Q3) ×ˢ factorCarrier d.Q2)).biUnion
      (fun t => (t.2.1 * t.2.2).divisors.image (fun D => (t, D))) at ho
  have hpairs := (Finset.mem_filter.mp (Finset.mem_product.mp ho).1).1
  have hp := (Finset.mem_product.mp hpairs).1
  have hN1 := (Finset.mem_product.mp (Finset.mem_product.mp hpairs).2).1
  obtain ⟨t, ht, hImage⟩ := Finset.mem_biUnion.mp (Finset.mem_product.mp ho).2
  obtain ⟨D, _hD, he⟩ := Finset.mem_image.mp hImage
  have het : t = o.2.1 := congrArg Prod.fst he
  have htail : o.2.1.1 ∈ factorCarrier d.Q3 ∧
      o.2.1.2.1 ∈ factorCarrier d.Q3 ∧ o.2.1.2.2 ∈ factorCarrier d.Q2 := by
    rw [← het]
    exact ⟨(Finset.mem_product.mp ht).1,
      (Finset.mem_product.mp (Finset.mem_product.mp ht).2).1,
      (Finset.mem_product.mp (Finset.mem_product.mp ht).2).2⟩
  exact ⟨hp, hN1, htail⟩

/-- Constructor from the ORIGINAL outer carrier, ORIGINAL inner carrier and
the literal row's gcd guard. The separate CRT guard is not needed analytically. -/
def Cell.ofOriginal (d : MediumAtom) (Z : ℝ)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) (u : ℕ × ℤ)
    (ho : o ∈ d.smallCoreSquaredOuterCarrier)
    (hu : u ∈ d.smallCoreSquaredInnerCarrier Z o)
    (hgcd : (o.2.1.1 * u.1).gcd (o.2.1.2.1 * o.2.1.2.2) = o.2.2) : Cell d o.2.2 where
  p := o.1.1
  r := o.2.1.1
  s := u.1
  r' := o.2.1.2.1
  s' := o.2.1.2.2
  N1 := o.1.2.1
  hp := (original_outer_memberships d o ho).1
  hr := (original_outer_memberships d o ho).2.2.1
  hs := (Finset.mem_product.mp hu).1
  hr' := (original_outer_memberships d o ho).2.2.2.1
  hs' := (original_outer_memberships d o ho).2.2.2.2
  hN1 := (original_outer_memberships d o ho).2.1
  hgcd := hgcd

def base (d : MediumAtom) (D : ℕ) : ℝ :=
  d.V * D / (d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2)
def Hnat (j : ℕ) : ℕ := 2 ^ j
def Hreal (j : ℕ) : ℝ := (Hnat j : ℝ)
def epsilon (negative : Bool) : ℝ := if negative then -1 else 1
def lambda (d : MediumAtom) (D j : ℕ) : ℝ := base d D * Hreal j
def P (d : MediumAtom) (p : ℕ) : ℝ := (p : ℝ) / d.Q1
def Rr (d : MediumAtom) (r : ℕ) : ℝ := (r : ℝ) / d.Q3
def Uu (d : MediumAtom) (s : ℕ) : ℝ := (s : ℝ) / d.Q2
def Ww (d : MediumAtom) (w : ℕ) : ℝ := (w : ℝ) / (d.Q3 * d.Q2)
def product {d : MediumAtom} {D : ℕ} (c : Cell d D) : ℝ :=
  P d c.p * Rr d c.r * Uu d c.s * Ww d c.w
def eta (d : MediumAtom) (N1 : ℕ) : ℝ := Real.log ((N1 : ℝ) / d.U)
def logV {d : MediumAtom} {D : ℕ} (c : Cell d D) (j : ℕ) (h : ℤ) : ℝ :=
  Real.log (|(h : ℝ)| / Hreal j) - Real.log (product c)

lemma epsilon_abs (negative : Bool) : |epsilon negative| = 1 := by
  cases negative <;> norm_num [epsilon]

lemma Hreal_pos (j : ℕ) : 0 < Hreal j := by
  unfold Hreal Hnat
  exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) j)

lemma factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) :
    0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hc : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  exact ⟨by omega, (Nat.le_ceil Q).trans (by exact_mod_cast hlo),
    (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * Q))⟩

lemma factor_ratio {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : (n : ℝ) / Q ∈ Icc (1 : ℝ) 2 := by
  obtain ⟨_, hlo, hhi⟩ := factor_bounds hQ hn
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  exact ⟨(le_div_iff₀ hQ0).mpr (by simpa using hlo), (div_le_iff₀ hQ0).mpr hhi⟩

lemma interval_mul {a b A B : ℝ} (ha : a ∈ Icc 1 A) (hb : b ∈ Icc 1 B) :
    a * b ∈ Icc (1 : ℝ) (A * B) := by
  constructor
  · calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ a * b := mul_le_mul ha.1 hb.1 zero_le_one (by linarith [ha.1])
  · exact mul_le_mul ha.2 hb.2 (by linarith [hb.1]) (by linarith [ha.1, ha.2])

lemma cell_ratios {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) :
    P d c.p ∈ Icc (1 : ℝ) 2 ∧ Rr d c.r ∈ Icc (1 : ℝ) 2 ∧
      Uu d c.s ∈ Icc (1 : ℝ) 2 ∧ Ww d c.w ∈ Icc (1 : ℝ) 4 ∧
      product c ∈ Icc (1 : ℝ) 32 := by
  have hp := factor_ratio hd.2.2.1 (Finset.mem_filter.mp c.hp).1
  have hr := factor_ratio hd.2.2.2.2.1 c.hr
  have hs := factor_ratio hd.2.2.2.1 c.hs
  have hr' := factor_ratio hd.2.2.2.2.1 c.hr'
  have hs' := factor_ratio hd.2.2.2.1 c.hs'
  change P d c.p ∈ Icc 1 2 at hp
  change Rr d c.r ∈ Icc 1 2 at hr
  change Uu d c.s ∈ Icc 1 2 at hs
  have hw : Ww d c.w ∈ Icc (1 : ℝ) 4 := by
    have he : Ww d c.w = ((c.r' : ℝ) / d.Q3) * ((c.s' : ℝ) / d.Q2) := by
      simp only [Ww, Cell.w, Nat.cast_mul, div_mul_div_comm]
    rw [he]
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using interval_mul hr' hs'
  have hpr : P d c.p * Rr d c.r ∈ Icc (1 : ℝ) 4 := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using interval_mul hp hr
  have hpru : P d c.p * Rr d c.r * Uu d c.s ∈ Icc (1 : ℝ) 8 := by
    simpa only [show (4 : ℝ) * 2 = 8 by norm_num] using interval_mul hpr hs
  have hprod : product c ∈ Icc (1 : ℝ) 32 := by
    simpa only [product, show (8 : ℝ) * 4 = 32 by norm_num] using interval_mul hpru hw
  exact ⟨hp, hr, hs, hw, hprod⟩

lemma cell_positive {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) :
    0 < c.p ∧ 0 < c.r ∧ 0 < c.s ∧ 0 < c.w ∧ 0 < c.N1 ∧ 0 < D ∧ 0 < c.L := by
  have hp := (factor_bounds hd.2.2.1 (Finset.mem_filter.mp c.hp).1).1
  have hr := (factor_bounds hd.2.2.2.2.1 c.hr).1
  have hs := (factor_bounds hd.2.2.2.1 c.hs).1
  have hr' := (factor_bounds hd.2.2.2.2.1 c.hr').1
  have hs' := (factor_bounds hd.2.2.2.1 c.hs').1
  have hw : 0 < c.w := Nat.mul_pos hr' hs'
  have hN : 0 < c.N1 := by
    have hN := (actual_transposed_N1_window hd c.hN1).1
    have hNR : 0 < (c.N1 : ℝ) := by linarith [hd.1]
    exact_mod_cast hNR
  have hD : 0 < D := by
    rw [← c.hgcd]
    exact Nat.gcd_pos_of_pos_left c.w (Nat.mul_pos hr hs)
  have hL : 0 < c.L := Nat.lcm_pos (Nat.mul_pos hp (Nat.mul_pos hr hs)) (Nat.mul_pos hp hw)
  exact ⟨hp, hr, hs, hw, hN, hD, hL⟩

/-- The lcm identity is proved on the ACTUAL natural labels, not assumed. -/
lemma actual_D_mul_L {d : MediumAtom} {D : ℕ} (c : Cell d D) :
    D * c.L = c.p * c.r * c.s * c.w := by
  calc
    _ = (c.r * c.s).gcd c.w * c.L :=
      congrArg (fun n : ℕ => n * c.L) (by simpa only [Cell.w] using c.hgcd.symm)
    _ = c.p * ((c.r * c.s).gcd c.w * (c.r * c.s).lcm c.w) := by
      unfold Cell.L
      rw [sharedFirstFactor_lcm]
      ring
    _ = _ := by rw [Nat.gcd_mul_lcm]; ring

/-- T=M/L, not L, is T0 divided by the four ratios. -/
lemma actual_T_normalization {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) :
    d.V / (c.L : ℝ) = base d D / product c := by
  obtain ⟨hp, hr, hs, hw, _, hD, _⟩ := cell_positive hd c
  have hpR : (c.p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hrR : (c.r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hsR : (c.s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have hwR : (c.w : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hQ : d.Q1 ≠ 0 := ne_of_gt (zero_lt_one.trans_le hd.2.2.1)
  have hS : d.Q2 ≠ 0 := ne_of_gt (zero_lt_one.trans_le hd.2.2.2.1)
  have hR : d.Q3 ≠ 0 := ne_of_gt (zero_lt_one.trans_le hd.2.2.2.2.1)
  have hDL : (D : ℝ) * (c.L : ℝ) = (c.p : ℝ) * c.r * c.s * c.w := by
    exact_mod_cast actual_D_mul_L c
  have hL : (c.L : ℝ) = (c.p : ℝ) * c.r * c.s * c.w / D := by
    apply (eq_div_iff hDR).mpr
    nlinarith [hDL]
  rw [hL]
  unfold base product P Rr Uu Ww
  field_simp [hpR, hrR, hsR, hwR, hDR, hQ, hS, hR]

lemma base_nonneg {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D : ℕ) : 0 ≤ base d D := by
  have hV : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hQ : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
  unfold base
  positivity

lemma physical_lambda_pos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) (j : ℕ) :
    0 < lambda d D j := by
  have hD : 0 < (D : ℝ) := by exact_mod_cast (cell_positive hd c).2.2.2.2.2.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hS : 0 < d.Q2 := zero_lt_one.trans_le hd.2.2.2.1
  have hR : 0 < d.Q3 := zero_lt_one.trans_le hd.2.2.2.2.1
  exact mul_pos (div_pos (mul_pos hV hD) (by positivity)) (Hreal_pos j)

/- EXACT finite signed dyadic fibres. No final block is enlarged. -/
def window (d : MediumAtom) (D : ℕ) (Z : ℝ) : Finset ℤ :=
  poissonNonzeroFrequencyWindow (d.sharedSmoothFrequencyBound Z D)
def dyadicKey (h : ℤ) : ℕ × Bool := (Nat.log 2 h.natAbs, decide (h < 0))
def block (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) : Finset ℤ :=
  (window d D Z).filter (fun h => dyadicKey h = a)

lemma window_nonzero {d : MediumAtom} {D : ℕ} {Z : ℝ} {h : ℤ}
    (hh : h ∈ window d D Z) : h ≠ 0 ∧ h.natAbs ≤ d.sharedSmoothFrequencyBound Z D := by
  change h ∈ poissonNonzeroFrequencyWindow (d.sharedSmoothFrequencyBound Z D) at hh
  unfold poissonNonzeroFrequencyWindow at hh
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    exact ⟨by exact_mod_cast hn0, by simpa using (Finset.mem_Icc.mp hn).2⟩
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    exact ⟨neg_ne_zero.mpr (by exact_mod_cast hn0), by simpa using (Finset.mem_Icc.mp hn).2⟩

lemma mem_canonical_block {d : MediumAtom} {D : ℕ} {Z : ℝ} {h : ℤ}
    (hh : h ∈ window d D Z) : h ∈ block d D Z (dyadicKey h) := by
  exact Finset.mem_filter.mpr ⟨hh, rfl⟩

/-- Finite exact decomposition of the ORIGINAL signed shortened window. -/
theorem sum_original_window_eq_blocks (d : MediumAtom) (D : ℕ) (Z : ℝ) (f : ℤ → ℂ) :
    (∑ h ∈ window d D Z, f h) =
      ∑ a ∈ (window d D Z).image dyadicKey, ∑ h ∈ block d D Z a, f h := by
  simpa only [block] using
    (Finset.sum_fiberwise_of_maps_to
      (s := window d D Z) (t := (window d D Z).image dyadicKey) (g := dyadicKey)
      (fun h hh => Finset.mem_image_of_mem dyadicKey hh) f).symm

lemma block_facts {d : MediumAtom} {D : ℕ} {Z : ℝ} {a : ℕ × Bool} {h : ℤ}
    (hh : h ∈ block d D Z a) :
    h ≠ 0 ∧ (h : ℝ) = epsilon a.2 * |(h : ℝ)| ∧
      |(h : ℝ)| / Hreal a.1 ∈ Icc (1 : ℝ) 2 := by
  obtain ⟨hwin, hkey⟩ := Finset.mem_filter.mp hh
  have hn := (window_nonzero hwin).1
  have hnabs : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hj : Nat.log 2 h.natAbs = a.1 := congrArg Prod.fst hkey
  have hlo : Hnat a.1 ≤ h.natAbs := by
    simpa only [Hnat, hj] using Nat.pow_log_le_self 2 hnabs
  have hhi : h.natAbs < 2 * Hnat a.1 := by
    have ht := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) h.natAbs
    simpa only [hj, Hnat, pow_succ, Nat.mul_comm] using ht
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hloR : Hreal a.1 ≤ |(h : ℝ)| := by
    rw [← habs]
    change (Hnat a.1 : ℝ) ≤ (h.natAbs : ℝ)
    exact_mod_cast hlo
  have hhiR : |(h : ℝ)| < 2 * Hreal a.1 := by
    rw [← habs]
    change (h.natAbs : ℝ) < 2 * (Hnat a.1 : ℝ)
    exact_mod_cast hhi
  have hratio : |(h : ℝ)| / Hreal a.1 ∈ Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ (Hreal_pos a.1)).mpr (by simpa using hloR),
      (div_le_iff₀ (Hreal_pos a.1)).mpr hhiR.le⟩
  refine ⟨hn, ?_, hratio⟩
  rw [← hkey]
  by_cases hneg : h < 0
  · have hnegR : (h : ℝ) < 0 := by exact_mod_cast hneg
    simp [dyadicKey, epsilon, hneg, abs_of_neg hnegR]
  · have hpos : 0 < h := by omega
    have hposR : 0 < (h : ℝ) := by exact_mod_cast hpos
    simp [dyadicKey, epsilon, hneg, abs_of_pos hposR]

lemma log_ratio_12 {x : ℝ} (hx : x ∈ Icc 1 2) : Real.log x ∈ Icc (0 : ℝ) 1 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  exact ⟨Real.log_nonneg hx.1, (Real.log_le_sub_one_of_pos hx0).trans (by linarith [hx.2])⟩

lemma log_ratio_132 {x : ℝ} (hx : x ∈ Icc 1 32) : Real.log x ∈ Icc (0 : ℝ) 5 := by
  have h2 := (log_ratio_12 (show (2 : ℝ) ∈ Icc 1 2 by norm_num)).2
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, Real.log_pow]
    norm_num
  exact ⟨Real.log_nonneg hx.1,
    (Real.log_le_log (zero_lt_one.trans_le hx.1) hx.2).trans (by rw [h32]; linarith)⟩

lemma actual_eta_range {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {N1 : ℕ}
    (hN1 : N1 ∈ d.transposedAtom.betaCarrier) : eta d N1 ∈ Icc (-5 : ℝ) 1 := by
  obtain ⟨hlo, hhi⟩ := actual_transposed_N1_window hd hN1
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hq : (N1 : ℝ) / d.U ∈ Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hU).mpr (by simpa using hlo), (div_le_iff₀ hU).mpr hhi⟩
  have h := log_ratio_12 hq
  exact ⟨by change -5 ≤ Real.log ((N1 : ℝ) / d.U); linarith [h.1], h.2⟩

lemma actual_v_range {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    {Z : ℝ} {a : ℕ × Bool} {h : ℤ} (hh : h ∈ block d D Z a) :
    logV c a.1 h ∈ Icc (-5 : ℝ) 1 := by
  have hs := log_ratio_12 (block_facts hh).2.2
  have hp := log_ratio_132 (cell_ratios hd c).2.2.2.2
  unfold logV
  exact ⟨by linarith [hs.1, hp.2], by linarith [hs.2, hp.1]⟩

/-- Literal Th identity, preserving the original signed h. -/
lemma actual_xval {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    {Z : ℝ} {a : ℕ × Bool} {h : ℤ} (hh : h ∈ block d D Z a) :
    xval (epsilon a.2) (lambda d D a.1) (logV c a.1 h) =
      (d.V / (c.L : ℝ)) * (h : ℝ) := by
  have hs := (block_facts hh).2.1
  have hratio : 0 < |(h : ℝ)| / Hreal a.1 :=
    zero_lt_one.trans_le (block_facts hh).2.2.1
  have hprod : 0 < product c := zero_lt_one.trans_le (cell_ratios hd c).2.2.2.2.1
  have he : Real.exp (logV c a.1 h) = (|(h : ℝ)| / Hreal a.1) / product c := by
    rw [logV, Real.exp_sub, Real.exp_log hratio, Real.exp_log hprod]
  calc
    _ = epsilon a.2 * (base d D * Hreal a.1) *
        ((|(h : ℝ)| / Hreal a.1) / product c) := by rw [xval, he]; rfl
    _ = ((epsilon a.2 * base d D) *
        (Hreal a.1 * (|(h : ℝ)| / Hreal a.1))) / product c := by ring
    _ = ((epsilon a.2 * base d D) * |(h : ℝ)|) / product c := by
      rw [mul_div_cancel₀ _ (Hreal_pos a.1).ne']
    _ = (base d D / product c) * (epsilon a.2 * |(h : ℝ)|) := by ring
    _ = (base d D / product c) * (h : ℝ) :=
      congrArg (fun v : ℝ => (base d D / product c) * v) hs.symm
    _ = _ := by rw [← actual_T_normalization hd c]

def slow (d : MediumAtom) (N1 L : ℕ) (h : ℤ) : ℂ :=
  fourier h ((((d.residue : ℝ) / ((N1 : ℝ) * (L : ℝ))) : ℝ) : UnitAddCircle)

lemma fourier_frequency_as_one (u : ℝ) (h : ℤ) :
    fourier h (u : UnitAddCircle) = fourier 1 (((h : ℝ) * u : ℝ) : UnitAddCircle) := by
  simp only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
  congr 1
  push_cast
  ring

/-- Literal WHOLE slow phase: the original N1 and the full lcm L remain. -/
lemma actual_slow_argument {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    {Z : ℝ} {a : ℕ × Bool} {h : ℤ} (hh : h ∈ block d D Z a) :
    movingRatio d * epsilon a.2 * lambda d D a.1 *
        Real.exp (logV c a.1 h - eta d c.N1) =
      (d.residue : ℝ) * (h : ℝ) / ((c.N1 : ℝ) * (c.L : ℝ)) := by
  have hN : 0 < (c.N1 : ℝ) := by exact_mod_cast (cell_positive hd c).2.2.2.2.1
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hratio : 0 < (c.N1 : ℝ) / d.U := div_pos hN hU
  have hx := actual_xval hd c hh
  change epsilon a.2 * lambda d D a.1 * Real.exp (logV c a.1 h) = _ at hx
  calc
    _ = movingRatio d * (d.U / (c.N1 : ℝ)) *
        (epsilon a.2 * lambda d D a.1 * Real.exp (logV c a.1 h)) := by
      rw [Real.exp_sub, eta, Real.exp_log hratio]
      field_simp [hN.ne', hU.ne']
    _ = movingRatio d * (d.U / (c.N1 : ℝ)) *
        ((d.V / (c.L : ℝ)) * (h : ℝ)) := by rw [hx]
    _ = _ := (actual_slow_argument_eq_common_ratio hd c.hN1
      (cell_positive hd c).2.2.2.2.2.2 h).symm

lemma actual_slow_eq_phase {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    {Z : ℝ} {a : ℕ × Bool} {h : ℤ} (hh : h ∈ block d D Z a) :
    slow d c.N1 c.L h = Complex.exp (phaseArg (movingRatio d)
      (epsilon a.2) (lambda d D a.1) (eta d c.N1) (logV c a.1 h)) := by
  rw [actual_phase_normalization, actual_slow_argument hd c hh]
  simp only [slow, fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
  congr 1
  push_cast
  ring

/-- This is the actual imported amplitude API, including its h=0 gate. -/
lemma actual_amplitude_slow_eq {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    {Z : ℝ} {a : ℕ × Bool} {h : ℤ} (hh : h ∈ block d D Z a) :
    SharedGeneralDRowAdapter.amplitude d Z c.p c.r c.s c.w h * slow d c.N1 c.L h =
      ((d.V / (c.L : ℝ) : ℝ) : ℂ) *
        (Phi (xval (epsilon a.2) (lambda d D a.1) (logV c a.1 h)) *
          (poissonSmoothLowPass (xval (epsilon a.2) (lambda d D a.1)
            (logV c a.1 h) / Z) : ℂ) *
          Complex.exp (phaseArg (movingRatio d) (epsilon a.2) (lambda d D a.1)
            (eta d c.N1) (logV c a.1 h))) := by
  have hn := (block_facts hh).1
  rw [actual_xval hd c hh]
  unfold SharedGeneralDRowAdapter.amplitude
  dsimp only
  rw [if_neg hn, actual_slow_eq_phase hd c hh]
  simp only [Cell.L, Phi, Complex.real_smul]
  ring

/- The coefficient signature contains NO N1,p,r,s,w,h or future spectral variable. -/
def coeff (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) (k : ℤ × ℤ) : ℂ :=
  actualDoubleCoeff (movingRatio d) (epsilon a.2) (lambda d D a.1) Z k.1 k.2

def outerLog (d : MediumAtom) (p r w : ℕ) : ℝ :=
  Real.log (P d p) + Real.log (Rr d r) + Real.log (Ww d w)
def outerPhase (d : MediumAtom) (N1 p r w : ℕ) (k : ℤ × ℤ) : ℂ :=
  basis k.1 (eta d N1) * basis (-k.2) (outerLog d p r w)
def innerPhase (d : MediumAtom) (s : ℕ) (n : ℤ) : ℂ := basis (-n) (Real.log (Uu d s))
def hPhase (j : ℕ) (h n : ℤ) : ℂ := basis n (Real.log (|(h : ℝ)| / Hreal j))
def outerMultiplier (d : MediumAtom) (N1 p r w : ℕ) (k : ℤ × ℤ) : ℂ :=
  ((P d p * Rr d r * Ww d w)⁻¹ : ℝ) * outerPhase d N1 p r w k
def innerMultiplier (d : MediumAtom) (s : ℕ) (n : ℤ) : ℂ :=
  ((Uu d s)⁻¹ : ℝ) * innerPhase d s n
def hMode (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) (h n : ℤ) : ℂ :=
  if h ∈ block d D Z a then hPhase a.1 h n else 0
def modeTerm {d : MediumAtom} {D : ℕ} (Z : ℝ) (a : ℕ × Bool)
    (c : Cell d D) (h : ℤ) (k : ℤ × ℤ) : ℂ :=
  (base d D : ℂ) * coeff d D Z a k * outerMultiplier d c.N1 c.p c.r c.w k *
    innerMultiplier d c.s k.2 * hMode d D Z a h k.2

lemma basis_add_real (n : ℤ) (x y : ℝ) : basis n (x + y) = basis n x * basis n y := by
  simp only [basis, fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma basis_sub_real (n : ℤ) (x y : ℝ) : basis n (x - y) = basis n x * basis (-n) y := by
  simp only [basis, fourier_coe_apply, Int.cast_neg]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma log_product_split {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) :
    Real.log (product c) = outerLog d c.p c.r c.w + Real.log (Uu d c.s) := by
  obtain ⟨hp, hr, hs, hw, _⟩ := cell_ratios hd c
  have hp0 := (zero_lt_one.trans_le hp.1).ne'
  have hr0 := (zero_lt_one.trans_le hr.1).ne'
  have hs0 := (zero_lt_one.trans_le hs.1).ne'
  have hw0 := (zero_lt_one.trans_le hw.1).ne'
  unfold product outerLog
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero hp0 hr0) hs0) hw0,
    Real.log_mul (mul_ne_zero hp0 hr0) hs0, Real.log_mul hp0 hr0]
  ring

lemma mode_phase_split {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    (j : ℕ) (h : ℤ) (k : ℤ × ℤ) :
    basis k.1 (eta d c.N1) * basis k.2 (logV c j h) =
      outerPhase d c.N1 c.p c.r c.w k * innerPhase d c.s k.2 * hPhase j h k.2 := by
  rw [logV, log_product_split hd c, basis_sub_real, basis_add_real]
  unfold outerPhase innerPhase hPhase
  ring

lemma actual_T_split {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) :
    d.V / (c.L : ℝ) = base d D * (P d c.p * Rr d c.r * Ww d c.w)⁻¹ * (Uu d c.s)⁻¹ := by
  rw [actual_T_normalization hd c]
  unfold product
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual pointwise term, with COMMON coefficients and COMMON h mode. -/
theorem actual_amplitude_slow_hasSum {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    (b : ℕ) (Z : ℝ) (_hZ : 0 < Z) (a : ℕ × Bool) (h : ℤ)
    (hh : h ∈ block d D Z a) :
    HasSum (fun k : ℤ × ℤ => modeTerm Z a c h k)
      (SharedGeneralDRowAdapter.amplitude d Z c.p c.r c.s c.w h * slow d c.N1 c.L h) := by
  have hG := actual_physical_reconstruction b (movingRatio d) (epsilon_abs a.2)
    (physical_lambda_pos hd c a.1).le Z (eta d c.N1) (logV c a.1 h)
      (actual_eta_range hd c.hN1) (actual_v_range hd c hh)
  have hscaled := hG.mul_left ((d.V / (c.L : ℝ) : ℝ) : ℂ)
  rw [← actual_amplitude_slow_eq hd c hh] at hscaled
  have hterm (k : ℤ × ℤ) :
      ((d.V / (c.L : ℝ) : ℝ) : ℂ) *
        (actualDoubleCoeff (movingRatio d) (epsilon a.2) (lambda d D a.1) Z k.1 k.2 *
          basis k.1 (eta d c.N1) * basis k.2 (logV c a.1 h)) = modeTerm Z a c h k := by
    rw [actual_T_split hd c]
    have hp := mode_phase_split hd c a.1 h k
    unfold modeTerm outerMultiplier innerMultiplier hMode
    rw [if_pos hh]
    simp only [coeff, Complex.ofReal_mul]
    calc
      _ = (base d D : ℂ) * (actualDoubleCoeff (movingRatio d) (epsilon a.2)
          (lambda d D a.1) Z k.1 k.2) *
          (((P d c.p * Rr d c.r * Ww d c.w)⁻¹ : ℝ) : ℂ) * (((Uu d c.s)⁻¹ : ℝ) : ℂ) *
          (basis k.1 (eta d c.N1) * basis k.2 (logV c a.1 h)) := by ring
      _ = _ := by rw [hp]; ring
  simpa only [hterm] using hscaled

/-- Direct original-label intake, not merely a reconstruction theorem for G. -/
theorem original_carrier_amplitude_slow_hasSum
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (b : ℕ) (Z : ℝ) (hZ : 0 < Z)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) (u : ℕ × ℤ)
    (ho : o ∈ d.smallCoreSquaredOuterCarrier)
    (hu : u ∈ d.smallCoreSquaredInnerCarrier Z o)
    (hgcd : (o.2.1.1 * u.1).gcd (o.2.1.2.1 * o.2.1.2.2) = o.2.2)
    (a : ℕ × Bool) (hh : u.2 ∈ block d o.2.2 Z a) :
    HasSum (fun k : ℤ × ℤ => modeTerm Z a (Cell.ofOriginal d Z o u ho hu hgcd) u.2 k)
      (SharedGeneralDRowAdapter.amplitude d Z o.1.1 o.2.1.1 u.1
          (o.2.1.2.1 * o.2.1.2.2) u.2 *
        slow d o.1.2.1 ((o.1.1 * (o.2.1.1 * u.1)).lcm
          (o.1.1 * (o.2.1.2.1 * o.2.1.2.2))) u.2) := by
  exact actual_amplitude_slow_hasSum hd (Cell.ofOriginal d Z o u ho hu hgcd) b Z hZ a u.2 hh

lemma norm_outerPhase (d : MediumAtom) (N1 p r w : ℕ) (k : ℤ × ℤ) :
    ‖outerPhase d N1 p r w k‖ = 1 := by simp only [outerPhase, norm_mul, norm_basis, mul_one]
lemma norm_innerPhase (d : MediumAtom) (s : ℕ) (n : ℤ) : ‖innerPhase d s n‖ = 1 := norm_basis _ _
lemma norm_hPhase (j : ℕ) (h n : ℤ) : ‖hPhase j h n‖ = 1 := norm_basis _ _

/-- Multiplication by the ACTUAL common unit phase preserves any beta norm. -/
lemma norm_beta_mul_innerPhase (d : MediumAtom) (s : ℕ) (n : ℤ) (beta : ℂ) :
    ‖beta * innerPhase d s n‖ = ‖beta‖ := by rw [norm_mul, norm_innerPhase, mul_one]

theorem finite_beta_phase_energy (d : MediumAtom) (S : Finset ℕ) (beta : ℕ → ℂ) (n : ℤ) :
    (∑ s ∈ S, ‖beta s * innerPhase d s n‖ ^ 2) = ∑ s ∈ S, ‖beta s‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro s hs
  rw [norm_beta_mul_innerPhase]

lemma norm_hMode_le (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) (h n : ℤ) :
    ‖hMode d D Z a h n‖ ≤ 1 := by
  unfold hMode
  split_ifs
  · exact (norm_hPhase _ _ _).le
  · simp only [norm_zero, zero_le_one]

lemma multipliers_norm_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) (k : ℤ × ℤ) :
    ‖outerMultiplier d c.N1 c.p c.r c.w k‖ ≤ 1 ∧ ‖innerMultiplier d c.s k.2‖ ≤ 1 := by
  obtain ⟨hp, hr, hs, hw, _⟩ := cell_ratios hd c
  have hpr := interval_mul hp hr
  have hout := interval_mul hpr hw
  have ho0 : 0 < P d c.p * Rr d c.r * Ww d c.w := zero_lt_one.trans_le hout.1
  have hi0 : 0 < Uu d c.s := zero_lt_one.trans_le hs.1
  have ho : (P d c.p * Rr d c.r * Ww d c.w)⁻¹ ≤ (1 : ℝ) := by
    simpa only [one_div] using (div_le_one ho0).mpr hout.1
  have hi : (Uu d c.s)⁻¹ ≤ (1 : ℝ) := by
    simpa only [one_div] using (div_le_one hi0).mpr hs.1
  constructor
  · simpa only [outerMultiplier, norm_mul, norm_outerPhase, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ho0.le)] using ho
  · simpa only [innerMultiplier, norm_mul, norm_innerPhase, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hi0.le)] using hi

lemma common_gamma_inner_norm_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D) (n : ℤ) :
    ‖d.gamma2 c.s * innerMultiplier d c.s n‖ ≤ 1 := by
  have hg : ‖d.gamma2 c.s‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h2, _⟩ := hd
    exact (h2 c.s c.hs).1
  have hi := (multipliers_norm_le hd c (0, n)).2
  rw [norm_mul]
  exact (mul_le_mul hg hi (norm_nonneg _) zero_le_one).trans_eq (by ring)

/-- The quotient t carries the common s=q*t mode; no r is frozen into it. -/
lemma common_qt_inner (d : MediumAtom) (q t : ℕ) (n : ℤ) :
    innerMultiplier d (q * t) n =
      ((((q : ℝ) * (t : ℝ) / d.Q2)⁻¹ : ℝ) : ℂ) *
        basis (-n) (Real.log ((q : ℝ) * (t : ℝ) / d.Q2)) := by
  simp only [innerMultiplier, innerPhase, Uu, Nat.cast_mul]

/-- First retain the exact fourth-power residue cost, before any ledger debit. -/
theorem coeff_l1_fourth {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (b D : ℕ) (Z : ℝ) (hZ : 0 < Z) (a : ℕ × Bool) :
    Summable (fun k : ℤ × ℤ => ‖coeff d D Z a k‖) ∧
      (∑' k : ℤ × ℤ, ‖coeff d D Z a k‖) ≤
        fourierCost b * (1 + |movingRatio d|) ^ 4 / (1 + lambda d D a.1) ^ b := by
  have hlambda : 0 ≤ lambda d D a.1 := mul_nonneg (base_nonneg hd D) (Hreal_pos a.1).le
  simpa only [coeff] using actual_doubleCoeff_l1 b (movingRatio d)
    (epsilon_abs a.2) hlambda Z hZ

/-- Alternative bound on that SAME norm: the original SINGLE five-kappa debit. -/
theorem coeff_l1_original_five {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hkappa : 0 ≤ kappa)
    (b D : ℕ) (Z : ℝ) (hZ : 0 < Z) (a : ℕ × Bool) :
    Summable (fun k : ℤ × ℤ => ‖coeff d D Z a k‖) ∧
      (∑' k : ℤ × ℤ, ‖coeff d D Z a k‖) ≤
        16 * fourierCost b * d.scale ^ (5 * kappa) / (1 + lambda d D a.1) ^ b := by
  have hlambda : 0 ≤ lambda d D a.1 := mul_nonneg (base_nonneg hd D) (Hreal_pos a.1).le
  simpa only [coeff] using actual_atom_doubleCoeff_l1 b hd hkappa (epsilon_abs a.2) hlambda Z hZ

lemma modeTerm_norm_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    (Z : ℝ) (a : ℕ × Bool) (h : ℤ) (k : ℤ × ℤ) :
    ‖modeTerm Z a c h k‖ ≤ base d D * ‖coeff d D Z a k‖ := by
  have hmult := multipliers_norm_le hd c k
  have hh := norm_hMode_le d D Z a h k.2
  have hb := base_nonneg hd D
  unfold modeTerm
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (base_nonneg hd D)]
  calc
    _ ≤ ((base d D * ‖coeff d D Z a k‖) * 1 * 1) * 1 := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hmult.1 (mul_nonneg (base_nonneg hd D) (norm_nonneg _)))
          hmult.2 (norm_nonneg _) (by positivity))
        hh (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_mode_l1 {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hkappa : 0 ≤ kappa)
    {D : ℕ} (c : Cell d D) (b : ℕ) (Z : ℝ) (hZ : 0 < Z) (a : ℕ × Bool) (h : ℤ) :
    Summable (fun k : ℤ × ℤ => ‖modeTerm Z a c h k‖) ∧
      (∑' k : ℤ × ℤ, ‖modeTerm Z a c h k‖) ≤
        base d D * (16 * fourierCost b * d.scale ^ (5 * kappa) /
          (1 + lambda d D a.1) ^ b) := by
  obtain ⟨hc, hcost⟩ := coeff_l1_original_five hd hkappa b D Z hZ a
  have hmajor := hc.mul_left (base d D)
  have hbound := modeTerm_norm_le hd c Z a h
  have hs := hmajor.of_nonneg_of_le (fun k => norm_nonneg _) hbound
  refine ⟨hs, (hasSum_le hbound hs.hasSum hmajor.hasSum).trans ?_⟩
  rw [hc.tsum_mul_left (base d D)]
  exact mul_le_mul_of_nonneg_left hcost (base_nonneg hd D)

lemma conjugate_basis (n : ℤ) (x : ℝ) : (starRingEnd ℂ) (basis n x) = basis (-n) x := by
  exact fourier_neg.symm

/-- The negative real-projection branch conjugates the amplitude/slow modes,
not gamma. The common h mode gets the exact opposite Fourier sign. -/
lemma conjugate_hMode (d : MediumAtom) (D : ℕ) (Z : ℝ)
    (a : ℕ × Bool) (h n : ℤ) : (starRingEnd ℂ) (hMode d D Z a h n) = hMode d D Z a h (-n) := by
  unfold hMode hPhase
  split_ifs
  · exact conjugate_basis _ _
  · exact map_zero _

theorem actual_amplitude_slow_conjugate_hasSum
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    (b : ℕ) (Z : ℝ) (hZ : 0 < Z) (a : ℕ × Bool) (h : ℤ)
    (hh : h ∈ block d D Z a) :
    HasSum (fun k : ℤ × ℤ => (starRingEnd ℂ) (modeTerm Z a c h k))
      ((starRingEnd ℂ) (SharedGeneralDRowAdapter.amplitude d Z c.p c.r c.s c.w h *
        slow d c.N1 c.L h)) := by
  have hs := actual_amplitude_slow_hasSum hd c b Z hZ a h hh
  exact Complex.conjCLE.toContinuousLinearMap.hasSum hs

theorem conjugate_coeff_l1_same_cost (d : MediumAtom) (D : ℕ) (Z : ℝ) (a : ℕ × Bool) :
    (fun k : ℤ × ℤ => ‖(starRingEnd ℂ) (coeff d D Z a k)‖) = (fun k => ‖coeff d D Z a k‖) := by
  funext k
  exact norm_conj _

/-- A genuine finite exchange for any finite family of ACTUAL labelled cells
in one fixed D/sign/dyadic block. The coefficient family remains common. -/
theorem finite_actual_hasSum {ι : Type*} {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D b : ℕ) (Z : ℝ) (hZ : 0 < Z)
    (a : ℕ × Bool) (S : Finset ι) (cells : ι → Cell d D) (freq : ι → ℤ)
    (hfreq : ∀ i ∈ S, freq i ∈ block d D Z a) :
    HasSum (fun k : ℤ × ℤ => (base d D : ℂ) * coeff d D Z a k *
      ∑ i ∈ S, outerMultiplier d (cells i).N1 (cells i).p (cells i).r (cells i).w k *
        innerMultiplier d (cells i).s k.2 * hMode d D Z a (freq i) k.2)
      (∑ i ∈ S, SharedGeneralDRowAdapter.amplitude d Z (cells i).p (cells i).r
        (cells i).s (cells i).w (freq i) * slow d (cells i).N1 (cells i).L (freq i)) := by
  have hh := hasSum_sum (s := S) (fun i hi =>
    actual_amplitude_slow_hasSum hd (cells i) b Z hZ a (freq i) (hfreq i hi))
  convert hh using 1
  funext k
  simp only [Finset.mul_sum, modeTerm]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The original complex gamma remains OUTSIDE the original real projection.
E denotes a fixed remaining original character. This algebraic consumer does
not assert the independent root/reciprocal arithmetic dictionary or an energy. -/
theorem actual_gamma_real_hasSum {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {D : ℕ} (c : Cell d D)
    (b : ℕ) (Z : ℝ) (hZ : 0 < Z) (a : ℕ × Bool) (h : ℤ)
    (hh : h ∈ block d D Z a) (E : ℂ) :
    HasSum (fun k : ℤ × ℤ => d.gamma2 c.s * (((modeTerm Z a c h k * E).re : ℝ) : ℂ))
      (d.gamma2 c.s * (((SharedGeneralDRowAdapter.amplitude d Z c.p c.r c.s c.w h *
        slow d c.N1 c.L h * E).re : ℝ) : ℂ)) := by
  have hs := (actual_amplitude_slow_hasSum hd c b Z hZ a h hh).mul_right E
  let realEmbed : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have hre := hs.map realEmbed.toAddMonoidHom realEmbed.continuous
  change HasSum (fun k : ℤ × ℤ => (((modeTerm Z a c h k * E).re : ℝ) : ℂ))
    (((SharedGeneralDRowAdapter.amplitude d Z c.p c.r c.s c.w h *
      slow d c.N1 c.L h * E).re : ℝ) : ℂ) at hre
  exact hre.mul_left (d.gamma2 c.s)

/- Z<=0 is a ZERO FINITE ROW because the ORIGINAL finite frequency window is
empty. The individual amplitude at Z=0 is NOT falsely asserted to be zero. -/
lemma frequency_bound_zero_of_nonpos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (D : ℕ) {Z : ℝ} (hZ : Z ≤ 0) :
    d.sharedSmoothFrequencyBound Z D = 0 := by
  unfold MediumAtom.sharedSmoothFrequencyBound
  apply Nat.ceil_eq_zero.mpr
  have hQ : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
  have hK : 0 ≤ 64 * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 := by positivity
  have hnum : 64 * Z * d.Q1 * d.Q3 ^ 2 * d.Q2 ^ 2 ≤ 0 := by
    have ht := mul_nonpos_of_nonpos_of_nonneg hZ hK
    nlinarith [ht]
  rw [div_eq_mul_inv]
  exact mul_nonpos_of_nonpos_of_nonneg hnum
    (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg D) (by linarith [hd.2.1])))

lemma original_innerCarrier_empty_of_nonpos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) {Z : ℝ} (hZ : Z ≤ 0) :
    d.smallCoreSquaredInnerCarrier Z o = ∅ := by
  simp only [MediumAtom.smallCoreSquaredInnerCarrier,
    frequency_bound_zero_of_nonpos hd o.2.2 hZ, poissonNonzeroFrequencyWindow]
  norm_num

theorem original_row_sum_zero_of_nonpos {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (o : (ℕ × ℕ × ℕ) × ((ℕ × ℕ × ℕ) × ℕ)) {Z : ℝ} (hZ : Z ≤ 0) :
    (∑ u ∈ d.smallCoreSquaredInnerCarrier Z o, d.smallCoreSquaredRowTerm Z o u) = 0 := by
  rw [original_innerCarrier_empty_of_nonpos hd o hZ]
  exact Finset.sum_empty

/- Exact remaining interfaces: instantiate Cell with the original outer/inner
membership and its actual gcd gate; the remaining original character E is
handled by the independent root/reciprocal dictionary. Its arbitrary beta
energy and the original 7/32 spectral return are NOT analytic consequences.
All pure phases above have norm exactly1. Only the displayed reciprocal
geometric weights and the exact finite block indicator have norm at most1.
The coefficients use one actual mixed22 bound and one original 5*kappa debit.
The physical Cell makes D>0, hence lambda>0. Analytic lambda=0 exists in the
parent, but no fictitious physical zero/sign block is introduced here.
-/

end P3ActualLogAdapterSourceOnly
end
/-!
SOURCEONLY / UNCOMPILED companion. Load after the separated-row matcher and
the EXACT literal log adapter 08300fa322809ea6bc2eec7d170beb3b682ecbc9cde78a34a493e2ad5bfbb2d6.
This supplies CONCRETE instances of alpha,W,omega and the common coefficient;
none is a caller-supplied row-descent hypothesis. Every normalized-cell field
is obtained from the ORIGINAL fixedSlice and original normalized t carrier.
-/
namespace ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly
noncomputable section
open Classical Finset GeneralDGateNormalization
open GeneralDActivePairCountSourceOnly GeneralDActiveOuterEnergySourceOnly
open ActualFixedFeaturePacketPushforwardSourceOnly ActualSeparatedRowPacketMatchSourceOnly
open CommonSmoothCutoff
open scoped BigOperators FourierTransform

abbrev LogCell := _root_.P3ActualLogAdapterSourceOnly.Cell

/-- Actual log-analytic cell, constructed from the exact normalized carrier.
There is no independently assumed real coordinate rectangle or phase identity. -/
def normalizedCell (e : MediumAtom)
    (_hN : 1 ≤ e.U) (_hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (_hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (_hg : 0 < g) (_hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1) : LogCell e D := by
  refine {
    p := o.1.1, r := o.2.1.1, s := quotient o.2.1.1 D * t,
    r' := o.2.1.2.1, s' := o.2.1.2.2, N1 := o.1.2.1,
    hp := ?_, hr := ?_, hs := ?_, hr' := ?_, hs' := ?_, hN1 := ?_, hgcd := ?_ }
  · exact (fixedSlice_facts e Yb Ys D delta g l ho).1
  · exact (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.1
  · have hr := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.1
    have hq := (quotient_data (factorCarrier_bounds hR hr).1 hD).1
    exact ((mem_normalizedCarrier hq).mp ht).1
  · exact (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.2.1
  · exact (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.2.2.1
  · exact (fixedSlice_facts e Yb Ys D delta g l ho).2.1
  · obtain ⟨_hp, _hN1, _hN2, hr, _hrp, _hsp, _hne, _hDo, _hd, _hgc,
        _hsup, hDw, hgate⟩ := fixedSlice_facts e Yb Ys D delta g l ho
    have hrpos := (factorCarrier_bounds hR hr).1
    have hq := (quotient_data hrpos hD).1
    have hunit := ((mem_normalizedCarrier hq).mp ht).2
    have hG : originalGate o.1.1 o.2.1.1 (o.2.1.2.1 * o.2.1.2.2)
        D o.1.2.1 o.1.2.2 (quotient o.2.1.1 D * t) := by
      apply (originalGate_iff hrpos hD hDw).mpr
      exact ⟨dvd_mul_right _ _, hgate,
        by simpa only [Nat.mul_div_cancel_left t hq] using hunit⟩
    exact hG.1

/-- The six actual Nat labels are unchanged by the proof-field construction. -/
private theorem normalizedCell_labels (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1) :
    let c := normalizedCell e hN hQ hR hS Yb Ys hD hg hl ho ht
    c.p = o.1.1 ∧ c.r = o.2.1.1 ∧ c.s = quotient o.2.1.1 D * t ∧
      c.r' = o.2.1.2.1 ∧ c.s' = o.2.1.2.2 ∧ c.N1 = o.1.2.1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def modeProduct (e : MediumAtom) (D : ℕ) (Z : ℝ) (tag : ℕ × Bool)
    (m : ℤ × ℤ) (o : OuterIndex) (s : ℕ) (h : ℤ) : ℂ :=
  (_root_.P3ActualLogAdapterSourceOnly.base e D : ℂ) *
    _root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m *
    _root_.P3ActualLogAdapterSourceOnly.outerMultiplier e o.1.2.1 o.1.1 o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) m *
    _root_.P3ActualLogAdapterSourceOnly.innerMultiplier e s m.2 *
    _root_.P3ActualLogAdapterSourceOnly.hMode e D Z tag h m.2

/-- This is literally the named analytic adapter's modeTerm, not a replacement
amplitude manufactured for the packet argument. -/
theorem modeTerm_normalizedCell (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1)
    (Z : ℝ) (tag : ℕ × Bool) (h : ℤ) (m : ℤ × ℤ) :
    _root_.P3ActualLogAdapterSourceOnly.modeTerm Z tag
      (normalizedCell e hN hQ hR hS Yb Ys hD hg hl ho ht) h m =
      modeProduct e D Z tag m o (quotient o.2.1.1 D * t) h := by
  let c := normalizedCell e hN hQ hR hS Yb Ys hD hg hl ho ht
  obtain ⟨hp, hr, hs, hrp, hsp, hN1⟩ :=
    normalizedCell_labels e hN hQ hR hS Yb Ys hD hg hl ho ht
  have hw : _root_.P3ActualLogAdapterSourceOnly.Cell.w c =
      o.2.1.2.1 * o.2.1.2.2 := congrArg₂ Nat.mul hrp hsp
  have hout : _root_.P3ActualLogAdapterSourceOnly.outerMultiplier e c.N1 c.p c.r
      (_root_.P3ActualLogAdapterSourceOnly.Cell.w c) m =
      _root_.P3ActualLogAdapterSourceOnly.outerMultiplier e o.1.2.1 o.1.1 o.2.1.1
        (o.2.1.2.1 * o.2.1.2.2) m := by
    rw [hN1, hp, hr, hw]
  exact congrArg₂ (fun outer inner : ℂ =>
    (_root_.P3ActualLogAdapterSourceOnly.base e D : ℂ) *
      _root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m * outer * inner *
      _root_.P3ActualLogAdapterSourceOnly.hMode e D Z tag h m.2) hout
    (congrArg (fun s : ℕ => _root_.P3ActualLogAdapterSourceOnly.innerMultiplier e s m.2) hs)

def modeCoefficient (e : MediumAtom) (D : ℕ) (Z : ℝ) (tag : ℕ × Bool)
    (m : ℤ × ℤ) (negative : Bool) : ℂ :=
  branch negative ((_root_.P3ActualLogAdapterSourceOnly.base e D : ℂ) *
    _root_.P3ActualLogAdapterSourceOnly.coeff e D Z tag m)

def modeAlpha (e : MediumAtom) (m : ℤ × ℤ) (negative : Bool) (o : OuterIndex) : ℂ :=
  branch negative (_root_.P3ActualLogAdapterSourceOnly.outerMultiplier e o.1.2.1 o.1.1
    o.2.1.1 (o.2.1.2.1 * o.2.1.2.2) m)

def modeW (e : MediumAtom) (m : ℤ × ℤ) (negative : Bool) (s : ℕ) : ℂ :=
  e.gamma2 s * branch negative (_root_.P3ActualLogAdapterSourceOnly.innerMultiplier e s m.2)

def modeOmega (e : MediumAtom) (D : ℕ) (Z : ℝ) (tag : ℕ × Bool)
    (m : ℤ × ℤ) (negative : Bool) (h : ℤ) : ℂ :=
  branch negative (_root_.P3ActualLogAdapterSourceOnly.hMode e D Z tag h m.2)

theorem concrete_mode_term_factorization (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (o : OuterIndex) (s : ℕ) (h : ℤ) :
    e.gamma2 s * branch negative (modeProduct e D Z tag m o s h *
      strippedPhase e.residue o s h) =
      modeCoefficient e D Z tag m negative * modeAlpha e m negative o *
        (modeW e m negative s * modeOmega e D Z tag m negative h *
          branch negative (strippedPhase e.residue o s h)) := by
  unfold modeProduct modeCoefficient modeAlpha modeW modeOmega
  simp only [branch_mul]
  ring

/-- One genuine Fourier mode of the gamma2-outside-Re row, after its physical
slow factor has been included in the analytic symbol. H is still the original
finite signed window (or any exact common subblock); no frequency is merged. -/
def actualModeRow {g l : ℕ} (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (k : ZMod (g * l)) (H : Finset ℤ) (o : OuterIndex) : ℂ :=
  ∑ t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1,
    ∑ h ∈ H, if (h : ZMod (g * l)) = k then
      e.gamma2 (quotient o.2.1.1 D * t) *
        branch negative (modeProduct e D Z tag m o (quotient o.2.1.1 D * t) h *
          strippedPhase e.residue o (quotient o.2.1.1 D * t) h) else 0

theorem actualModeRow_eq_literalMode {g l : ℕ} (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (k : ZMod (g * l)) (H : Finset ℤ) (o : OuterIndex) :
    actualModeRow e D Z tag m negative k H o =
      modeCoefficient e D Z tag m negative * modeAlpha e m negative o *
        literalMode e D e.residue negative (modeW e m negative)
          (modeOmega e D Z tag m negative) H k o := by
  unfold actualModeRow literalMode
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  by_cases hh : (h : ZMod (g * l)) = k
  · simp only [if_pos hh]
    exact concrete_mode_term_factorization e D Z tag m negative o _ h
  · simp only [if_neg hh, mul_zero]

/-- Concrete actual-Fourier-mode to packet-J equality, with NO descent
assumption. Only the named common coefficient and genuine outer alpha remain. -/
theorem actualModeRow_eq_packetJ (e : MediumAtom)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} [NeZero (g * l)]
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (k : ZMod (g * l)) (H : Finset ℤ) :
    actualModeRow e D Z tag m negative k H o =
      modeCoefficient e D Z tag m negative * modeAlpha e m negative o *
        packetJ e D delta g l e.residue negative (rootFeature D delta g l o) k
          (modeW e m negative) (modeOmega e D Z tag m negative) H
            (packetKey D delta g l o) := by
  rw [actualModeRow_eq_literalMode,
    literalMode_eq_packetJ e hN hQ hR hS Yb Ys hD hg hl ho]

/-- The actual gamma remains outside both branches of the real projection. -/
theorem gamma_real_two_branches (gamma z : ℂ) :
    gamma * ((z.re : ℝ) : ℂ) =
      (gamma * branch false z + gamma * branch true z) / 2 := by
  change gamma * ((z.re : ℝ) : ℂ) = (gamma * z + gamma * (starRingEnd ℂ) z) / 2
  rw [Complex.re_eq_add_conj]
  ring

/-- The original low-pass/Poisson payload, not a newly postulated row. -/
theorem literalPayload_eq_amplitude_crt (e : MediumAtom) (Z : ℝ)
    (o : OuterIndex) (s : ℕ) (h : ℤ) :
    literalPayload e Z o s h = e.gamma2 s *
      (((SharedGeneralDRowAdapter.amplitude e Z o.1.1 o.2.1.1 s
        (o.2.1.2.1 * o.2.1.2.2) h * crtPhase e.residue o s h).re : ℝ) : ℂ) := by
  unfold literalPayload SharedGeneralDRowAdapter.amplitude crtPhase literalLcm
  dsimp only
  by_cases hh : h = 0
  · simp only [hh, poissonNonzeroFrequency_zero, if_true, mul_zero, zero_mul]
  · simp only [poissonNonzeroFrequency, if_neg hh, mul_assoc]

/-- Direct reconstruction of one ORIGINAL payload from the named parent's
actual modeTerm. The whole slow factor is restored exactly, before Re. -/
theorem actual_payload_mode_hasSum
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    {t : ℕ} (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1)
    (b : ℕ) (Z : ℝ) (hZ : 0 < Z) (tag : ℕ × Bool) (h : ℤ)
    (hh : h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag) :
    HasSum (fun m : ℤ × ℤ => e.gamma2 (quotient o.2.1.1 D * t) *
      (((modeProduct e D Z tag m o (quotient o.2.1.1 D * t) h *
        strippedPhase e.residue o (quotient o.2.1.1 D * t) h).re : ℝ) : ℂ))
      (literalPayload e Z o (quotient o.2.1.1 D * t) h) := by
  let c := normalizedCell e hN hQ hR hS Yb Ys hD hg hl ho ht
  obtain ⟨hp, hr, hsCell, hrp, hsp, hN1⟩ :=
    normalizedCell_labels e hN hQ hR hS Yb Ys hD hg hl ho ht
  have hw : _root_.P3ActualLogAdapterSourceOnly.Cell.w c =
      o.2.1.2.1 * o.2.1.2.2 := congrArg₂ Nat.mul hrp hsp
  have hL : _root_.P3ActualLogAdapterSourceOnly.Cell.L c =
      literalLcm o (quotient o.2.1.1 D * t) :=
    congrArg₂ Nat.lcm (congrArg₂ Nat.mul hp (congrArg₂ Nat.mul hr hsCell))
      (congrArg₂ Nat.mul hp hw)
  have hslow : _root_.P3ActualLogAdapterSourceOnly.slow e c.N1
      (_root_.P3ActualLogAdapterSourceOnly.Cell.L c) h =
      slowPhase e.residue o (quotient o.2.1.1 D * t) h :=
    congrArg₂ (fun N L : ℕ => _root_.P3ActualLogAdapterSourceOnly.slow e N L h) hN1 hL
  have hs := _root_.P3ActualLogAdapterSourceOnly.actual_gamma_real_hasSum he
    c b Z hZ tag h hh (strippedPhase e.residue o (quotient o.2.1.1 D * t) h)
  have hmode (m : ℤ × ℤ) :
      e.gamma2 (quotient o.2.1.1 D * t) *
        (((modeProduct e D Z tag m o (quotient o.2.1.1 D * t) h *
          strippedPhase e.residue o (quotient o.2.1.1 D * t) h).re : ℝ) : ℂ) =
      e.gamma2 c.s *
        (((_root_.P3ActualLogAdapterSourceOnly.modeTerm Z tag c h m *
          strippedPhase e.residue o (quotient o.2.1.1 D * t) h).re : ℝ) : ℂ) := by
    rw [show _root_.P3ActualLogAdapterSourceOnly.modeTerm Z tag c h m =
        modeProduct e D Z tag m o (quotient o.2.1.1 D * t) h from
      modeTerm_normalizedCell e hN hQ hR hS Yb Ys hD hg hl ho ht Z tag h m,
      hsCell]
  have hlimit :
      e.gamma2 c.s *
        (((SharedGeneralDRowAdapter.amplitude e Z c.p c.r c.s
            (_root_.P3ActualLogAdapterSourceOnly.Cell.w c) h *
          _root_.P3ActualLogAdapterSourceOnly.slow e c.N1
            (_root_.P3ActualLogAdapterSourceOnly.Cell.L c) h *
          strippedPhase e.residue o (quotient o.2.1.1 D * t) h).re : ℝ) : ℂ) =
      literalPayload e Z o (quotient o.2.1.1 D * t) h := by
    rw [hsCell, hp, hr, hw, hslow, mul_assoc, slowPhase_mul_stripped,
      literalPayload_eq_amplitude_crt]
  exact hlimit ▸ hs.congr_fun hmode

def actualBlockRow {g l : ℕ} (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (k : ZMod (g * l)) (o : OuterIndex) : ℂ :=
  ∑ t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1,
    ∑ h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag,
      if (h : ZMod (g * l)) = k then
        literalPayload e Z o (quotient o.2.1.1 D * t) h else 0

def actualRealModeRow {g l : ℕ} (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (k : ZMod (g * l)) (o : OuterIndex) : ℂ :=
  ∑ t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1,
    ∑ h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag,
      if (h : ZMod (g * l)) = k then e.gamma2 (quotient o.2.1.1 D * t) *
        (((modeProduct e D Z tag m o (quotient o.2.1.1 D * t) h *
          strippedPhase e.residue o (quotient o.2.1.1 D * t) h).re : ℝ) : ℂ) else 0

theorem actualRealModeRow_eq_half_branches {g l : ℕ} (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (k : ZMod (g * l)) (o : OuterIndex) :
    actualRealModeRow e D Z tag m k o =
      (actualModeRow e D Z tag m false k
          (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) o +
        actualModeRow e D Z tag m true k
          (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) o) / 2 := by
  unfold actualRealModeRow actualModeRow
  simp only [← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro h _
  by_cases hh : (h : ZMod (g * l)) = k
  · simp only [if_pos hh]
    exact gamma_real_two_branches _ _
  · simp only [if_neg hh, add_zero, zero_div]

/-- The genuine finite row in one exact dyadic/residue block is reconstructed.
Both branches retain the SAME original gamma2 and every original t label. -/
theorem actualBlockRow_hasSum
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (b : ℕ) (Z : ℝ) (hZ : 0 < Z) (tag : ℕ × Bool) (k : ZMod (g * l)) :
    HasSum (fun m : ℤ × ℤ =>
      (actualModeRow e D Z tag m false k
          (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) o +
        actualModeRow e D Z tag m true k
          (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) o) / 2)
      (actualBlockRow e D Z tag k o) := by
  have hpoint (t : ℕ)
      (ht : t ∈ normalizedCarrier (factorCarrier e.Q2) o.2.1.1
        (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1)
      (h : ℤ) (hh : h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag) :
      HasSum (fun m : ℤ × ℤ => if (h : ZMod (g * l)) = k then
        e.gamma2 (quotient o.2.1.1 D * t) *
          (((modeProduct e D Z tag m o (quotient o.2.1.1 D * t) h *
            strippedPhase e.residue o (quotient o.2.1.1 D * t) h).re : ℝ) : ℂ) else 0)
        (if (h : ZMod (g * l)) = k then
          literalPayload e Z o (quotient o.2.1.1 D * t) h else 0) := by
    by_cases hhk : (h : ZMod (g * l)) = k
    · simpa only [if_pos hhk] using
        (actual_payload_mode_hasSum he hN hQ hR hS Yb Ys hD hg hl ho ht b Z hZ tag h hh)
    · simp only [if_neg hhk]
      exact hasSum_zero
  have hs := hasSum_sum
    (s := normalizedCarrier (factorCarrier e.Q2) o.2.1.1
      (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1) (fun t ht =>
    hasSum_sum (s := _root_.P3ActualLogAdapterSourceOnly.block e D Z tag) (hpoint t ht))
  change HasSum (fun m : ℤ × ℤ => actualRealModeRow e D Z tag m k o)
    (actualBlockRow e D Z tag k o) at hs
  simpa only [actualRealModeRow_eq_half_branches] using hs

/-- Actual row reconstruction followed by the constructed packet match.
There is NO hrow, support certificate, coefficient-norm or spectral premise. -/
theorem actualBlockRow_hasSum_packet
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (hN : 1 ≤ e.U) (hQ : 1 ≤ e.Q1) (hR : 1 ≤ e.Q3) (hS : 1 ≤ e.Q2)
    (Yb Ys : ℝ) {D delta g l : ℕ} [NeZero (g * l)]
    (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l)
    (b : ℕ) (Z : ℝ) (hZ : 0 < Z) (tag : ℕ × Bool) (k : ZMod (g * l)) :
    HasSum (fun m : ℤ × ℤ =>
      (modeCoefficient e D Z tag m false * modeAlpha e m false o *
        packetJ e D delta g l e.residue false (rootFeature D delta g l o) k
          (modeW e m false) (modeOmega e D Z tag m false)
          (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) (packetKey D delta g l o) +
      modeCoefficient e D Z tag m true * modeAlpha e m true o *
        packetJ e D delta g l e.residue true (rootFeature D delta g l o) k
          (modeW e m true) (modeOmega e D Z tag m true)
          (_root_.P3ActualLogAdapterSourceOnly.block e D Z tag) (packetKey D delta g l o)) / 2)
      (actualBlockRow e D Z tag k o) := by
  simpa only [actualModeRow_eq_packetJ e hN hQ hR hS Yb Ys hD hg hl ho] using
    (actualBlockRow_hasSum he hN hQ hR hS Yb Ys hD hg hl ho b Z hZ tag k)

/-- Exact finite decomposition of the LITERAL normalizedRow. Every original
signed frequency occurs once, in its real dyadicKey block and residue class.
No positive enlargement, shortened-window replacement or label erasure. -/
theorem normalizedRow_eq_blocks_residues (e : MediumAtom) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g * l)]
    {o : OuterIndex} (ho : o ∈ fixedSlice e Yb Ys D delta g l) (Z : ℝ) :
    normalizedRow e Z o =
      ∑ tag ∈ (_root_.P3ActualLogAdapterSourceOnly.window e D Z).image
        _root_.P3ActualLogAdapterSourceOnly.dyadicKey,
        ∑ k : ZMod (g * l), actualBlockRow e D Z tag k o := by
  have hDo := (fixedSlice_facts e Yb Ys D delta g l ho).2.2.2.2.2.2.2.1
  unfold normalizedRow
  rw [hDo]
  let T := normalizedCarrier (factorCarrier e.Q2) o.2.1.1
    (o.2.1.2.1 * o.2.1.2.2) D o.1.2.1
  let K := (_root_.P3ActualLogAdapterSourceOnly.window e D Z).image
    _root_.P3ActualLogAdapterSourceOnly.dyadicKey
  change (∑ t ∈ T, ∑ h ∈ _root_.P3ActualLogAdapterSourceOnly.window e D Z,
    literalPayload e Z o (quotient o.2.1.1 D * t) h) = _
  calc
    _ = ∑ t ∈ T, ∑ tag ∈ K,
        ∑ h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag,
        ∑ k : ZMod (g * l), if (h : ZMod (g * l)) = k then
          literalPayload e Z o (quotient o.2.1.1 D * t) h else 0 := by
      apply sum_congr rfl
      intro t _
      rw [_root_.P3ActualLogAdapterSourceOnly.sum_original_window_eq_blocks]
      simp [K]
    _ = ∑ tag ∈ K, ∑ k : ZMod (g * l), ∑ t ∈ T,
        ∑ h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag,
        if (h : ZMod (g * l)) = k then
          literalPayload e Z o (quotient o.2.1.1 D * t) h else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro tag _
      calc
        _ = ∑ t ∈ T, ∑ k : ZMod (g * l),
            ∑ h ∈ _root_.P3ActualLogAdapterSourceOnly.block e D Z tag,
            if (h : ZMod (g * l)) = k then
              literalPayload e Z o (quotient o.2.1.1 D * t) h else 0 := by
          apply sum_congr rfl
          intro t _
          exact sum_comm
        _ = _ := sum_comm
    _ = _ := rfl

end
end ImbalancedChen.Part3.ActualLogModePacketInstanceSourceOnly
