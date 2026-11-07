import ImbalancedChen.Part3ActualCompletedSquarePushforward
import ImbalancedChen.Part3ActualM2FinitePoissonAdapter
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.NumberTheory.Divisors

/-!
SOURCEONLY / UNCOMPILED. One finite zero-difference payment at the ACTUAL
completed-square stage. The zeroSource includes signed f!=0 and is kept
separate from all nonzero-y auxiliary-divisor norms and from Poisson m=0.
The fixed divisor envelope is defined on nonzero |h|*t. No Bnu, diagonal
budget, pointwise coefficient norm or carrier embedding is a final premise.
Only generic intermediate lemmas take elementary coefficient/finite-window
inputs; the actual mode theorem below proves those inputs from admissibility.
No actual/cache/frozen parent is modified and no compiler/checker is run.
-/
namespace ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly GeneralDRootResidueCostSourceOnly
open GeneralDActivePairCountSourceOnly
open scoped BigOperators SchwartzMap FourierTransform
attribute [local instance] Classical.propDecidable

-- The following divisor injection and the two signed-window facts are
-- reused verbatim from frozen 373ffcd5; no old k-split/amplitude prefix.
abbrev PairIndex := (ℕ × ℤ) × (ℕ × ℤ)

def zeroCross (T : Finset ℕ) (W : Finset ℤ) : Finset PairIndex :=
  ((T ×ˢ W) ×ˢ (T ×ˢ W)).filter
    (fun uv ↦ uv.1.2 * (uv.2.1 : ℤ) = uv.2.2 * (uv.1.1 : ℤ))

def tauEnvelope (T : Finset ℕ) (W : Finset ℤ) : ℕ :=
  (W ×ˢ T).sup (fun ht ↦ (ht.1.natAbs * ht.2).divisors.card)

/-- Nontrivial divisor-fibre count: fix (h,s') and encode s as a divisor
of the NONZERO |h*s'|; h' is then forced. No tau(0) is used. -/
theorem zeroCross_card_le (T : Finset ℕ) (W : Finset ℤ)
    (hT : ∀ t ∈ T, 0 < t) (hW : ∀ h ∈ W, h ≠ 0) :
    (zeroCross T W).card ≤ W.card * T.card * tauEnvelope T W := by
  let V := (W ×ˢ T).sigma (fun ht ↦ (ht.1.natAbs * ht.2).divisors)
  have hinj : (zeroCross T W).card ≤ V.card := by
    apply card_le_card_of_injOn
      (fun uv : PairIndex ↦ (⟨(uv.1.2, uv.2.1), uv.1.1⟩ : Σ _ : ℤ × ℕ, ℕ))
    · intro uv huv
      obtain ⟨huvI, heq⟩ := mem_filter.mp huv
      obtain ⟨hu, hv⟩ := mem_product.mp huvI
      have habs := congrArg Int.natAbs heq
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
      apply mem_sigma.mpr
      refine ⟨mem_product.mpr ⟨(mem_product.mp hu).2, (mem_product.mp hv).1⟩, ?_⟩
      apply Nat.mem_divisors.mpr
      refine ⟨?_, mul_ne_zero (Int.natAbs_ne_zero.mpr (hW _ (mem_product.mp hu).2))
        (hT _ (mem_product.mp hv).1).ne'⟩
      rw [habs]
      exact dvd_mul_left _ _
    · intro x hx y hy heq
      have hh : x.1.2 = y.1.2 := congrArg (fun q : Σ _ : ℤ × ℕ, ℕ ↦ q.1.1) heq
      have hsp : x.2.1 = y.2.1 := congrArg (fun q : Σ _ : ℤ × ℕ, ℕ ↦ q.1.2) heq
      have hs : x.1.1 = y.1.1 := congrArg (fun q : Σ _ : ℤ × ℕ, ℕ ↦ q.2) heq
      have hxe := (mem_filter.mp hx).2
      have hye := (mem_filter.mp hy).2
      have hyt := (mem_product.mp (mem_product.mp (mem_filter.mp hy).1).1).1
      have htn : (y.1.1 : ℤ) ≠ 0 := by exact_mod_cast (hT _ hyt).ne'
      have hm : x.2.2 * (y.1.1 : ℤ) = y.2.2 * (y.1.1 : ℤ) := by
        calc
          _ = x.1.2 * (x.2.1 : ℤ) := by simpa only [hs] using hxe.symm
          _ = y.1.2 * (y.2.1 : ℤ) := by rw [hh, hsp]
          _ = _ := hye
      exact Prod.ext (Prod.ext hs hh) (Prod.ext hsp (mul_right_cancel₀ htn hm))
  calc
    _ ≤ V.card := hinj
    _ = ∑ ht ∈ W ×ˢ T, (ht.1.natAbs * ht.2).divisors.card := card_sigma _ _
    _ ≤ ∑ _ht ∈ W ×ˢ T, tauEnvelope T W :=
      sum_le_sum (fun ht hht ↦ Finset.le_sup
        (f := fun ht : ℤ × ℕ ↦ (ht.1.natAbs * ht.2).divisors.card) hht)
    _ = _ := by rw [sum_const_nat (fun _ _ => rfl), card_product]

private theorem frequency_nonzero (H : ℕ) {h : ℤ}
    (hh : h ∈ poissonNonzeroFrequencyWindow H) : h ≠ 0 := by
  rcases mem_union.mp hh with hp | hn
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    exact_mod_cast hn0
  · obtain ⟨n, hnmem, rfl⟩ := mem_image.mp hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hnmem).1; omega
    exact neg_ne_zero.mpr (by exact_mod_cast hn0)

theorem frequency_card_le (H : ℕ) :
    (poissonNonzeroFrequencyWindow H).card ≤ 2 * H := by
  have hu := card_union_le ((Icc 1 H).image (fun n : ℕ ↦ (n : ℤ)))
    ((Icc 1 H).image (fun n : ℕ ↦ -(n : ℤ)))
  have hp : ((Icc 1 H).image (fun n : ℕ ↦ (n : ℤ))).card ≤ (Icc 1 H).card := card_image_le
  have hn : ((Icc 1 H).image (fun n : ℕ ↦ -(n : ℤ))).card ≤ (Icc 1 H).card := card_image_le
  simpa only [poissonNonzeroFrequencyWindow, Nat.card_Icc, Nat.add_sub_cancel] using
    hu.trans (show ((Icc 1 H).image (fun n : ℕ ↦ (n : ℤ))).card +
      ((Icc 1 H).image (fun n : ℕ ↦ -(n : ℤ))).card ≤ 2 * (Icc 1 H).card by omega)

private theorem factor_pos_small {S : ℝ} (hS : 0 < S) {t : ℕ}
    (ht : t ∈ factorCarrier S) : 0 < t := by
  have hceil : 0 < Nat.ceil S := Nat.ceil_pos.mpr hS
  exact hceil.trans_le (mem_Icc.mp ht).1

private theorem factor_card_small {S : ℝ} (hS : 0 < S) :
    ((factorCarrier S).card : ℝ) ≤ 2*S := by
  have hsub : factorCarrier S ⊆ Ioc 0 (Nat.floor (2*S)) := by
    intro t ht
    exact mem_Ioc.mpr ⟨factor_pos_small hS ht, (mem_Icc.mp ht).2⟩
  calc
    _ ≤ ((Ioc 0 (Nat.floor (2*S))).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = (Nat.floor (2*S) : ℝ) := by simp only [Nat.card_Ioc, Nat.sub_zero]
    _ ≤ _ := Nat.floor_le (by positivity)

def signedF (F : ℝ) : Finset ℤ :=
  (Icc (Int.ceil (-F)) (Int.floor F)).filter (fun f => f ≠ 0)

private theorem signedF_card_le {F : ℝ} (hF : 0 ≤ F) :
    ((signedF F).card : ℝ) ≤ 2*F := by
  have hsub : signedF F ⊆ nonzeroMultipleCarrier F 1 := by
    intro f hf
    obtain ⟨hf, hfn⟩ := mem_filter.mp hf
    apply mem_nonzeroMultipleCarrier Nat.zero_lt_one hfn
    · rw [natAbs_cast_real]
      exact actual_f_window_bound F hf
    · exact one_dvd f
  have hc : (signedF F).card ≤ 2 * Nat.floor F := by
    simpa only [Nat.cast_one, div_one] using
      (card_le_card hsub).trans (card_nonzeroMultipleCarrier_le F 1)
  calc
    _ ≤ 2*(Nat.floor F : ℝ) := by exact_mod_cast hc
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le hF) (by norm_num)

/-- The true source's f!=0 licenses k=0; no nu-divisibility is used. -/
theorem zeroSource_difference_eq_zero (A : ℕ) (a : ℤ) (T : Finset ℕ)
    (H : ℕ) (Fset : Finset ℤ) {s : Source}
    (hs : s ∈ zeroSource (carrier A a T H Fset)) :
    ActualReciprocalSquarePoissonSourceOnly.difference s.2.1 s.2.2 = 0 := by
  have hc := (mem_filter.mp hs).1
  have hf : s.1 ≠ 0 := (mem_filter.mp hc).2.1
  have hy := (mem_filter.mp hs).2
  change s.1 * ActualReciprocalSquarePoissonSourceOnly.difference s.2.1 s.2.2 = 0 at hy
  exact (mul_eq_zero.mp hy).resolve_left hf

private theorem zeroSource_subset (A : ℕ) (a : ℤ) (T : Finset ℕ)
    (H : ℕ) (F : ℝ) :
    zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))) ⊆
      signedF F ×ˢ zeroCross T (poissonNonzeroFrequencyWindow H) := by
  intro s hs
  have hc := (mem_filter.mp hs).1
  obtain ⟨hr, hg⟩ := mem_filter.mp hc
  obtain ⟨hf, hp⟩ := mem_product.mp hr
  have hk := zeroSource_difference_eq_zero A a T H _ hs
  change s.2.1.2*(s.2.2.1 : ℤ) - s.2.2.2*(s.2.1.1 : ℤ) = 0 at hk
  exact mem_product.mpr ⟨mem_filter.mpr ⟨hf,hg.1⟩,
    mem_filter.mpr ⟨hp,sub_eq_zero.mp hk⟩⟩

/-- Nontrivial LINEAR HS count; no second HS factor or count square. -/
theorem zeroSource_card_le_hsf (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    {S F : ℝ} (_hS : 0 ≤ S) (hF : 0 ≤ F)
    (hT : ∀ t ∈ T, 0 < t) (hTc : (T.card : ℝ) ≤ 2*S) :
    ((zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)))).card : ℝ) ≤
      8*F*(H : ℝ)*S*(tauEnvelope T (poissonNonzeroFrequencyWindow H) : ℝ) := by
  let W := poissonNonzeroFrequencyWindow H
  have hs : (zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)))).card ≤
      (signedF F).card * (zeroCross T W).card := by
    simpa only [card_product] using card_le_card (zeroSource_subset A a T H F)
  have hz := zeroCross_card_le T W hT (fun h hh => frequency_nonzero H hh)
  have hn := hs.trans (Nat.mul_le_mul_left (signedF F).card hz)
  have hc : ((zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)))).card : ℝ) ≤
      ((signedF F).card : ℝ) * ((W.card : ℝ)*(T.card : ℝ)*
        (tauEnvelope T W : ℝ)) := by exact_mod_cast hn
  have hW : (W.card : ℝ) ≤ 2*(H : ℝ) := by exact_mod_cast frequency_card_le H
  calc
    _ ≤ ((signedF F).card : ℝ) * ((W.card : ℝ)*(T.card : ℝ)*
        (tauEnvelope T W : ℝ)) := hc
    _ ≤ (2*F) * ((2*(H : ℝ))*(2*S)*(tauEnvelope T W : ℝ)) := by
      exact mul_le_mul (signedF_card_le hF)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hW hTc (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _))
        (by positivity) (by positivity)
    _ = _ := by dsimp only [W]; ring

private theorem norm_scaledCutoff (P x : ℝ) :
    ‖(scaledDyadicCutoff P x : ℂ)‖ = scaledDyadicCutoff P x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (scaledDyadicCutoff_nonneg P x)]

private theorem cutoff_support {P : ℝ} (hP : 0 < P) {n : ℕ}
    (hn : scaledDyadicCutoff P n ≠ 0) : n ∈ Ioc 0 (Nat.floor (3*P)) := by
  have hpsi : dyadicCutoffSchwartz ((n : ℝ)/P) ≠ 0 := by
    simpa only [dyadicCutoffSchwartz_apply, scaledDyadicCutoff, ne_eq,
      Complex.ofReal_eq_zero] using hn
  obtain ⟨_, hnpos, _, hhi⟩ := physical_cutoff_nonzero_nat_modulus hpsi
  exact mem_Ioc.mpr ⟨hnpos, Nat.le_floor (by linarith)⟩

/-- Positive smooth b/c mass; no translated-interval +1 at small scales. -/
private theorem cutoff_mass_le {P : ℝ} (hP : 0 < P) (I : Finset ℕ) :
    (∑ n ∈ I, ‖(scaledDyadicCutoff P n : ℂ)‖) ≤ 3*P := by
  let J : Finset ℕ := I.filter (fun n : ℕ => scaledDyadicCutoff P (n : ℝ) ≠ 0)
  have hJ : J ⊆ Ioc 0 (Nat.floor (3*P)) := by
    intro n hn
    exact cutoff_support hP (mem_filter.mp hn).2
  calc
    _ = ∑ n ∈ I, scaledDyadicCutoff P n := by simp only [norm_scaledCutoff]
    _ = ∑ n ∈ J, scaledDyadicCutoff P n := by
      dsimp only [J]
      simp only [sum_filter_ne_zero]
    _ ≤ ∑ _n ∈ J, (1 : ℝ) := sum_le_sum (fun n _ => scaledDyadicCutoff_le_one P n)
    _ = (J.card : ℝ) := by simp only [sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((Ioc 0 (Nat.floor (3*P))).card : ℝ) := by exact_mod_cast card_le_card hJ
    _ = (Nat.floor (3*P) : ℝ) := by simp only [Nat.card_Ioc, Nat.sub_zero]
    _ ≤ _ := Nat.floor_le (by positivity)

private theorem residuePhase_norm_le {c : ℕ} [NeZero c] (a y z : ℤ) (b : ℕ) :
    ‖OriginalSmoothPoissonTail.Physical.residuePhase a y z (b : ZMod c)‖ ≤ 1 := by
  unfold OriginalSmoothPoissonTail.Physical.residuePhase
  split_ifs
  · simp only [ZMod.stdAddChar_apply, Circle.norm_coe, le_refl]
  · simp only [norm_zero, zero_le_one]

/-- The FULL completed m series is bounded via its proved finite b identity.
No m=0 deletion or termwise unweighted m triangle estimate is used. -/
private theorem completed_frequency_norm_le {c : ℕ} [NeZero c]
    {M : ℝ} (hM : 0 < M) (a y : ℤ) (z : ℕ) (hz : c.Coprime z) :
    ‖∑' m : ℤ, frequency M c a y (z : ℤ) m‖ ≤ 3*M := by
  let I := Ioc 0 (Nat.floor (3*M))
  have hI : ∀ b : ℕ, scaledDyadicCutoff M b ≠ 0 → b ∈ I :=
    fun b hb => cutoff_support hM hb
  have hunit : IsUnit ((z : ℤ) : ZMod c) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime z c).mpr hz.symm
  rw [← OriginalSmoothPoissonTail.Physical.finiteKernel_poisson
    (c := c) hM I hI a y (z : ℤ) hunit]
  unfold OriginalSmoothPoissonTail.Physical.finiteKernel
  calc
    _ ≤ ∑ b ∈ I, ‖(scaledDyadicCutoff M b : ℂ) *
        OriginalSmoothPoissonTail.Physical.residuePhase a y (z : ℤ) (b : ZMod c)‖ := norm_sum_le _ _
    _ ≤ ∑ b ∈ I, ‖(scaledDyadicCutoff M b : ℂ)‖ := by
      apply sum_le_sum
      intro b _
      simpa only [norm_mul, mul_one] using mul_le_mul_of_nonneg_left
        (residuePhase_norm_le (c := c) a y (z : ℤ) b) (norm_nonneg (scaledDyadicCutoff M b : ℂ))
    _ ≤ _ := cutoff_mass_le hM I

/-- Uniform finite-kernel norm, in particular at y=0. -/
theorem completedKernel_norm_le {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (C : ℝ) (a : ℤ) (zy : Output) : ‖completedKernel M N C a zy‖ ≤ 9*M*N := by
  unfold completedKernel
  calc
    _ ≤ ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ‖if c.Coprime zy.1 then
        (scaledDyadicCutoff N c : ℂ) * ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ Ioc 0 (Nat.floor (10*C)), ‖(scaledDyadicCutoff N c : ℂ)‖*(3*M) := by
      apply sum_le_sum
      intro c hc
      let : NeZero c := ⟨(mem_Ioc.mp hc).1.ne'⟩
      by_cases hz : c.Coprime zy.1
      · rw [if_pos hz, norm_mul]
        exact mul_le_mul_of_nonneg_left
          (completed_frequency_norm_le (c := c) hM a zy.2 zy.1 hz) (norm_nonneg _)
      · rw [if_neg hz, norm_zero]
        positivity
    _ = (∑ c ∈ Ioc 0 (Nat.floor (10*C)), ‖(scaledDyadicCutoff N c : ℂ)‖)*(3*M) :=
      (sum_mul _ _ _).symm
    _ ≤ (3*N)*(3*M) := mul_le_mul_of_nonneg_right
      (cutoff_mass_le hN _) (by positivity)
    _ = _ := by ring

def zeroPiece (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N C F : ℝ) : ℂ :=
  let U := zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)))
  ∑ zy ∈ U.image output, beta U lambda omega zy * completedKernel M N C a zy

theorem zeroPiece_eq_source (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N C F : ℝ) :
    zeroPiece A a T H lambda omega M N C F =
      ∑ s ∈ zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))),
        weight lambda omega s * completedKernel M N C a (output s) := by
  unfold zeroPiece
  exact (weighted_pushforward _ _ _ _).symm

/-- Exact actual P3 split; the second summand is left unchanged. -/
theorem completedPiece_eq_zeroPiece_add_nonzero (A : ℕ) (a : ℤ)
    (T : Finset ℕ) (H : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    completedPiece A a T H lambda omega M N B C F =
      zeroPiece A a T H lambda omega M N C F +
        ∑ s ∈ nonzeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))),
          weight lambda omega s * completedKernel M N C a (output s) := by
  rw [completedPiece_eq_source, zeroPiece_eq_source]
  exact sum_zero_nonzero _ _

private theorem weight_norm_le (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (Fset : Finset ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hlambda : ∀ t ∈ T, ‖lambda t‖ ≤ 1)
    (homega : ∀ h ∈ poissonNonzeroFrequencyWindow H, ‖omega h‖ ≤ 1)
    {s : Source} (hs : s ∈ carrier A a T H Fset) : ‖weight lambda omega s‖ ≤ 1 := by
  have hp := (mem_product.mp (mem_filter.mp hs).1).2
  have h1 := (mem_product.mp hp).1
  have h2 := (mem_product.mp hp).2
  have atom_bound (u : Inner) (hu : u ∈ finiteInnerCarrier T H) :
      ‖atomCoeff lambda omega u‖ ≤ 1 := by
    have hu' := mem_product.mp hu
    rw [atomCoeff, norm_mul]
    exact (mul_le_mul (hlambda _ hu'.1) (homega _ hu'.2)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  change ‖atomCoeff lambda omega s.2.1 *
      star (atomCoeff lambda omega s.2.2)‖ ≤ 1
  rw [norm_mul, norm_star]
  exact (mul_le_mul (atom_bound _ h1) (atom_bound _ h2)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Generic finite step; the actual theorem below derives every norm/window input. -/
theorem zeroPiece_norm_le (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M N S F : ℝ} (C : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hS : 0 ≤ S) (hF : 0 ≤ F)
    (hT : ∀ t ∈ T, 0 < t) (hTc : (T.card : ℝ) ≤ 2*S)
    (hlambda : ∀ t ∈ T, ‖lambda t‖ ≤ 1)
    (homega : ∀ h ∈ poissonNonzeroFrequencyWindow H, ‖omega h‖ ≤ 1) :
    ‖zeroPiece A a T H lambda omega M N C F‖ ≤
      72*M*N*F*(H : ℝ)*S*(tauEnvelope T (poissonNonzeroFrequencyWindow H) : ℝ) := by
  rw [zeroPiece_eq_source]
  calc
    _ ≤ ∑ s ∈ zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))),
        ‖weight lambda omega s * completedKernel M N C a (output s)‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))),
        (9*M*N) := by
      apply sum_le_sum
      intro s hs
      rw [norm_mul]
      have hw := weight_norm_le A a T H _ lambda omega hlambda homega (mem_filter.mp hs).1
      exact (mul_le_mul hw (completedKernel_norm_le hM hN C a (output s))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = ((zeroSource (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)))).card : ℝ)*(9*M*N) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (8*F*(H : ℝ)*S*(tauEnvelope T (poissonNonzeroFrequencyWindow H) : ℝ))*(9*M*N) :=
      mul_le_mul_of_nonneg_right (zeroSource_card_le_hsf A a T H hS hF hT hTc) (by positivity)
    _ = _ := by ring

private theorem norm_branch_eq (negative : Bool) (z : ℂ) :
    ‖branch negative z‖ = ‖z‖ := by
  cases negative with
  | false => rfl
  | true =>
      change ‖star z‖ = ‖z‖
      exact norm_star z

private theorem norm_rootT_eq (A : ℕ) [NeZero A] (a : ZMod A)
    (u : (ZMod A)ˣ) (k : ZMod A) (t : (ZMod A)ˣ) : ‖rootT A a u k t‖ = 1 := by
  change ‖ZMod.stdAddChar
    (-a * k * ((u : ZMod A) * (↑(t⁻¹) : ZMod A)))‖ = 1
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

private theorem modeLambda_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)] (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) {t : ℕ}
    (ht : t ∈ baseCarrier e (D/delta)) :
    ‖actualModeLambda e D delta g l m negative u k t‖ ≤ 1 := by
  have hs := baseCarrier_window e (D/delta) ht
  have hQ : 1 ≤ e.Q2 := he.2.2.2.1
  have hQ0 : 0 < e.Q2 := zero_lt_one.trans_le hQ
  have hslo := (factorCarrier_bounds hQ hs).2.1
  have hU : 1 ≤ _root_.P3ActualLogAdapterSourceOnly.Uu e (D/delta*t) := by
    change 1 ≤ ((D/delta*t : ℕ) : ℝ)/e.Q2
    exact (le_div_iff₀ hQ0).mpr (by simpa only [one_mul] using hslo)
  have hU0 := zero_lt_one.trans_le hU
  have hi : ‖_root_.P3ActualLogAdapterSourceOnly.innerMultiplier e (D/delta*t) m.2‖ ≤ 1 := by
    have hv : (_root_.P3ActualLogAdapterSourceOnly.Uu e (D/delta*t))⁻¹ ≤ (1 : ℝ) := by
      simpa only [one_div] using (div_le_one hU0).mpr hU
    simpa only [_root_.P3ActualLogAdapterSourceOnly.innerMultiplier, norm_mul,
      _root_.P3ActualLogAdapterSourceOnly.norm_innerPhase, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hU0.le)] using hv
  have hg : ‖e.gamma2 (D/delta*t)‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h2, _⟩ := he
    exact (h2 _ hs).1
  simp only [actualModeLambda, commonLambda,
    ActualLogModePacketInstanceSourceOnly.modeW, norm_mul,
    norm_branch_eq, norm_rootT_eq, mul_one]
  exact (mul_le_mul hg hi (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

private theorem modeOmega_norm_le (e : MediumAtom) (D g l : ℕ) (Z : ℝ)
    (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool) (k : ZMod (g*l)) (h : ℤ) :
    ‖actualModeOmega e D g l Z tag m negative k h‖ ≤ 1 := by
  unfold actualModeOmega commonOmega
  split_ifs
  · change ‖branch negative
      (_root_.P3ActualLogAdapterSourceOnly.hMode e D Z tag h m.2)‖ ≤ 1
    rw [norm_branch_eq]
    exact _root_.P3ActualLogAdapterSourceOnly.norm_hMode_le e D Z tag h m.2
  all_goals simp only [norm_zero, zero_le_one]

def actualZeroPiece (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (M N : ℝ) : ℂ :=
  zeroPiece (g*l) (signedResidue negative e.residue)
    (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
    (actualModeLambda e D delta g l m negative u k)
    (actualModeOmega e D g l Z tag m negative k)
    M N (scaleC e D g l) (scaleF e D g)

/-- Actual mode: all coefficient and true closed-window inputs are conclusions.
The physical inner scale is Q2*delta/D, including 0<Sinner<1. -/
theorem actualZeroPiece_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hdeltaD : delta ∣ D) (hg : 0 < g)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) {M N : ℝ} (hM : 0 < M) (hN : 0 < N) :
    ‖actualZeroPiece e D delta g l Z tag m negative u k M N‖ ≤
      72*M*N*(scaleF e D g)*(e.sharedSmoothFrequencyBound Z D : ℝ)*
        (e.Q2*(delta : ℝ)/(D : ℝ))*
        (tauEnvelope (baseCarrier e (D/delta))
          (poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D)) : ℝ) := by
  have hq : 0 < D/delta := Nat.div_pos (Nat.le_of_dvd hD hdeltaD) hdelta
  have hqR : (0 : ℝ) < (D/delta : ℕ) := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hQ : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
  have hS : 0 < e.Q2 / ((D/delta : ℕ) : ℝ) := div_pos hQ hqR
  have hTeq := baseCarrier_eq_factorCarrier_div e hQ.le hq
  have hT : ∀ t ∈ baseCarrier e (D/delta), 0 < t := by
    intro t ht
    rw [hTeq] at ht
    exact factor_pos_small hS ht
  have hTc : ((baseCarrier e (D/delta)).card : ℝ) ≤
      2*(e.Q2/((D/delta : ℕ) : ℝ)) := by
    rw [hTeq]
    exact factor_card_small hS
  have hF : 0 ≤ scaleF e D g := by
    have hU : 0 < e.U := zero_lt_one.trans_le he.1
    have hQ1 : 0 < e.Q1 := zero_lt_one.trans_le he.2.2.1
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    unfold scaleF
    positivity
  have hfact : ((D/delta : ℕ) : ℝ)*(delta : ℝ) = (D : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hdeltaD
  have hscale : e.Q2/((D/delta : ℕ) : ℝ) = e.Q2*(delta : ℝ)/(D : ℝ) := by
    apply (div_eq_div_iff hqR.ne' hDR.ne').mpr
    calc
      _ = e.Q2 * (((D/delta : ℕ) : ℝ)*(delta : ℝ)) := by rw [hfact]
      _ = _ := by ring
  unfold actualZeroPiece
  have hp := zeroPiece_norm_le (g*l) (signedResidue negative e.residue)
    (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
    (actualModeLambda e D delta g l m negative u k)
    (actualModeOmega e D g l Z tag m negative k) (scaleC e D g l)
    hM hN hS.le hF hT hTc
    (fun t ht => modeLambda_norm_le he D delta g l m negative u k ht)
    (fun h _ => modeOmega_norm_le e D g l Z tag m negative k h)
  simpa only [hscale] using hp

/-- Literal adapter/P3 intake; this is the existing completed piece, with
zeroSource removed only into its explicitly paid first summand. -/
theorem completedModePiece_eq_zero_add_nonzero
    (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (M N : ℝ) :
    completedModePiece e D delta g l Z tag m negative u k M N =
      actualZeroPiece e D delta g l Z tag m negative u k M N +
        ∑ s ∈ nonzeroSource (carrier (g*l) (signedResidue negative e.residue)
          (baseCarrier e (D/delta)) (e.sharedSmoothFrequencyBound Z D)
          (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g)))),
          weight (actualModeLambda e D delta g l m negative u k)
            (actualModeOmega e D g l Z tag m negative k) s *
              completedKernel M N (scaleC e D g l) (signedResidue negative e.residue) (output s) := by
  unfold completedModePiece actualZeroPiece
  exact completedPiece_eq_zeroPiece_add_nonzero _ _ _ _ _ _ _ _ _ _ _

def actualZeroSix (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) : ℂ :=
  let Bb := scaleB e delta l
  let Cc := scaleC e D g l
  actualZeroPiece e D delta g l Z tag m negative u k Bb Cc +
    actualZeroPiece e D delta g l Z tag m negative u k Bb (2*Cc) +
    actualZeroPiece e D delta g l Z tag m negative u k Bb (4*Cc) +
    actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) Cc +
    actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (2*Cc) +
    actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (4*Cc)

private theorem norm_six_le (z1 z2 z3 z4 z5 z6 : ℂ) :
    ‖z1+z2+z3+z4+z5+z6‖ ≤ ‖z1‖+‖z2‖+‖z3‖+‖z4‖+‖z5‖+‖z6‖ := by
  have h12 := norm_add_le z1 z2
  have h123 := (norm_add_le (z1+z2) z3).trans (add_le_add h12 (le_refl ‖z3‖))
  have h1234 := (norm_add_le (z1+z2+z3) z4).trans (add_le_add h123 (le_refl ‖z4‖))
  have h12345 := (norm_add_le (z1+z2+z3+z4) z5).trans (add_le_add h1234 (le_refl ‖z5‖))
  exact (norm_add_le (z1+z2+z3+z4+z5) z6).trans (add_le_add h12345 (le_refl ‖z6‖))

/-- All six smooth zero pieces have the original H*S*B*F*C scale.
1512=72*(1+2)*(1+2+4); no six-piece Cauchy factor is inserted. -/
theorem actualZeroSix_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)]
    (hD : 0 < D) (hdelta : 0 < delta) (hdeltaD : delta ∣ D)
    (hg : 0 < g) (hl : 0 < l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    ‖actualZeroSix e D delta g l Z tag m negative u k‖ ≤
      1512*(scaleB e delta l)*(scaleC e D g l)*(scaleF e D g)*
        (e.sharedSmoothFrequencyBound Z D : ℝ)*(e.Q2*(delta : ℝ)/(D : ℝ))*
        (tauEnvelope (baseCarrier e (D/delta))
          (poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D)) : ℝ) := by
  let Bb := scaleB e delta l
  let Cc := scaleC e D g l
  let R : ℝ := (scaleF e D g)*(e.sharedSmoothFrequencyBound Z D : ℝ)*
    (e.Q2*(delta : ℝ)/(D : ℝ))*(tauEnvelope (baseCarrier e (D/delta))
      (poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D)) : ℝ)
  have hU : 0 < e.U := zero_lt_one.trans_le he.1
  have hQ2 : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
  have hQ3 : 0 < e.Q3 := zero_lt_one.trans_le he.2.2.2.2.1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hBb : 0 < Bb := by dsimp only [Bb, scaleB]; positivity
  have hCc : 0 < Cc := by dsimp only [Cc, scaleC]; positivity
  have hp (M N : ℝ) (hM : 0 < M) (hN : 0 < N) :
      ‖actualZeroPiece e D delta g l Z tag m negative u k M N‖ ≤ 72*M*N*R := by
    have ht := actualZeroPiece_norm_le he D delta g l hD hdelta hdeltaD hg
      Z tag m negative u k hM hN
    simpa only [R, mul_assoc] using ht
  have h1 := hp Bb Cc hBb hCc
  have h2 := hp Bb (2*Cc) hBb (by positivity)
  have h3 := hp Bb (4*Cc) hBb (by positivity)
  have h4 := hp (2*Bb) Cc (by positivity) hCc
  have h5 := hp (2*Bb) (2*Cc) (by positivity) (by positivity)
  have h6 := hp (2*Bb) (4*Cc) (by positivity) (by positivity)
  calc
    _ ≤ ‖actualZeroPiece e D delta g l Z tag m negative u k Bb Cc‖ +
        ‖actualZeroPiece e D delta g l Z tag m negative u k Bb (2*Cc)‖ +
        ‖actualZeroPiece e D delta g l Z tag m negative u k Bb (4*Cc)‖ +
        ‖actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) Cc‖ +
        ‖actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (2*Cc)‖ +
        ‖actualZeroPiece e D delta g l Z tag m negative u k (2*Bb) (4*Cc)‖ := norm_six_le _ _ _ _ _ _
    _ ≤ 72*Bb*Cc*R + 72*Bb*(2*Cc)*R + 72*Bb*(4*Cc)*R +
        72*(2*Bb)*Cc*R + 72*(2*Bb)*(2*Cc)*R + 72*(2*Bb)*(4*Cc)*R :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6
    _ = _ := by dsimp only [Bb, Cc, R]; ring

/-- A TRUE fixedSlice supplies delta>0 and delta|D from its stored gcd.
No diagonal budget, coefficient bound or window premise is accepted. -/
theorem fixedSlice_actualZeroSix_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : GeneralDGateNormalization.OuterIndex}
    (ho : o ∈ GeneralDActiveOuterEnergySourceOnly.fixedSlice e Yb Ys D delta g l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    ‖actualZeroSix e D delta g l Z tag m negative u k‖ ≤
      1512*(scaleB e delta l)*(scaleC e D g l)*(scaleF e D g)*
        (e.sharedSmoothFrequencyBound Z D : ℝ)*(e.Q2*(delta : ℝ)/(D : ℝ))*
        (tauEnvelope (baseCarrier e (D/delta))
          (poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D)) : ℝ) := by
  have hdeq : o.2.1.1.gcd D = delta := (mem_filter.mp ho).2.2.1
  have hdpos : 0 < delta := by
    rw [← hdeq, Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left _ hD
  have hdiv : delta ∣ D := by
    rw [← hdeq]
    exact Nat.gcd_dvd_right _ _
  exact actualZeroSix_norm_le he D delta g l hD hdpos hdiv hg hl Z tag m negative u k
/-- The SAME actual raw E324 pays this zero component, with T0 squared
exactly once. Ordinary packet-tau, root scalar costs and coeff/Re weights
stay external; no replacement of the energy by a BCF cardinal is made. -/
theorem actual_zero_payment_rawE324
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Yb Ys : ℝ)
    {D delta g l : ℕ} [NeZero (g*l)] (hD : 0 < D) (hg : 0 < g) (hl : 0 < l)
    {o : GeneralDGateNormalization.OuterIndex}
    (ho : o ∈ GeneralDActiveOuterEnergySourceOnly.fixedSlice d.cleanedAlphaAtom Yb Ys D delta g l)
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) :
    let e := d.cleanedAlphaAtom
    let Z0 := 1512*(scaleB e delta l)*(scaleC e D g l)*(scaleF e D g)*
      (e.sharedSmoothFrequencyBound Z D : ℝ)*(e.Q2*(delta : ℝ)/(D : ℝ))*
      (tauEnvelope (baseCarrier e (D/delta))
        (poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D)) : ℝ)
    (GeneralDActiveOuterEnergySourceOnly.physicalT0 e D)^2 *
      GeneralDActiveOuterEnergySourceOnly.fixedFirstEnergy e Yb Ys D delta g l *
        (actualZeroSix e D delta g l Z tag m negative u k).re ≤
      (GeneralDActiveOuterEnergySourceOnly.physicalT0 e D)^2 *
        (324*(D.divisors.card : ℝ)*d.U^2*d.Q3^2*d.Q2 /
          ((g : ℝ)^2*(l : ℝ)*(delta : ℝ)*(D : ℝ)^2))*Z0 := by
  dsimp only
  let e := d.cleanedAlphaAtom
  let Z0 := 1512*(scaleB e delta l)*(scaleC e D g l)*(scaleF e D g)*
    (e.sharedSmoothFrequencyBound Z D : ℝ)*(e.Q2*(delta : ℝ)/(D : ℝ))*
    (tauEnvelope (baseCarrier e (D/delta))
      (poissonNonzeroFrequencyWindow (e.sharedSmoothFrequencyBound Z D)) : ℝ)
  have h0 : ‖actualZeroSix e D delta g l Z tag m negative u k‖ ≤ Z0 :=
    fixedSlice_actualZeroSix_norm_le (mediumAdmissible_cleanedAlphaAtom hd)
      Yb Ys hD hg hl ho Z tag m negative u k
  have hZ0 : 0 ≤ Z0 := (norm_nonneg _).trans h0
  have hre : (actualZeroSix e D delta g l Z tag m negative u k).re ≤ Z0 :=
    (Complex.re_le_norm _).trans h0
  have hdeq : o.2.1.1.gcd D = delta := (mem_filter.mp ho).2.2.1
  have hdpos : 0 < delta := by
    rw [← hdeq, Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left _ hD
  have hE := GeneralDPhysicalTailCountSourceOnly.actual_fixedFirstEnergy_le_324
    hd Yb Ys hD hdpos hg hl
  have hE0 : 0 ≤ GeneralDActiveOuterEnergySourceOnly.fixedFirstEnergy e Yb Ys D delta g l := by
    unfold GeneralDActiveOuterEnergySourceOnly.fixedFirstEnergy
    exact sum_nonneg (fun o _ => sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left hre (mul_nonneg (sq_nonneg _) hE0)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (sq_nonneg _)) hZ0)

-- Public owner-file API for separate zero-tag consumers. Every type below
-- is the original private helper type; the proof is a direct local call.

/-- Exact signed nonzero-window membership. -/
theorem zero_frequency_nonzero (H : ℕ) {h : ℤ}
    (hh : h ∈ poissonNonzeroFrequencyWindow H) : h ≠ 0 :=
  frequency_nonzero H hh

/-- Positive closed-window factor, including scales below one. -/
theorem zero_factor_pos_small {S : ℝ} (hS : 0 < S) {t : ℕ}
    (ht : t ∈ factorCarrier S) : 0 < t :=
  factor_pos_small hS ht

/-- Closed-window cardinal bound at every positive scale. -/
theorem zero_factor_card_small {S : ℝ} (hS : 0 < S) :
    ((factorCarrier S).card : ℝ) ≤ 2*S :=
  factor_card_small hS

/-- Scalar triangle bound for the same six complex pieces. -/
theorem zero_norm_six_le (z1 z2 z3 z4 z5 z6 : ℂ) :
    ‖z1+z2+z3+z4+z5+z6‖ ≤ ‖z1‖+‖z2‖+‖z3‖+‖z4‖+‖z5‖+‖z6‖ :=
  norm_six_le z1 z2 z3 z4 z5 z6
end
end ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly
