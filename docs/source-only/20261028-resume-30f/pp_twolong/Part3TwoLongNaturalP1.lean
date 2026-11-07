import Mathlib
import ImbalancedChen.Part3TwoLongNaturalPeriodization
import ImbalancedChen.Part3TwoLongP1AxisCancellation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual original natural compact-carrier discrepancy is transformed
to P1. The finite residue/Poisson interchange is justified by the actual
absolute Schwartz mode sums. Unit inversion proves the required phase
orientation S(b*j,k), rather than silently identifying S(k,b*j) with it.
P2 and its fixed N2 Fourier-decay bound are not hypotheses or conclusions.
-/
namespace ImbalancedChen.Part3.TwoLongNaturalP1
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators Topology SchwartzMap FourierTransform
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongNaturalResidueCore
open ImbalancedChen.Part3.TwoLongNaturalPeriodization
open ImbalancedChen.Part3.TwoLongActualDoublePeriodization
open ImbalancedChen.Part3.TwoLongP1AxisCancellation
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

variable {q : ℕ} [NeZero q]

private theorem sum_unit_filter (f : ZMod q → ℂ) :
    (∑ u : ZMod q, if IsUnit u then f u else 0) =
      ∑ v : (ZMod q)ˣ, f (v : ZMod q) := by
  calc
    _ = ∑ u : ZMod q, (if IsUnit u then (1 : ℂ) else 0) * f u := by
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs <;> simp only [one_mul,zero_mul]
    _ = ∑ u : ZMod q,
        (∑ v : (ZMod q)ˣ, if u=(v : ZMod q) then (1 : ℂ) else 0) * f u := by
      simp_rw [ImbalancedChen.Part3.sum_unitResidueIndicator]
    _ = ∑ v : (ZMod q)ˣ, ∑ u : ZMod q,
        (if u=(v : ZMod q) then (1 : ℂ) else 0) * f u := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [ite_mul]

/-- The literal production Kloosterman convention is symmetric by an
actual bijection of the unit group, at every positive composite modulus. -/
theorem kloosterman_swap (r s : ℤ) : kloosterman q r s = kloosterman q s r := by
  rw [kloosterman_eq_zmod,kloosterman_eq_zmod,sum_unit_filter,sum_unit_filter]
  have hi : Function.Bijective (fun v : (ZMod q)ˣ => v⁻¹) := by
    constructor
    · intro u v h
      simpa only [inv_inv] using congrArg (fun w : (ZMod q)ˣ => w⁻¹) h
    · intro v
      exact ⟨v⁻¹,inv_inv v⟩
  apply Fintype.sum_bijective (fun v : (ZMod q)ˣ => v⁻¹) hi
  intro v
  simp only [ZMod.inv_coe_unit,inv_inv]
  congr 1
  ring

def residueCharacter (j : ℤ) (x : ZMod q) : ℂ :=
  ZMod.stdAddChar ((j : ZMod q)*x)

theorem fourier_residue (j : ℤ) (x : ZMod q) :
    fourier j ((x.val : ℝ)/(q : ℝ) : UnitAddCircle) = residueCharacter j x := by
  have hx : ((j*(x.val : ℤ) : ℤ) : ZMod q)=(j : ZMod q)*x := by
    simp only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [residueCharacter,← hx,ZMod.stdAddChar_coe,fourier_coe_apply]
  push_cast
  congr 1
  ring

theorem unitMass_character (j : ℤ) :
    unitMass (residueCharacter (q:=q) j) = ramanujan q j := by
  rw [unitMass,sum_unit_filter,ramanujan_eq_units]

/-- The primitive unit graph first gives S(k,b*j), and unit inversion
then gives exactly the original manuscript S(b*j,k). -/
theorem unitGraph_character (b j k : ℤ) :
    unitGraphCount (b : ZMod q) (residueCharacter j) (residueCharacter k) =
      kloosterman q (b*j) k := by
  rw [kloosterman_swap,kloosterman_eq_zmod]
  unfold unitGraphCount residueCharacter
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hu : IsUnit y
  · simp only [if_pos hu,← AddChar.map_add_eq_mul,Int.cast_mul]
    congr 1
    ring
  · simp only [if_neg hu]

/-- The independent exact coprime mean supplies BOTH Ramanujan factors. -/
theorem residueCore_character (m a : ZMod q) (ha : IsUnit a) (hm : IsUnit m)
    (b : ℤ) (hb : (b : ZMod q)=a*m⁻¹) (j k : ℤ) :
    residueCore m a (residueCharacter j) (residueCharacter k) =
      centeredKernel q b j k := by
  rw [residueCore_eq_unitGraph m a ha hm,← hb,unitGraph_character,
    unitMass_character,unitMass_character,centeredKernel]
  ring

/- The only auxiliary interchange is used immediately for the actual
finite complete residue kernel. Its hypotheses are summability of the
actual one-coordinate Poisson sequences, proved in batch E. -/
private theorem finite_bilinear_tsum {ι : Type*} (s : Finset ι)
    (w : ι → ℂ) (A B : ι → ℤ → ℂ)
    (hA : ∀ p ∈ s, Summable (A p)) (hB : ∀ p ∈ s, Summable (B p)) :
    (∑ p ∈ s, w p*(∑' j, A p j)*(∑' k, B p k)) =
      ∑' j, ∑' k, ∑ p ∈ s, w p*A p j*B p k := by
  calc
    _ = ∑ p ∈ s, ∑' j, w p*A p j*(∑' k, B p k) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [tsum_mul_right,tsum_mul_left]
    _ = ∑' j, ∑ p ∈ s, w p*A p j*(∑' k, B p k) :=
      (Summable.tsum_finsetSum (fun p hp => ((hA p hp).mul_left (w p)).mul_right _)).symm
    _ = _ := by
      apply tsum_congr
      intro j
      calc
        _ = ∑ p ∈ s, ∑' k, w p*A p j*B p k := by simp_rw [tsum_mul_left]
        _ = _ := (Summable.tsum_finsetSum (fun p hp => (hB p hp).mul_left _)).symm

/-- Absolute convergence on the product of the two genuine integer
frequency axes, before commuting the actual finite residue sums. -/
theorem residue_modes_norm_summable (m a : ZMod q) (F G : 𝓢(ℝ, ℂ))
    (hF : HasCompactSupport (F : ℝ → ℂ)) (hG : HasCompactSupport (G : ℝ → ℂ))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    Summable (fun p : ℤ × ℤ =>
      ‖∑ x : ZMod q, ∑ y : ZMod q,
        residueKernel m a x y * poissonMode F U q x.val p.1 *
          poissonMode G V q y.val p.2‖) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs (x y : ZMod q) : Summable (fun p : ℤ × ℤ =>
      ‖residueKernel m a x y‖ * ‖poissonMode F U q x.val p.1‖ *
        ‖poissonMode G V q y.val p.2‖) := by
    have hf := poissonMode_norm_summable F hF hU hq x.val
    have hg := poissonMode_norm_summable G hG hV hq y.val
    apply (summable_prod_of_nonneg (fun p => by positivity)).mpr
    constructor
    · intro j
      exact hg.mul_left _
    · simp_rw [tsum_mul_left]
      exact (hf.mul_left _).mul_right _
  have hmajor : Summable (fun p : ℤ × ℤ =>
      ∑ x : ZMod q, ∑ y : ZMod q,
        ‖residueKernel m a x y‖ * ‖poissonMode F U q x.val p.1‖ *
          ‖poissonMode G V q y.val p.2‖) :=
    summable_sum (fun x hx => summable_sum (fun y hy => hs x y))
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  calc
    _ ≤ ∑ x : ZMod q, ‖∑ y : ZMod q,
        residueKernel m a x y * poissonMode F U q x.val p.1 *
          poissonMode G V q y.val p.2‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [norm_mul] using (norm_sum_le (Finset.univ)
        (fun y : ZMod q => residueKernel m a x y * poissonMode F U q x.val p.1 *
          poissonMode G V q y.val p.2))

/-- No convergence of an invented candidate series is assumed: every
actual residue row uses its own absolutely summable affine Poisson modes. -/
theorem residueCore_periodization_modes (m a : ZMod q) (F G : 𝓢(ℝ, ℂ))
    (hF : HasCompactSupport (F : ℝ → ℂ)) (hG : HasCompactSupport (G : ℝ → ℂ))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    residueCore m a (periodizedResidue F U) (periodizedResidue G V) =
      ∑' j : ℤ, ∑' k : ℤ, ∑ x : ZMod q, ∑ y : ZMod q,
        residueKernel m a x y * poissonMode F U q x.val j * poissonMode G V q y.val k := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  unfold residueCore periodizedResidue
  simp_rw [affine_periodization_poisson F hF hU hq,
    affine_periodization_poisson G hG hV hq]
  have he := finite_bilinear_tsum (Finset.univ : Finset (ZMod q × ZMod q))
    (fun p => residueKernel m a p.1 p.2)
    (fun p => poissonMode F U q p.1.val) (fun p => poissonMode G V q p.2.val)
    (fun p hp => (poissonMode_norm_summable F hF hU hq p.1.val).of_norm)
    (fun p hp => (poissonMode_norm_summable G hG hV hq p.2.val).of_norm)
  simpa only [← Finset.univ_product_univ,Finset.sum_product] using he

theorem residueCore_periodization_P1 (m a : ZMod q) (ha : IsUnit a) (hm : IsUnit m)
    (b : ℤ) (hb : (b : ZMod q)=a*m⁻¹) (F G : 𝓢(ℝ, ℂ))
    (hF : HasCompactSupport (F : ℝ → ℂ)) (hG : HasCompactSupport (G : ℝ → ℂ))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    residueCore m a (periodizedResidue F U) (periodizedResidue G V) =
      ((U*V/(q : ℝ)^2 : ℝ) : ℂ) *
        ∑' j : ℤ, ∑' k : ℤ, (𝓕 F) ((U/q)*(j : ℝ)) *
          (𝓕 G) ((V/q)*(k : ℝ)) * centeredKernel q b j k := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [residueCore_periodization_modes m a F G hF hG hU hV]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro j
  apply tsum_congr
  intro k
  rw [← residueCore_character m a ha hm b hb j k]
  simp only [residueCore,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [poissonMode,smul_eq_mul,fourier_residue]
  push_cast
  field_simp [hq]
  ring

/-- Original P1 on the actual natural compact carrier, with original
alpha, literal inverse short factor, exact mean, and UV/q^2 factor. -/
theorem naturalCore_P1 (F G : 𝓢(ℝ, ℂ))
    (hFc : HasCompactSupport (F : ℝ → ℂ)) (hGc : HasCompactSupport (G : ℝ → ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    (hG : Function.support (G : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (m a : ℕ)
    (hm : Nat.Coprime m q) (ha : Nat.Coprime a q) (alpha : ℂ) :
    fixedMCore (wideWindow U) (wideWindow V) m a q alpha F G U V =
      alpha * ((U*V/(q : ℝ)^2 : ℝ) : ℂ) *
        ∑' j : ℤ, ∑' k : ℤ, (𝓕 F) ((U/q)*(j : ℝ)) *
          (𝓕 G) ((V/q)*(k : ℝ)) *
            centeredKernel q ((a : ℤ)*inverseResidue q (m : ℤ)) j k := by
  have hmU : IsUnit (m : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using hm
  have haU : IsUnit (a : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using ha
  have hb : (((a : ℤ)*inverseResidue q (m : ℤ) : ℤ) : ZMod q)=
      (a : ZMod q)*(m : ZMod q)⁻¹ := by
    simp only [Int.cast_mul,Int.cast_natCast,inverseResidue,ZMod.natCast_zmod_val]
  rw [fixedMCore_eq_residueCore]
  have hf : rowMass (wideWindow U) (fun n => F ((n : ℝ)/U)) = periodizedResidue F U :=
    funext (rowMass_eq_periodization F hF hU)
  have hg : rowMass (wideWindow V) (fun n => G ((n : ℝ)/V)) = periodizedResidue G V :=
    funext (rowMass_eq_periodization G hG hV)
  rw [hf,hg,residueCore_periodization_P1 (m : ZMod q) (a : ZMod q) haU hmU _ hb
    F G hFc hGc hU hV]
  ring

end
end ImbalancedChen.Part3.TwoLongNaturalP1
