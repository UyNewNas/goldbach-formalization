import Mathlib
import ImbalancedChen.Part3TwoLongNaturalResidueCore
import ImbalancedChen.Part3TwoLongActualDoublePeriodization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual natural compact-carrier residues are identified with affine integer
periodizations by a support bijection. This binds the original count and
EXACT coprime mean to independently defined finite unit-residue sums.
-/
namespace ImbalancedChen.Part3.TwoLongNaturalPeriodization
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongNaturalResidueCore
open ImbalancedChen.Part3.TwoLongActualDoublePeriodization

/-- General natural-to-integer affine-lattice bijection for the original
positive compact long profile; no periodization identity is a premise. -/
theorem natural_progression_eq_periodization (F : ℝ → ℂ)
    (hF : Function.support F ⊆ Icc (1/2 : ℝ) (5/2))
    {U : ℝ} (hU : 0 < U) {q : ℕ} (hq : 0 < q) (b : ℤ) :
    (∑ n ∈ wideWindow U, if Int.ModEq q (n : ℤ) b then F ((n : ℝ)/U) else 0) =
      ∑' z : ℤ, F (((b : ℝ)+(q : ℝ)*(z : ℝ))/U) := by
  let f : ℕ → ℂ := fun n => if Int.ModEq q (n : ℤ) b then F ((n : ℝ)/U) else 0
  let g : ℤ → ℂ := fun z => F (((b : ℝ)+(q : ℝ)*(z : ℝ))/U)
  have hnonneg (z : Function.support g) : 0 ≤ b+(q : ℤ)*z.val := by
    have hs := hF z.property
    have hlo : (0 : ℝ) ≤ (b : ℝ)+(q : ℝ)*z.val := by
      have h := (le_div_iff₀ hU).mp hs.1
      linarith
    exact_mod_cast hlo
  let i : Function.support g → ℕ := fun z => (b+(q : ℤ)*z.val).toNat
  have hcast (z : Function.support g) : (i z : ℤ)=b+(q : ℤ)*z.val :=
    Int.toNat_of_nonneg (hnonneg z)
  have hi : Function.Injective i := by
    intro z w h
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    rw [hcast,hcast] at hh
    exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast hq.ne') (add_left_cancel hh))
  have hf : Function.support f ⊆ Set.range i := by
    intro n hn
    have hn' : Int.ModEq q (n : ℤ) b ∧ F ((n : ℝ)/U) ≠ 0 := by
      simpa only [f,Function.mem_support,ne_eq,ite_eq_right_iff,Classical.not_imp] using hn
    obtain ⟨z,hz⟩ := Int.modEq_iff_dvd.mp hn'.1.symm
    have he : b+(q : ℤ)*z=n := by linarith
    have heR : (b : ℝ)+(q : ℝ)*z=n := by exact_mod_cast he
    have hg : z ∈ Function.support g := by simpa only [g,heR] using hn'.2
    refine ⟨⟨z,hg⟩,?_⟩
    simp only [i,he,Int.toNat_natCast]
  have hfg (z : Function.support g) : f (i z)=g z := by
    have hm : Int.ModEq q (i z : ℤ) b := by
      rw [hcast]
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-z.val,by ring⟩
    have hr : (i z : ℝ)=(b : ℝ)+(q : ℝ)*z.val := by exact_mod_cast hcast z
    simp only [f,hm,if_pos,hr,g]
  calc
    _ = ∑' n : ℕ, f n := by
      symm
      apply tsum_eq_sum
      intro n hn
      have hz : F ((n : ℝ)/U)=0 := by
        by_contra h
        exact hn (nonzero_mem_wideWindow hU hF h)
      simp [f,hz]
    _ = _ := tsum_eq_tsum_of_ne_zero_bij i hi hf hfg

variable {q : ℕ} [NeZero q]

/-- The least nonnegative representative gives the SAME actual row. -/
theorem rowMass_eq_periodization (F : 𝓢(ℝ, ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U : ℝ} (hU : 0 < U) (x : ZMod q) :
    rowMass (wideWindow U) (fun n => F ((n : ℝ)/U)) x =
      progressionPeriodization F U (q : ℝ) (x.val : ℝ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hp (n : ℕ) : ((n : ZMod q)=x) ↔ Int.ModEq q (n : ℤ) (x.val : ℤ) := by
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using
      (ZMod.intCast_eq_intCast_iff (n : ℤ) (x.val : ℤ) q)
  unfold rowMass
  simp_rw [hp]
  exact natural_progression_eq_periodization F hF hU hq (x.val : ℤ)

def periodizedResidue (F : 𝓢(ℝ, ℂ)) (U : ℝ) (x : ZMod q) : ℂ :=
  progressionPeriodization F U (q : ℝ) (x.val : ℝ)

/-- The original natural AP count and its exact coprime mean equal the
actual finite unit graph and product mean, including unchanged alpha.
No hP1, P2, unrestricted mean or arbitrary count identity is supplied. -/
theorem naturalCore_eq_unit_periodizations (F G : 𝓢(ℝ, ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    (hG : Function.support (G : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (m a : ℕ)
    (hm : Nat.Coprime m q) (ha : Nat.Coprime a q) (alpha : ℂ) :
    fixedMCore (wideWindow U) (wideWindow V) m a q alpha F G U V =
      alpha * (unitGraphCount ((a : ZMod q)*(m : ZMod q)⁻¹)
        (periodizedResidue F U) (periodizedResidue G V) -
          (Nat.totient q : ℂ)⁻¹ * unitMass (periodizedResidue F U) *
            unitMass (periodizedResidue G V)) := by
  have hmU : IsUnit (m : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using hm
  have haU : IsUnit (a : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using ha
  rw [fixedMCore_eq_residueCore]
  have hf : rowMass (wideWindow U) (fun n => F ((n : ℝ)/U)) = periodizedResidue F U :=
    funext (rowMass_eq_periodization F hF hU)
  have hg : rowMass (wideWindow V) (fun n => G ((n : ℝ)/V)) = periodizedResidue G V :=
    funext (rowMass_eq_periodization G hG hV)
  rw [hf,hg,residueCore_eq_unitGraph (m : ZMod q) (a : ZMod q) haU hmU]

/-- Original nonprimitive m case: both literal arithmetic terms vanish. -/
theorem naturalCore_zero_of_nonprimitive (I J : Finset ℕ) (m a : ℕ)
    (hm : ¬ Nat.Coprime m q) (ha : Nat.Coprime a q) (alpha : ℂ)
    (f g : ℝ → ℂ) (U V : ℝ) : fixedMCore I J m a q alpha f g U V = 0 := by
  have hmU : ¬ IsUnit (m : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using hm
  have haU : IsUnit (a : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using ha
  rw [fixedMCore_eq_residueCore,residueCore_zero_of_nonunit (m : ZMod q) (a : ZMod q) haU hmU,mul_zero]

end
end ImbalancedChen.Part3.TwoLongNaturalPeriodization
