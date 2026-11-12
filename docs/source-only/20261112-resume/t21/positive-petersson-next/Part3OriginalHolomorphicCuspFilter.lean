import ImbalancedChen.Part3OriginalNonzeroCuspOneSource
import ImbalancedChen.Part3CenteredFourier

namespace ImbalancedChen.Part3.OriginalHolomorphicCuspFilter20261112

noncomputable section
open Matrix
open scoped MatrixGroups BigOperators
open OriginalSmoothPoissonTail OriginalSmoothPoissonTail.Physical
open Gamma0ActualCuspsSourceOnly P3Period64NativeReconstructionSourceOnly (e e_add norm_e)

/-- Bottom-row condition after changing to any integral cusp chart. -/
theorem integral_cusp_gate (N : ℕ) (M g : SL(2,ℤ)) :
    M*g⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (N:ℤ) ∣ M 1 0*g 1 1-M 1 1*g 1 0 := by
  rw [gamma0_mem_iff_level_dvd_c]
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two,
    Matrix.SpecialLinearGroup.SL2_inv_expl, sub_eq_add_neg]

def chi (q : ℕ) (v : ℤ) : ℂ := e ((v:ℝ)/(q:ℝ))

theorem chi_eq (q : ℕ) [NeZero q] (v : ℤ) :
    chi q v = ZMod.stdAddChar (v : ZMod q) := by
  rw [ZMod.stdAddChar_coe]
  simp only [chi,e]
  push_cast; congr 1; ring

def Dval (C : ℕ) {N : ℕ} [NeZero N] (u : ZMod C) (j : ZMod N) : ℤ :=
  (u.val:ℤ)+(C:ℤ)*j.val

def residuePhase (C N : ℕ) (n : ℤ) (u D : ℤ) : ℂ :=
  e ((n:ℝ)*D/((C:ℝ)*N)) * chi C u

/-- Positive bottom entry C, horizontal period N, and every lifted denominator residue. -/
def cuspSum (N C : ℕ) [NeZero N] [NeZero C] (g : SL(2,ℤ)) (m n : ℤ) : ℂ :=
  ∑ u : ZMod C, if IsUnit u then ∑ j : ZMod N,
    if (N:ℤ) ∣ (C:ℤ)*g 1 1-Dval C u j*g 1 0 then
      residuePhase C N n (m*(u⁻¹).val) (Dval C u j) else 0 else 0

def freq (N C : ℕ) [NeZero N] (g : SL(2,ℤ)) (n : ℤ) (t : ZMod N) : ℤ :=
  n-(t.val:ℤ)*g 1 0*C

private theorem insert_character (N : ℕ) [NeZero N] (d : ℤ) (A : ℂ) :
    (if (N:ℤ)∣d then A else 0) =
      (N:ℂ)⁻¹ * ∑ t : ZMod N, chi N ((t.val:ℤ)*d)*A := by
  rw [← Finset.sum_mul]
  simp only [chi_eq, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, sum_stdAddChar_mul_eq]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  split_ifs <;> simp [NeZero.ne N]

private theorem product_phase (N C : ℕ) [NeZero N] [NeZero C] (g : SL(2,ℤ))
    (m n : ℤ) (t : ZMod N) (u : ZMod C) (j : ZMod N) :
    chi N ((t.val:ℤ)*((C:ℤ)*g 1 1-Dval C u j*g 1 0)) *
      residuePhase C N n (m*(u⁻¹).val) (Dval C u j) =
      (chi N ((t.val:ℤ)*C*g 1 1) *
        e ((freq N C g n t : ℝ)*u.val/((C:ℝ)*N)) * chi C (m*(u⁻¹).val)) *
          chi N ((j.val:ℤ) * freq N C g n t) := by
  dsimp [chi,residuePhase,Dval,freq]
  simp only [← e_add]
  congr 1
  push_cast
  field_simp [NeZero.ne N,NeZero.ne C] <;> ring

private theorem sum_lifts (N C : ℕ) [NeZero N] [NeZero C] (g : SL(2,ℤ))
    (m n : ℤ) (t : ZMod N) (u : ZMod C) :
    (N:ℂ)⁻¹ * (∑ j : ZMod N,
      chi N ((t.val:ℤ)*((C:ℤ)*g 1 1-Dval C u j*g 1 0)) *
        residuePhase C N n (m*(u⁻¹).val) (Dval C u j)) =
    if (N:ℤ) ∣ freq N C g n t then
      chi N ((t.val:ℤ)*C*g 1 1) *
        ZMod.stdAddChar (((freq N C g n t / (N:ℤ) : ℤ):ZMod C) * u + (m:ZMod C)*u⁻¹)
    else 0 := by
  simp_rw [product_phase]
  rw [← Finset.mul_sum]
  simp only [chi_eq, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, sum_stdAddChar_mul_eq]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  split_ifs with h
  · let b := freq N C g n t / (N:ℤ)
    have hb : b*(N:ℤ)=freq N C g n t := Int.ediv_mul_cancel h
    have he : e ((freq N C g n t : ℝ)*u.val/((C:ℝ)*N)) =
        ZMod.stdAddChar ((b : ZMod C)*u) := by
      have hh : ((b*(u.val:ℤ):ℤ):ZMod C)=(b:ZMod C)*u := by simp
      rw [← hh, ← chi_eq,chi,← hb]
      congr 1; push_cast; field_simp [NeZero.ne N,NeZero.ne C] <;> ring
    rw [he, ZMod.stdAddChar.map_add_eq_mul]
    change _ = _ * (ZMod.stdAddChar ((b:ZMod C)*u) * _)
    field_simp [NeZero.ne N]
    <;> ring
  · ring

/-- No prime-level restriction and no inverse of the cusp numerator is required. -/
theorem cuspSum_eq (N C : ℕ) [NeZero N] [NeZero C] (g : SL(2,ℤ)) (m n : ℤ) :
    cuspSum N C g m n =
      ∑ t : ZMod N, if (N:ℤ) ∣ freq N C g n t then
        chi N ((t.val:ℤ)*C*g 1 1) * kloosterman C (freq N C g n t / (N:ℤ)) m else 0 := by
  classical
  let A := fun (t : ZMod N) (u : ZMod C) => if IsUnit u then
    (N:ℂ)⁻¹*(∑ j : ZMod N,chi N ((t.val:ℤ)*((C:ℤ)*g 1 1-Dval C u j*g 1 0))*
      residuePhase C N n (m*(u⁻¹).val) (Dval C u j)) else 0
  calc
    _ = ∑ u : ZMod C, ∑ t : ZMod N, A t u := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : IsUnit u
      · simp only [cuspSum, A, if_pos hu]
        simp_rw [insert_character]
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      · simp [A,hu]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      simp only [A,sum_lifts]
      by_cases h : (N:ℤ) ∣ freq N C g n t
      · simp only [if_pos h,Physical.kloosterman_eq_zmod,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _; split_ifs <;> simp
      · simp [h]

/-- A majorant uniform in the second Fourier integer of the Hecke expansion propagates through
every actual integral cusp, with the exact finite period as cost. -/
theorem cuspSum_bound (N C : ℕ) [NeZero N] [NeZero C] (g : SL(2,ℤ)) (m n : ℤ)
    {b : ℝ} (hb : 0≤b) (hC : ∀ h : ℤ, ‖kloosterman C h m‖≤b) :
    ‖cuspSum N C g m n‖ ≤ (N:ℝ)*b := by
  rw [cuspSum_eq]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _t : ZMod N, b := by
      apply Finset.sum_le_sum; intro t _
      split_ifs
      · simp only [norm_mul,chi,norm_e,one_mul]; apply hC
      · simpa using hb
    _ = _ := by simp

theorem inverse_swap (C : ℕ) [NeZero C] (m n : ℤ) :
    kloosterman C m n = kloosterman C n m := by
  classical
  have rep (a b : ℤ) : kloosterman C a b =
      ∑ u ∈ (Finset.univ : Finset (ZMod C)).filter IsUnit,
        ZMod.stdAddChar ((a:ZMod C)*u+(b:ZMod C)*u⁻¹) := by
    rw [Physical.kloosterman_eq_zmod,Finset.sum_filter]
  have hi {u : ZMod C} (hu : IsUnit u) : IsUnit u⁻¹ ∧ (u⁻¹)⁻¹=u := by
    obtain ⟨v,rfl⟩ := hu
    simp only [ZMod.inv_coe_unit,inv_inv,Units.isUnit,true_and]
  rw [rep,rep]
  apply Finset.sum_bij (fun u _ => u⁻¹)
  · intro u hu; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hi (Finset.mem_filter.mp hu).2).1⟩
  · intro u hu v hv he
    simpa only [(hi (Finset.mem_filter.mp hu).2).2,(hi (Finset.mem_filter.mp hv).2).2]
      using congrArg Inv.inv he
  · intro u hu
    exact ⟨u⁻¹,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hi (Finset.mem_filter.mp hu).2).1⟩,
      (hi (Finset.mem_filter.mp hu).2).2⟩
  · intro u hu
    rw [(hi (Finset.mem_filter.mp hu).2).2,add_comm]

end
end ImbalancedChen.Part3.OriginalHolomorphicCuspFilter20261112
