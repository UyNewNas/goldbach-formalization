import ImbalancedChen.Part3OriginalPositivePeterssonTrace

/-! Transfer the existing arbitrary-frame Hecke Fourier expansion to the
two identity observations. The period-N expression retains only frequencies
N h; the N-fold denominator residue sum cancels its Fourier normalization. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityHolomorphicOrbit20261113
noncomputable section
open Finset Matrix Complex
open scoped MatrixGroups FourierTransform BigOperators UpperHalfPlane
open OriginalSmoothPoissonTail OriginalSmoothPoissonTail.Physical
open OriginalHolomorphicCuspFilter20261112 OriginalHeckeCuspSeries20261112 OriginalHeckePoisson20261112
open P3Period64NativeReconstructionSourceOnly (e)

/-- Positive modulus after the identity-frame gate is the literal C,
with N|C. A physical integer h occurs in the period-N expansion at N h. -/
theorem identity_cusp_sum (N C : ℕ) [NeZero N] [NeZero C] (m n : ℤ) :
    cuspSum N C 1 m n =
      if (N:ℤ)∣n then if N∣C then (N:ℂ)*kloosterman C (n/(N:ℤ)) m else 0 else 0 := by
  classical
  rw [cuspSum_eq]
  have f (t : ZMod N) : freq N C (1 : SL(2,ℤ)) n t=n := by simp [freq]
  simp_rw [f]
  by_cases dn : (N:ℤ)∣n
  · simp only [if_pos dn]
    change (∑ t : ZMod N, chi N ((t.val:ℤ)*C*(1 : SL(2,ℤ)) 1 1)*
      kloosterman C (n/(N:ℤ)) m)=_
    have entry : (1 : SL(2,ℤ)) 1 1=(1:ℤ) := by simp
    simp only [entry,mul_one]
    rw [←sum_mul]
    simp only [chi_eq,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,sum_stdAddChar_mul_eq]
    by_cases dc : N∣C
    · have zero : (C:ZMod N)=0 := (ZMod.natCast_eq_zero_iff C N).mpr dc
      rw [if_pos zero,if_pos dc]
    · have nz : (C:ZMod N)≠0 := fun h => dc ((ZMod.natCast_eq_zero_iff C N).mp h)
      rw [if_neg nz,zero_mul,if_neg dc]
  · simp [dn]

local instance (c : ℕ+) : NeZero c.val := ⟨c.property.ne'⟩

/-- Every auxiliary period-N Poisson mode outside the native lattice
vanishes before either the horizontal integral or the modulus sum. -/
theorem forbidden_layer (N k m : ℕ) [NeZero N] (C : ℕ+) (n : ℤ) (p : Params)
    (h : ¬(N:ℤ)∣n ∨ ¬N∣C.val) : layer N k m 1 (C,n) p=0 := by
  rw [layer,identity_cusp_sum]
  rcases h with bad|bad
  · simp [bad]
  · split_ifs <;> simp_all

/-- The surviving literal integer mode h and denominator C. The
Fourier factor is independent of the choice of level divisor of C. -/
theorem surviving_layer (N k m : ℕ) [NeZero N] (C : ℕ+) (h : ℤ) (p : Params) (hc : N∣C.val) :
    layer N k m 1 (C,(N:ℤ)*h) p =
      kloosterman C.val h (m:ℤ)*
        ((1/(C:ℝ)^k*(C:ℝ)^(-2*p.1.val)*p.2.im^(1-(k:ℝ))*p.2.im^(-p.1.val):ℝ):ℂ)*
        transformed 1 k m C h p * e ((h:ℝ)*p.2.re) := by
  have nz : (N:ℤ)≠0 := by exact_mod_cast NeZero.ne N
  have zr : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  have zc : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  rw [layer,identity_cusp_sum,if_pos (dvd_mul_right _ _),if_pos hc,Int.mul_ediv_cancel_left _ nz]
  have scale : (N:ℂ)*kloosterman C.val h (m:ℤ)/(N:ℂ)=kloosterman C.val h (m:ℤ) := by
    field_simp [zc]
  rw [scale]
  have sx : sample N ((N:ℤ)*h) p.2=sample 1 h p.2 := by
    dsimp [sample]
    push_cast
    field_simp [zr] <;> ring
  have sy : (((N:ℤ)*h:ℤ):ℝ)*p.2.re/N=(h:ℝ)*p.2.re := by
    push_cast
    field_simp [zr] <;> ring
  simp only [transformed,sx,sy]

private def lattice (N : ℕ) [NeZero N] : ℤ ≃ {n : ℤ // (N:ℤ)∣n} where
  toFun h := ⟨(N:ℤ)*h,dvd_mul_right _ _⟩
  invFun n := n.val/(N:ℤ)
  left_inv h := Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne N)
  right_inv n := Subtype.ext (by rw [mul_comm,Int.ediv_mul_cancel n.property])

/-- The native integer expansion, with the external level entering only by
the modulus-divisor gate. The existing convergent Poisson expansion is
reindexed exactly, also at physical Fourier frequency zero. -/
theorem identity_denominator (N k m : ℕ) [NeZero N] (hk : 2≤k) (C : ℕ+) (p : Params) :
    denominator N k m 1 C p =
    if N∣C.val then ∑' h : ℤ,
      kloosterman C.val h (m:ℤ)*
        ((1/(C:ℝ)^k*(C:ℝ)^(-2*p.1.val)*p.2.im^(1-(k:ℝ))*p.2.im^(-p.1.val):ℝ):ℂ)*
        transformed 1 k m C h p * e ((h:ℝ)*p.2.re) else 0 := by
  classical
  let F := fun n : ℤ => layer N k m 1 (C,n) p
  have H : HasSum F (denominator N k m 1 C p) := denominator_modes N k m hk 1 C p
  by_cases good : N∣C.val
  · rw [if_pos good]
    have support : Function.support F ⊆ {n : ℤ | (N:ℤ)∣n} := by
      intro n hn
      by_contra bad
      exact hn (forbidden_layer N k m C n p (Or.inl bad))
    have A := (hasSum_subtype_iff_of_support_subset support).mpr H
    have B := (lattice N).hasSum_iff.mpr A
    apply (B.congr_fun (fun h => ?_)).tsum_eq.symm
    exact (surviving_layer N k m C h p good).symm
  · rw [if_neg good,←H.tsum_eq]
    exact tsum_eq_zero (fun n => forbidden_layer N k m C n p (Or.inr good))

end
end ImbalancedChen.Part3.OriginalSameInfinityHolomorphicOrbit20261113
