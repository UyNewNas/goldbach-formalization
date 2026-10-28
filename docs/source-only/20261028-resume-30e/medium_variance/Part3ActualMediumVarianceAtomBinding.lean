import ImbalancedChen.Part3ActualWeightedFilteredBDH
import ImbalancedChen.Part3OriginalSamePsiS1OwnedAtlas
import ImbalancedChen.Part3MediumReceiverCutoffArithmetic
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium appendix (8)--(9),(14): y=x^(1/loglog x), the actual
strict receiver and occupied half-open dyadic keys. Q=floor(8*Q1*D)
is independent of any proposed discrepancy or variance estimate.
-/

namespace ImbalancedChen.Part3.ActualMediumVarianceAtomBindingSourceOnly

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MediumCanonicalFixedBlock20261028 MediumGlobalDyadicOwnership20261028
open MediumReceiverCutoffArithmetic20261028 OriginalSamePsiS1OwnedAtlas
open ActualLowConductorLogChoiceSourceOnly ActualWeightedFilteredBDHSourceOnly
open ActualCrudeWeightedVarianceSourceOnly ActualLowConductorQuotientSumSourceOnly

/-- The original smooth-factor deletion scale in appendix section 3. -/
def originalSmoothTrim (atom : MediumAtom) : ℝ :=
  atom.scale ^ (1/Real.log (Real.log atom.scale))

def originalNumericKeys (atom : MediumAtom) (z : ℝ) : Finset Key :=
  keyBank atom (strictReceiverCutoff z) (originalSmoothTrim atom)

def actualVarianceCap (atom : MediumAtom) (k : Key) : ℕ := Nat.floor (8*keyY atom k)

/-- This upper bound uses the actual retained moduli and their owner;
D is not an independent geometric parameter. -/
theorem occupied_keyD_le_trim_square {atom : MediumAtom} {z y : ℝ} {k : Key}
    (hy : 0 ≤ y) (hk : k ∈ keyBank atom z y) : keyD k ≤ y^2 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hpair,hret⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq1,hq2,hs,ht⟩ := hret
  have hd0 : actualD z q ≠ 0 := (split_nonzero z q).2.2.2.2.1
  have hD : keyD (owner z q) ≤ (actualD z q : ℝ) := by
    change (((2 : ℕ)^Nat.log2 (actualD z q) : ℕ) : ℝ) ≤ _
    exact_mod_cast Nat.log2_self_le hd0
  refine hD.trans ?_
  change ((smoothPart z q.1 * smoothPart z q.2 : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul]
  simpa only [pow_two] using mul_le_mul hs ht (Nat.cast_nonneg _) hy

/-- The subpower trim is eventually below a fixed power chosen from sigma. -/
theorem originalTrim_square_le {atom : MediumAtom} {sigma : ℝ}
    (hX : 1 ≤ atom.scale) (hsigma : 0 < sigma)
    (hll : 4/sigma ≤ Real.log (Real.log atom.scale)) :
    originalSmoothTrim atom ^ 2 ≤ atom.scale ^ (sigma/2) := by
  have hX0 : 0 < atom.scale := zero_lt_one.trans_le hX
  have hll0 : 0 < Real.log (Real.log atom.scale) := (div_pos (by norm_num) hsigma).trans_le hll
  have hmul : 4 ≤ Real.log (Real.log atom.scale)*sigma := (div_le_iff₀ hsigma).mp hll
  have hinv : 1/Real.log (Real.log atom.scale) ≤ sigma/4 :=
    (div_le_iff₀ hll0).mpr (by nlinarith)
  unfold originalSmoothTrim
  calc
    _ = atom.scale ^ ((1/Real.log (Real.log atom.scale))*2) := by
      rw [Real.rpow_mul hX0.le,Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- One threshold works for every atom and all occupied keys. -/
theorem exists_actual_margin_threshold {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ X : ℝ, x0 ≤ X →
      1 ≤ X ∧ 4/sigma ≤ Real.log (Real.log X) ∧ 8 ≤ X^(sigma/6) := by
  have hll : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hpow : Tendsto (fun X : ℝ => X^(sigma/6)) atTop atTop :=
    tendsto_rpow_atTop (by linarith : 0 < sigma/6)
  have he : ∀ᶠ X : ℝ in atTop,
      1 ≤ X ∧ 4/sigma ≤ Real.log (Real.log X) ∧ 8 ≤ X^(sigma/6) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),hll.eventually_ge_atTop (4/sigma),
      hpow.eventually_ge_atTop (8 : ℝ)] with X hX hLL hP
    exact ⟨hX,hLL,hP⟩
  obtain ⟨x1,hx1⟩ := eventually_atTop.mp he
  refine ⟨max 2 x1,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro X hX
  exact hx1 X ((le_max_right 2 x1).trans hX)

/-- Exact Q=floor(8Y) gates for the original atom and occupied strict
receiver. No previously desired variance estimate is used. -/
theorem actualVarianceCap_gates
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (hsigma : 0 < sigma)
    (hX : 1 ≤ atom.scale) (hll : 4/sigma ≤ Real.log (Real.log atom.scale))
    (h8 : 8 ≤ atom.scale^(sigma/6)) (z : ℝ) (k : Key)
    (hk : k ∈ originalNumericKeys atom z) :
    1 ≤ actualVarianceCap atom k ∧
      actualVarianceCap atom k ≤ Nat.floor (2*atom.U) ∧
      (actualVarianceCap atom k : ℝ) ≤ atom.scale ∧
      (actualVarianceCap atom k : ℝ) ≤
        (Nat.floor (2*atom.U) : ℝ)*atom.scale^(-(sigma/3)) := by
  have hU : 1 ≤ atom.U := hA.1
  have hV : 1 ≤ atom.V := hA.2.1
  have hQ : 1 ≤ atom.Q1 := hA.2.2.1
  have hX0 : 0 < atom.scale := zero_lt_one.trans_le hX
  have hU0 : 0 ≤ atom.U := zero_le_one.trans hU
  have hN : atom.U ≤ (Nat.floor (2*atom.U) : ℝ) := U_le_actual_prefix hU
  have hD1 : 1 ≤ keyD k := by
    exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2) : 1 ≤ (2 : ℕ)^k.d)
  have hy0 : 0 ≤ originalSmoothTrim atom := Real.rpow_nonneg hX0.le _
  have hD := (occupied_keyD_le_trim_square hy0 hk).trans (originalTrim_square_le hX hsigma hll)
  have hfirst : atom.Q1 ≤ atom.U*atom.scale^(-sigma) := hA.2.2.2.2.2.2.2.2.1.le
  have hY : keyY atom k ≤ atom.U*atom.scale^(-(sigma/2)) := by
    unfold keyY
    calc
      _ ≤ (atom.U*atom.scale^(-sigma))*atom.scale^(sigma/2) :=
        mul_le_mul hfirst hD (by dsimp [keyD]; positivity) (by positivity)
      _ = _ := by
        rw [mul_assoc,← Real.rpow_add hX0]
        congr 1
        congr 1
        ring
  have hY1 : 1 ≤ keyY atom k := by
    dsimp only [keyY]
    nlinarith [mul_le_mul hQ hD1 zero_le_one (zero_le_one.trans hQ)]
  have h8Y : 8*keyY atom k ≤ atom.U*atom.scale^(-(sigma/3)) := by
    calc
      _ ≤ 8*(atom.U*atom.scale^(-(sigma/2))) := mul_le_mul_of_nonneg_left hY (by norm_num)
      _ ≤ atom.scale^(sigma/6)*(atom.U*atom.scale^(-(sigma/2))) :=
        mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = _ := by
        rw [mul_comm _ (atom.U*_),mul_assoc,← Real.rpow_add hX0]
        congr 1
        congr 1
        ring
  have hf : (actualVarianceCap atom k : ℝ) ≤ 8*keyY atom k :=
    Nat.floor_le (by linarith : 0 ≤ 8*keyY atom k)
  have hsmall : atom.scale^(-(sigma/3)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hX
      (show -(sigma/3) ≤ 0 by linarith)
  have hcapU : (actualVarianceCap atom k : ℝ) ≤ atom.U :=
    hf.trans (h8Y.trans (by simpa using mul_le_mul_of_nonneg_left hsmall hU0))
  have hUx : atom.U ≤ atom.scale := by
    change atom.U ≤ atom.U*atom.V
    exact le_mul_of_one_le_right hU0 hV
  refine ⟨(Nat.one_le_floor_iff (8*keyY atom k)).mpr (by linarith : 1 ≤ 8*keyY atom k),?_,
    hcapU.trans hUx,?_⟩
  · exact_mod_cast hcapU.trans hN
  · exact hf.trans (h8Y.trans (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hX0.le _)))

/-- (14) at the actual cap, strict receiver and original smooth deletion
scale. Constants precede z, the occupied key and auxiliary r. -/
theorem uniformAuxiliarySW_actual_medium_atom_variance
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) (w : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, ∀ k ∈ originalNumericKeys (F i) z,
        ∀ r : ℕ, 1 ≤ r →
          weightedVariance (F i) (actualVarianceCap (F i) k) r w ≤
            C*tau r^(2*C0)*(Nat.floor (2*(F i).U) : ℝ)^2/(Real.log (F i).scale)^A := by
  obtain ⟨C,hC,xb,hxb,hbound⟩ :=
    uniformAuxiliarySW_weighted_filtered_BDH F B C0 sigma kappa c0 hadmissible hSW
      (by linarith : 0 < sigma/3) A hA w
  obtain ⟨xm,hxm,hmargin⟩ := exists_actual_margin_threshold hsigma
  refine ⟨C,hC,max xb xm,lt_of_lt_of_le hxb (le_max_left _ _),?_⟩
  intro i hx z k hk r hr
  have hxB : xb ≤ (F i).scale := (le_max_left _ _).trans hx
  have hxM : xm ≤ (F i).scale := (le_max_right _ _).trans hx
  obtain ⟨hX,hll,h8⟩ := hmargin _ hxM
  obtain ⟨hQ,hQN,hQX,hQscale⟩ := actualVarianceCap_gates (hadmissible i) hsigma hX hll h8 z k hk
  exact hbound i hxB (actualVarianceCap (F i) k) r hQ hr hQN hQX hQscale

end
end ImbalancedChen.Part3.ActualMediumVarianceAtomBindingSourceOnly
