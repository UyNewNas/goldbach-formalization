import ImbalancedChen.Part3ActualMediumVarianceAtomBinding
import ImbalancedChen.Part3OriginalLambdaTrimPoissonFamily
import ImbalancedChen.Part3ZRegularSpectralPolynomial
import ImbalancedChen.Part3ZExceptionalSpectralPolynomial
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original (23)--(26) scales on the ACTUAL occupied rough owner, not on
an arbitrary independently licensed family. Its harmless dyadic factors
are explicit: R<=2Q3, S<=2Q2 and rough product<=4RS. The actual Poisson
keyRealH, original q and M,N are retained. This file proves scaling and
normalization only, not a classical spectral estimate or a bare bound.
-/

namespace ImbalancedChen.Part3.ActualOriginalSpectralScales20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumCanonicalFixedBlock20261028 MediumGlobalDyadicOwnership20261028
open OriginalSamePsiS1OwnedAtlas ActualMediumVarianceAtomBindingSourceOnly
open OriginalLambdaTrimPoissonFamily20261028

def theta : ℝ := 7/32
def roughR (k : Key) : ℝ := ((2 : ℕ)^k.v : ℕ)
def roughS (k : Key) : ℝ := ((2 : ℕ)^k.u : ℕ)
def spectralB (atom : MediumAtom) (k : Key) : ℝ := atom.U*roughR k
def spectralC (atom : MediumAtom) (k : Key) : ℝ := atom.U*roughR k*roughS k
def spectralU (atom : MediumAtom) (k : Key) : ℝ :=
  atom.U*(roughR k)^2*(roughS k)^3/atom.V
def spectralZ (k : Key) : ℝ := (roughS k)^2
def countingF (atom : MediumAtom) : ℝ := atom.U/atom.Q1
def D0 (atom : MediumAtom) (k : Key) : ℝ :=
  atom.U^2*(roughR k)^2*roughS k/atom.scale
def D1 (atom : MediumAtom) (k : Key) : ℝ :=
  (atom.residue.natAbs : ℝ)^theta*atom.U*atom.Q1*
    (roughR k)^2*(roughS k)^5/atom.scale^2
def D2 (atom : MediumAtom) (k : Key) : ℝ :=
  atom.U^(1+2*theta)*atom.Q1*(roughR k)^(2+2*theta)*
    (roughS k)^(5-2*theta)/atom.scale^2

theorem rough_scales_one_le (k : Key) : 1 ≤ roughR k ∧ 1 ≤ roughS k := by
  have hr : 1 ≤ (2 : ℕ)^k.v := Nat.succ_le_iff.mpr (pow_pos (by norm_num) _)
  have hs : 1 ≤ (2 : ℕ)^k.u := Nat.succ_le_iff.mpr (pow_pos (by norm_num) _)
  exact ⟨by exact_mod_cast hr,by exact_mod_cast hs⟩

private theorem roughPart_le_source {q : ℕ} (hq : q ≠ 0) (z : ℝ) :
    roughPart z q ≤ q := by
  have hs : 1 ≤ smoothPart z q := Nat.one_le_iff_ne_zero.mpr (smoothPart_supported z q).1
  have hmul := Nat.mul_le_mul_right (roughPart z q) hs
  simpa only [one_mul,smooth_mul_rough z hq] using hmul

/-- Actual occupied source witnesses supply all rough-scale bounds.
No caps are added as fields of a putative spectral interface. -/
theorem actual_rough_owner_geometry {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z y : ℝ) (k : Key)
    (hk : k ∈ keyBank atom z y) :
    roughR k ≤ 2*atom.Q3 ∧ roughS k ≤ 2*atom.Q2 ∧
      keyR k ≤ 4*roughR k*roughS k := by
  obtain ⟨q,hq,howner⟩ := mem_image.mp hk
  obtain ⟨hpair,h2nz,h3nz,hsy,hty⟩ := mem_filter.mp hq
  obtain ⟨h2,h3⟩ := mem_product.mp hpair
  obtain ⟨hs,ht,hu,hv,hd,hw⟩ := (owner_eq_iff_windows z q k).mp howner
  have hulo : roughS k ≤ (roughPart z q.1 : ℝ) := by
    exact_mod_cast (mem_Ico.mp hu).1
  have hvlo : roughR k ≤ (roughPart z q.2 : ℝ) := by
    exact_mod_cast (mem_Ico.mp hv).1
  have huhi : (roughPart z q.1 : ℝ) ≤ 2*roughS k := by
    have h := (mem_Ico.mp hu).2.le
    simpa only [roughS,pow_succ,Nat.cast_mul,Nat.cast_ofNat,mul_comm] using
      (show (roughPart z q.1 : ℝ) ≤ ((2^(k.u+1) : ℕ) : ℝ) by exact_mod_cast h)
  have hvhi : (roughPart z q.2 : ℝ) ≤ 2*roughR k := by
    have h := (mem_Ico.mp hv).2.le
    simpa only [roughR,pow_succ,Nat.cast_mul,Nat.cast_ofNat,mul_comm] using
      (show (roughPart z q.2 : ℝ) ≤ ((2^(k.v+1) : ℕ) : ℝ) by exact_mod_cast h)
  have hq2 : (q.1 : ℝ) ≤ 2*atom.Q2 :=
    (show (q.1 : ℝ) ≤ Nat.floor (2*atom.Q2) by exact_mod_cast (mem_Icc.mp h2).2).trans
      (Nat.floor_le (by linarith [hA.2.2.2.1]))
  have hq3 : (q.2 : ℝ) ≤ 2*atom.Q3 :=
    (show (q.2 : ℝ) ≤ Nat.floor (2*atom.Q3) by exact_mod_cast (mem_Icc.mp h3).2).trans
      (Nat.floor_le (by linarith [hA.2.2.2.2.1]))
  have hr2 : (roughPart z q.1 : ℝ) ≤ q.1 := by exact_mod_cast roughPart_le_source h2nz z
  have hr3 : (roughPart z q.2 : ℝ) ≤ q.2 := by exact_mod_cast roughPart_le_source h3nz z
  refine ⟨hvlo.trans (hr3.trans hq3),hulo.trans (hr2.trans hq2),?_⟩
  have hW : keyR k ≤ (roughPart z q.1 : ℝ)*(roughPart z q.2 : ℝ) := by
    have h := (mem_Ico.mp hw).1
    simpa only [keyR,actualW,canonicalFactor,Nat.cast_mul] using
      (show (((2 : ℕ)^k.w : ℕ) : ℝ) ≤ (actualW z q : ℝ) by exact_mod_cast h)
  have hR0 := (rough_scales_one_le k).1
  have hprod := mul_le_mul huhi hvhi (Nat.cast_nonneg (roughPart z q.2))
    (show 0 ≤ 2*roughS k by have := (rough_scales_one_le k).2; linarith)
  exact hW.trans (hprod.trans_eq (by ring))

/-- Literal normalization of the upper spectral scales. These
identities use x=M*N and retain the full original rough powers. -/
theorem actual_spectral_normalizations {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) :
    spectralU atom k/spectralZ k = D0 atom k ∧
      spectralC atom k*spectralB atom k*spectralZ k = atom.scale*spectralU atom k ∧
      spectralC atom k/spectralB atom k = roughS k ∧
      spectralC atom k ≤ spectralB atom k*spectralZ k := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only [spectralU,spectralZ,D0,MediumAtom.scale]
    field_simp [hN.ne',hM.ne',hS.ne'] <;> ring
  · dsimp only [spectralC,spectralB,spectralZ,spectralU,MediumAtom.scale]
    field_simp [hM.ne'] <;> ring
  · dsimp only [spectralC,spectralB]
    field_simp [hN.ne',hR.ne']
  · have hs := (rough_scales_one_le k).2
    have hsq : roughS k ≤ (roughS k)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (by dsimp [spectralB]; positivity)

/-- The actual source real H is bounded on the same rough owner.
Its preliminary d and log^5 costs remain explicit, not x^epsilon. -/
theorem actual_keyH_short_ratio {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z y : ℝ) (k : Key)
    (hk : k ∈ keyBank atom z y) :
    keyRealH atom k/roughS k ≤
      (16*keyD k*(Real.log atom.scale)^5)*(atom.Q1/atom.U)*D0 atom k := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hx : 1 < atom.scale := by
    have he : 1 < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
    exact he.trans hA.2.2.2.2.2.1
  have hlog : 0 ≤ (Real.log atom.scale)^5 := pow_nonneg (Real.log_nonneg hx.le) _
  have hW0 : 0 ≤ keyR k := by dsimp [keyR]; positivity
  have hW := (actual_rough_owner_geometry hA z y k hk).2.2
  have hsq := pow_le_pow_left₀ hW0 hW 2
  have hQ : 0 ≤ atom.Q1 := zero_le_one.trans hA.2.2.1
  have hD : 0 ≤ keyD k := by dsimp [keyD]; positivity
  unfold keyRealH
  calc
    _ ≤ (atom.Q1*keyD k*(4*roughR k*roughS k)^2*
        (Real.log atom.scale)^5/atom.V)/roughS k := by
      apply div_le_div_of_nonneg_right _ hS.le
      apply div_le_div_of_nonneg_right _ hM.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (mul_nonneg hQ hD)) hlog
    _ = _ := by
      dsimp only [D0,MediumAtom.scale]
      field_simp [hN.ne',hM.ne',hS.ne'] <;> ring

/-- Actual regular polynomial comparison at the original spectral
scales. This consumes the proved physical prefactor, not a spectral
estimate; V is an ACTUAL retained nonempty common m block. -/
theorem actual_regular_return_polynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (nu : ℕ) (hnu : 0 < nu) (V W : ℝ)
    (ha : 0 < (atom.residue.natAbs : ℝ)) (hV : 0 < V) (hW : 1 ≤ W)
    (hcut : V ≤ W*spectralC atom k/spectralB atom k) :
    (spectralB atom k/spectralC atom k)^2*
      (V*(spectralC atom k)^4*spectralZ k/
        ((atom.residue.natAbs : ℝ)*V*spectralU atom k+
          (spectralC atom k)^2*spectralZ k))*
      (spectralU atom k/(nu : ℝ)+spectralZ k+
        (atom.residue.natAbs : ℝ)*V*spectralU atom k/(spectralC atom k)^2)*
      (V+spectralZ k+
        (atom.residue.natAbs : ℝ)*V*spectralU atom k/(spectralC atom k)^2) ≤
      W^2*(spectralC atom k*(spectralU atom k/(nu : ℝ)+spectralZ k)*
        (spectralC atom k+spectralB atom k*spectralZ k)+
          (atom.residue.natAbs : ℝ)*spectralU atom k*spectralZ k) := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  have hnuR : (0 : ℝ) < nu := by exact_mod_cast hnu
  exact ImbalancedChen.P3ZRegularSpectralPolynomial.regular_return_le_inflated_cutoff
    ha (by dsimp [spectralU]; positivity) (by dsimp [spectralC]; positivity)
    (by dsimp [spectralB]; positivity) (by dsimp [spectralU]; positivity)
    hV (by dsimp [spectralZ]; positivity) hW hcut

/-- The improved exceptional return retains all powers of D=Bspec
and costs W^(2-2theta), hence at most W^2. No large-a loss is dropped. -/
theorem actual_exceptional_return_polynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (V W : ℝ) (ha : 0 < (atom.residue.natAbs : ℝ))
    (hV : 0 < V) (hW : 1 ≤ W)
    (hcut : V ≤ W*spectralC atom k/spectralB atom k) :
    ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalReturn
      (atom.residue.natAbs : ℝ) (spectralU atom k) (spectralC atom k)
      (spectralB atom k) V (spectralZ k) theta ≤
      W^2*ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalPolynomial
        (spectralU atom k) (spectralC atom k) (spectralB atom k) (spectralZ k) theta := by
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hM : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hR : 0 < roughR k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).1
  have hS : 0 < roughS k := lt_of_lt_of_le zero_lt_one (rough_scales_one_le k).2
  exact ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptional_return_le_inflated_cutoff
    ha (by dsimp [spectralU]; positivity) (by dsimp [spectralC]; positivity)
    (by dsimp [spectralB]; positivity) hV (by dsimp [spectralZ]; positivity)
    (by norm_num [theta]) (by norm_num [theta]) hW hcut

end
end ImbalancedChen.Part3.ActualOriginalSpectralScales20261028
