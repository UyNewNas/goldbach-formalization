import ImbalancedChen.P4AFull87ClusteredRoughWords
import ImbalancedChen.P4AOriginalNewFifthPaidDensity
import ImbalancedChen.P4AActualMediumProductCeiling

/-! The actual T05 paid coefficient has nonzero moduli above the
necessary exponent for a whole-box medium tensor. The statement fixes
one excess exponent before small-prime precision and before the targets.
No assertion about the magnitude of the signed discrepancy follows. -/
namespace ImbalancedChen.P4AFull87UnionMediumSupportObstruction
noncomputable section
open scoped Classical BigOperators
open P4AFull87ClusteredRoughWords P5OriginalCommonRefinedConstructor VariableEnvelope

private theorem pick_rank {s theta B : ℝ} (hs : 0<s) (hst : s<theta) (hB : 0<B) :
    ∃ k : ℕ, Even k ∧ 0<k ∧ ∃ t : ℝ, 0<t ∧ t<B ∧ s<k*t ∧ (k+2:ℝ)*t<theta := by
  let h := (s+theta)/2
  have hs' : s<h := by dsimp [h]; linarith
  have ht' : h<theta := by dsimp [h]; linarith
  have hh := hs.trans hs'
  obtain ⟨m,hm⟩ := exists_nat_gt (max (h/B) ((2*h)/(theta-h)))
  let k := 2*(m+1)
  have hk : 0<k := by dsimp [k]; positivity
  have hmk : (m:ℝ)<k := by dsimp [k]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hk' : 0<(k:ℝ) := by exact_mod_cast hk
  have hbound := (div_lt_iff₀ hB).mp
    ((le_max_left _ _).trans_lt (hm.trans hmk) : h/B < k)
  have hgap := (div_lt_iff₀ (sub_pos.mpr ht')).mp
    ((le_max_right _ _).trans_lt (hm.trans hmk) : 2*h/(theta-h)<k)
  have heq : (k:ℝ)*(h/k)=h := by field_simp
  refine ⟨k,⟨m+1,by dsimp [k]; omega⟩,hk,h/k,div_pos hh hk',
    (div_lt_iff₀ hk').mpr (by linarith),by simpa only [heq] using hs',?_⟩
  calc
    ((k:ℝ)+2)*(h/k) = ((k+2)*h)/k := by ring
    _ < theta := (div_lt_iff₀ hk').mpr (by nlinarith)

private theorem integer_lengths {t U : ℝ} (ht : 0<t) (hU : t<U)
    (k D0 : ℕ) :
    ∃ D : ℕ, D0<D ∧ ∃ j : ℕ, 1≤j ∧ (D:ℝ)*t ≤ j ∧ (j:ℝ)+k < D*U := by
  obtain ⟨D,hD⟩ := exists_nat_gt (max (D0:ℝ) (((k:ℝ)+1)/(U-t)))
  have h₀ : D0<D := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hD : (D0:ℝ)<D)
  have hD' : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hg := (div_lt_iff₀ (sub_pos.mpr hU)).mp
    (lt_of_le_of_lt (le_max_right _ _) hD : ((k:ℝ)+1)/(U-t)<D)
  let j := ⌈(D:ℝ)*t⌉₊
  have hlo : (D:ℝ)*t≤j := Nat.le_ceil _
  have hhi : (j:ℝ)<(D:ℝ)*t+1 := Nat.ceil_lt_add_one (mul_pos hD' ht).le
  have hj : 0<(j:ℝ) := (mul_pos hD' ht).trans_le hlo
  refine ⟨D,h₀,j,by exact_mod_cast hj,hlo,by nlinarith⟩

abbrev first (d : OriginalData) := logPrimeMeshPoint 0 (19/96) d.m 1

theorem original_data_support (d : OriginalData) (hdOmega : 0<d.omega)
    (hdE : (d.e:ℝ)<11/64000) (hfirst : first d ≤ extendedFirstStop-4*(d.e:ℝ))
    (n : ℕ) {delta : ℝ} (hd : 0<delta) :
    ∃ s : ℝ, VariableEnvelope.cap<s ∧ ∃ omega0 : ℝ, 0<omega0 ∧
      ∀ omega : ℝ, omega<omega0 → ∀ D0 : ℕ, ∃ D : ℕ, D0<D ∧
      let N := 2^D
      let w := (N:ℝ)^omega
      let z := (N:ℝ)^(19/96:ℝ)
      let keep := P4AFull87UnionCompilerPayment.keep delta n d N
      let tag := P4AFull87DataCompilerReads.tag delta hd n d N
      ∀ tau L : ℝ, 1<L → ∃ x ∈ P4AUpperTaggedBetaAttachment.support N N w z,
        (N:ℝ)^s < (x:ℝ) ∧ P4AUpperTaggedBetaAttachment.rho keep tag N N w z tau L x=1 := by
  let theta := HistoricalThirdCoarse.initial (d.e:ℝ)
  have hi : VariableEnvelope.cap<theta := by
    dsimp [theta,HistoricalThirdCoarse.initial,extendedDistributionCap,VariableEnvelope.cap]
    linarith
  let s := (VariableEnvelope.cap+theta)/2
  have hcs : VariableEnvelope.cap<s := by dsimp [s]; linarith
  have hs : 0<s := (by norm_num [VariableEnvelope.cap] : (0:ℝ)<VariableEnvelope.cap).trans hcs
  have hst : s<theta := by dsimp [s]; linarith
  let B := min d.omega (min (1/100:ℝ) (min (first d) (19/96:ℝ)))
  have hf : 0<first d := by dsimp [first,logPrimeMeshPoint,logPrimeMeshStep]; positivity
  have hB : 0<B := lt_min hdOmega (lt_min (by norm_num) (lt_min hf (by norm_num)))
  obtain ⟨k,he,hk,t,ht,htB,hks,hkt⟩ := pick_rank hs hst hB
  let U := min B (theta/((k:ℝ)+2))
  have hK : (0:ℝ)<(k:ℝ)+2 := by positivity
  have hU : t<U := lt_min htB ((lt_div_iff₀ hK).mpr (by linarith))
  refine ⟨s,hcs,t,ht,?_⟩
  intro omega hw D0
  obtain ⟨D,hD,j,hj,hjt,hjU⟩ := integer_lengths ht hU k D0
  have hDN : 0<D := by omega
  have hDR : 0<(D:ℝ) := by exact_mod_cast hDN
  have hkR : 0<(k:ℝ) := by exact_mod_cast hk
  have hlim {b : ℝ} (h : U≤b) : (j:ℝ)+k<D*b :=
    hjU.trans_le (mul_le_mul_of_nonneg_left h hDR.le)
  have hBU : U≤B := min_le_left _ _
  have h1 : U≤d.omega := hBU.trans (min_le_left _ _)
  have h2 := hBU.trans (min_le_right _ _)
  have h3 := h2.trans (min_le_right _ _)
  have hc := (lt_div_iff₀ hK).mp (show (j:ℝ)+k < D*theta/((k:ℝ)+2) by
    rw [mul_div_assoc]; exact hlim (min_le_right _ _))
  have hsc : (D:ℝ)*s < j*k := by
    calc
      (D:ℝ)*s < D*(k*t) := mul_lt_mul_of_pos_left hks hDR
      _ = (D*t)*k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hjt hkR.le
  refine ⟨D,hD,?_⟩
  intro tau L hL
  exact clustered_target d n k j D he hj hDN delta omega (19/96) s hd (by norm_num)
    ((mul_lt_mul_of_pos_left hw hDR).trans_le hjt) hsc (hlim (h3.trans (min_le_right _ _)))
    (hlim h1) (hlim (h2.trans (min_le_left _ _))).le (hlim (h3.trans (min_le_left _ _)))
    hfirst hc tau L hL

/-- Same concrete Q, rho, target, beta level and per-prime z as in T05.
The positive power is uniform in the sufficiently small physical omega. -/
theorem paid_union_nonzero_above_cap (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ)
    (ha : 0<a) (he : (e:ℝ)<11/64000) (hq : 0<q) :
    ∃ s : ℝ, VariableEnvelope.cap<s ∧ ∃ omega0 : ℝ, 0<omega0 ∧
      ∀ nu beta : ℝ, 0<nu → 0<beta → nu*beta^2<omega0 → ∀ D0 : ℕ,
      ∃ D : ℕ, D0<D ∧ let N := 2^D
      let w := (N:ℝ)^(nu*beta^2)
      let L := (N:ℝ)^(nu*beta)
      ∀ tau : ℝ, ∃ x ∈ P4AOriginalFull87CompiledCounting.moduli N w, (N:ℝ)^s < (x:ℝ) ∧
        P4AOriginalNewFifthPaidDensity.rho r n e q a N w tau L x=1 := by
  have hfirst : first (P4AOriginalNewFifthUnion.data e q a) ≤ extendedFirstStop-4*(e:ℝ) := by
    change logPrimeMeshPoint 0 (19/96) (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) 1 ≤ _
    simp only [logPrimeMeshPoint,Nat.cast_one,one_mul,zero_add,
      P1OriginalFifthGrid400RefinedFullBoxCover.refined_step q hq,extendedFirstStop]
    have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
    have hw : (1:ℝ)/(2400*q) ≤ 1/2400 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  obtain ⟨s,hs,t,ht,H⟩ := original_data_support (P4AOriginalNewFifthUnion.data e q a)
    ha he hfirst n (P4AOriginalFull87HistoryCore.width_pos r)
  refine ⟨s,hs,t,ht,?_⟩
  intro nu beta hnu hb hw D0
  obtain ⟨D,hD,h⟩ := H (nu*beta^2) hw D0
  refine ⟨D,hD,?_⟩
  intro tau
  have hN : 1 < 2^D := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by omega)
  exact h tau _ (Real.one_lt_rpow (by exact_mod_cast hN) (mul_pos hnu hb))

/-- The unmodified three dyadic factor carriers of one local M atom.
The signed discrepancy on the counted primes is not part of membership. -/
def mediumSupport (C : ℝ) (N x : ℕ) : Prop :=
  ∃ (atom : Part3.MediumAtom) (B : ℕ) (sig kap c0 : ℝ), 0≤sig ∧
    Part3.MediumAdmissible B sig kap c0 atom ∧ 1≤atom.scale ∧
    atom.scale≤C*(N:ℝ) ∧ atom.residue.natAbs=N ∧
    ∃ a ∈ Part3.factorCarrier atom.Q1, ∃ b ∈ Part3.factorCarrier atom.Q2,
    ∃ c ∈ Part3.factorCarrier atom.Q3, a*b*c=x

private theorem excludes_medium {C s : ℝ} (hC : 0<C) {N x : ℕ} (hN : 1<N)
    (hq : (N:ℝ)^s < (x:ℝ))
    (hgap : 8*Real.log 8+5*Real.log C < (8*s-(5-7/32))*Real.log N) :
    ¬mediumSupport C N x := by
  rintro ⟨atom,B,sig,kap,c0,hsig,hm,hscale,hup,hr,a,ha,b,hb,c,hc,hprod⟩
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hxR : (0:ℝ)<x := (Real.rpow_pos_of_pos hNR _).trans hq
  have hx : 0<x := by exact_mod_cast hxR
  have hl := P4AActualMediumProductCeiling.physical_ceiling hsig hm hscale
    (by rw [hr]; omega) ha hb hc (by simpa only [hprod] using hx)
  rw [hprod,hr] at hl
  have hlocal := Real.log_le_log (zero_lt_one.trans_le hscale) hup
  rw [Real.log_mul hC.ne' hNR.ne'] at hlocal
  have hpoint := Real.log_lt_log (Real.rpow_pos_of_pos hNR _) hq
  rw [Real.log_rpow hNR] at hpoint
  nlinarith

/-- No M-only whole-box representation of the paid coefficient on its
literal complete high-rank support in the manuscript local scale range.
All displayed choices, including the multiplicative chart constant C,
precede the cofinal even targets. -/
theorem paid_union_outside_medium (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ)
    (ha : 0<a) (he : (e:ℝ)<11/64000) (hq : 0<q) :
    ∃ omega0 : ℝ, 0<omega0 ∧ ∀ nu beta : ℝ, 0<nu → 0<beta → nu*beta^2<omega0 →
      ∀ C : ℝ, 0<C → ∀ D0 : ℕ, ∃ D : ℕ, D0<D ∧ let N := 2^D
      let w := (N:ℝ)^(nu*beta^2)
      let L := (N:ℝ)^(nu*beta)
      ∀ tau : ℝ, ∃ x ∈ P4AOriginalFull87CompiledCounting.moduli N w,
        P4AOriginalNewFifthPaidDensity.rho r n e q a N w tau L x=1 ∧ ¬mediumSupport C N x := by
  obtain ⟨s,hs,t,ht,H⟩ := paid_union_nonzero_above_cap r n e q a ha he hq
  refine ⟨t,ht,?_⟩
  intro nu beta hnu hb hw C hC D0
  have hrate : 0 < (8*s-(5-7/32))*Real.log 2 :=
    mul_pos (by dsimp [VariableEnvelope.cap] at hs; linarith) (Real.log_pos (by norm_num))
  obtain ⟨M,hM⟩ := exists_nat_gt ((8*Real.log 8+5*Real.log C)/((8*s-(5-7/32))*Real.log 2))
  obtain ⟨D,hD,h⟩ := H nu beta hnu hb hw (max D0 M)
  have hD' : D0<D := (le_max_left _ _).trans_lt hD
  have hMc : (M:ℝ)<D := by exact_mod_cast ((le_max_right _ _).trans_lt hD : M<D)
  have hlarge := (div_lt_iff₀ hrate).mp (hM.trans hMc)
  have hN : 1 < 2^D := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by omega)
  refine ⟨D,hD',?_⟩
  intro tau
  obtain ⟨x,hx,hbig,hval⟩ := h tau
  refine ⟨x,hx,hval,excludes_medium hC hN hbig ?_⟩
  push_cast
  rw [Real.log_pow]
  nlinarith

end
end ImbalancedChen.P4AFull87UnionMediumSupportObstruction
