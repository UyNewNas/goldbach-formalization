import ImbalancedChen.Part5OriginalH430ClassicalRootCredits
import ImbalancedChen.Part5OriginalH430SeedSameCarrierPP

/-! The original rejected Γ5 pair on a classical U3 root. Its marked
integers retain the old half-open interval and the closed rejected wall.
All three scales below are computed from this root's single frozen Q. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalBadPairGeometry
noncomputable section
open Set Real Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedUnsiftedSource (pairLabels badPair)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels pair_data pair_eq pair_prod_pos)
open P2SeedOmegaLiteralFibre (a0 a2)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RootIntervalTheta (clampLevel)
open Part5OriginalH430ClassicalRootCredits (classical_Q_exact)
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430TaggedArithmeticReceivers (original_band_prime original_band_geometry)
open scoped Classical BigOperators

def floorScale (N : ℕ) : ℝ := (N:ℝ)^(1/200:ℝ)

structure Geometry (N p : ℕ) (Q : ℝ) (l : List ℕ) : Prop where
  outer : p.Prime ∧ p.Coprime N
  pair : l = [l.getD 0 0,l.getD 1 0]
  first : (l.getD 0 0).Prime ∧ (l.getD 0 0).Coprime N
  second : (l.getD 1 0).Prime ∧ (l.getD 1 0).Coprime N
  order : l.getD 0 0 < l.getD 1 0
  scale : floorScale N ≤ (p:ℝ) ∧ floorScale N ≤ (l.getD 0 0:ℝ) ∧
    floorScale N ≤ (l.getD 1 0:ℝ)
  big : 0 < p*l.prod ∧ p*l.prod ≤ N ∧ (p*l.prod).Coprime N
  parent : 1 < Q/(p:ℝ)
  child : 1 < Q/((p*l.prod:ℕ):ℝ)
  cutoff_order : floorScale N ≤ cutoff Q (p*l.prod) 2 ∧
    cutoff Q (p*l.prod) 2 ≤ cutoff Q p (227/50)
  height : floorScale N ≤ (N:ℝ)/(p*l.prod:ℕ) ∧ 1 < cutoff Q p (227/50)
  band : let x := (N:ℝ)/(p*l.prod:ℕ)
    let z := cutoff Q p (227/50)
    log x/log z ∈ Icc (2:ℝ) 100
  coordinates : log (l.getD 0 0:ℝ)/log (Q/p) ≤ a2 ∧
    log (l.getD 1 0:ℝ)/log (Q/p) ≤ a2

theorem actual_pair {N n p : ℕ} {τ : ℝ} (hN : 2 ≤ N)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p ∈ classicalBand N) {l : List ℕ} (hl : l ∈ badLabels N (rootQ N n .U3 τ p) p) :
    Geometry N p (rootQ N n .U3 τ p) l := by
  let Q := rootQ N n .U3 τ p
  let t := physicalPrime N p
  let R := Q/(p:ℝ)
  let a := l.getD 0 0
  let b := l.getD 1 0
  let D := p*l.prod
  let y := cutoff Q p (227/50)
  let J := Q/(D:ℝ)
  let x := (N:ℝ)/(D:ℝ)
  let w := cutoff Q D 2
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hN0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  have hpp := original_band_prime (Finset.mem_filter.mp hp).1
  have hpr : (0:ℝ)<p := Nat.cast_pos.mpr hpp.1.pos
  have hcl := classical_geometry (m:=0) hN hτ hτ' hn hp
  have hR : 1 < R := hcl.1
  have hR0 := zero_lt_one.trans hR
  have hRlog := log_pos hR
  obtain ⟨hlp, hbad⟩ := mem_filter.mp hl
  have he : l=[a,b] := pair_eq hlp
  have hwA := mem_primeWindow.mp ((pair_data hlp).2.2 a (by rw [he]; simp))
  have hwB := mem_primeWindow.mp ((pair_data hlp).2.2 b (by rw [he]; simp))
  have ha : (0:ℝ)<a := Nat.cast_pos.mpr hwA.1.pos
  have hb : (0:ℝ)<b := Nat.cast_pos.mpr hwB.1.pos
  have hab : a<b := by simpa [he] using (pair_data hlp).2.1
  have hD : D=p*a*b := by dsimp [D]; rw [he]; simp [mul_assoc]
  have hd := Nat.mul_pos hpp.1.pos (pair_prod_pos hlp)
  have hdr : (0:ℝ)<D := Nat.cast_pos.mpr hd
  have hdc : D.Coprime N := by
    rw [hD,Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_left]
    exact ⟨⟨hpp.2,hwA.2.1⟩,hwB.2.1⟩
  have hQpos : 0<Q := Real.rpow_pos_of_pos hN0 _
  have hfl := frozenLevel_bounds (show 1/2-τ∈Icc (0:ℝ) 1 from ⟨by linarith,by linarith⟩) n
  have ht := original_band_geometry hN (Finset.mem_filter.mp hp).1
  have hlogp : log (p:ℝ)=t*log (N:ℝ) := (div_mul_cancel₀ _ hlog.ne').symm
  have hlogR : log R=(clampLevel n τ-t)*log (N:ℝ) := by
    rw [show R=(N:ℝ)^(clampLevel n τ)/(p:ℝ) by rw [R,Q,classical_Q_exact hp],
      log_div (rpow_pos_of_pos hN0 _).ne' hpr.ne',log_rpow hN0,hlogp]
    ring
  have hLo : 7/128 ≤ clampLevel n τ-t := by
    change 7/128 ≤ frozenLevel n (1/2-τ)-physicalPrime N p
    linarith only [hfl.2,hn,hτ',ht.2]
  have hLo' := mul_le_mul_of_nonneg_right hLo hlog.le
  rw [←hlogR] at hLo'
  have hLp : 1/200*log (N:ℝ)≤log (p:ℝ) := by
    have hta := (Finset.mem_filter.mp hp).2
    change Part5UpperTables.OriginalU34.tailCutoff ≤ t at hta
    rw [hlogp]
    apply mul_le_mul_of_nonneg_right _ hlog.le
    dsimp [Part5UpperTables.OriginalU34.tailCutoff] at hta
    linarith only [hta]
  have coord (q : ℕ) (hq : q∈primeWindow N (R^a0) (R^a2)) :
      a0*log R ≤ log (q:ℝ) ∧ log (q:ℝ) ≤ a2*log R := by
    have hv := mem_primeWindow.mp hq
    have h1 := log_le_log (rpow_pos_of_pos hR0 _) hv.2.2.1
    have h2 := log_le_log (Nat.cast_pos.mpr hv.1.pos) hv.2.2.2.le
    simpa only [log_rpow hR0] using And.intro h1 h2
  have hA := coord a ((pair_data hlp).2.2 a (by rw [he]; simp))
  have hB := coord b ((pair_data hlp).2.2 b (by rw [he]; simp))
  have hord := log_le_log ha (show (a:ℝ)≤b by exact_mod_cast hab.le)
  have hwall : log R≤2*log (a:ℝ)+log (b:ℝ) := by
    change Q ≤ (p:ℝ)*(a:ℝ)^2*(b:ℝ) at hbad
    have hh : R≤(a:ℝ)^2*(b:ℝ) := (div_le_iff₀ hpr).mpr (by linarith only [hbad])
    simpa only [log_mul (pow_pos ha _).ne' hb.ne',log_pow,Nat.cast_ofNat] using log_le_log hR0 hh
  have hdlog : log (D:ℝ)=log (p:ℝ)+log (a:ℝ)+log (b:ℝ) := by
    rw [hD,Nat.cast_mul,Nat.cast_mul,log_mul (mul_pos hpr ha).ne' hb.ne',log_mul hpr.ne' ha.ne']
  have hlogJ : log J=log R-log (a:ℝ)-log (b:ℝ) := by
    rw [show log J=log Q-log (D:ℝ) from log_div hQpos.ne' hdr.ne',hdlog,
      show log R=log Q-log (p:ℝ) from log_div hQpos.ne' hpr.ne']
    ring
  have hlogx : log x=log (N:ℝ)-log (D:ℝ) := log_div hN0.ne' hdr.ne'
  have hhalf := log_le_log hQpos hcl.2.2
  rw [log_rpow hN0] at hhalf
  have h2R : 2*log R ≤ log (N:ℝ)-log (p:ℝ) := by
    rw [show log R=log Q-log (p:ℝ) from log_div hQpos.ne' hpr.ne']
    linarith only [hhalf,mul_nonneg hτ hlog.le,log_nonneg (by exact_mod_cast hpp.1.one_le : (1:ℝ)≤p)]
  have hJ0 : 0<J := div_pos hQpos hdr
  have hx0 : 0<x := div_pos hN0 hdr
  have hw0 : 0<w := rpow_pos_of_pos hJ0 _
  have hy0 : 0<y := rpow_pos_of_pos hR0 _
  have hly : log y=a0*log R := by
    change log (R^(1/(227/50):ℝ)) = _
    rw [log_rpow hR0]; norm_num [a0]
  have hlw : log w=(1/2)*log J := log_rpow hJ0 _
  have hF : 0<floorScale N := rpow_pos_of_pos hN0 _
  have hlF : log (floorScale N)=(1/200)*log (N:ℝ) := log_rpow hN0 _
  have hA' := hA
  have hB' := hB
  norm_num [a0,a2] at hA' hB'
  have hly' := hly
  norm_num [a0] at hly'
  have hjs : 0 < log J := by linarith only [hlogJ,hA'.2,hB'.2,hRlog]
  have hy1 : 0 < log y := by linarith only [hly',hRlog]
  have hxl : 2*log y ≤ log x := by linarith only [h2R,hlogx,hdlog,hA'.2,hB'.2,hly',hRlog]
  have hxN : x ≤ N := div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hd)
  have hxlog := log_le_log hx0 hxN
  have hDle : D≤N := by
    have hh : log (D:ℝ)≤log (N:ℝ) := by linarith only [hxl,hlogx,hy1]
    exact_mod_cast (log_le_log_iff hdr hN0).mp hh
  refine ⟨hpp,he,⟨hwA.1,hwA.2.1⟩,⟨hwB.1,hwB.2.1⟩,hab,
    ⟨(log_le_log_iff hF hpr).mp (by linarith only [hlF,hLp]),
     (log_le_log_iff hF ha).mp (by linarith only [hlF,hLo',hA'.1,hlog]),
     (log_le_log_iff hF hb).mp (by linarith only [hlF,hLo',hB'.1,hlog])⟩,
    ⟨hd,hDle,hdc⟩,hR,(log_pos_iff hJ0.le).mp hjs,
    ⟨(log_le_log_iff hF hw0).mp (by linarith only [hlF,hlw,hlogJ,hA'.2,hB'.2,hLo',hlog]),
     (log_le_log_iff hw0 hy0).mp (by linarith only [hlw,hly',hlogJ,hord,hwall,hRlog])⟩,
    ⟨(log_le_log_iff hF hx0).mp (by linarith only [hlF,hxl,hly',hLo',hlog]),
      (log_pos_iff hy0.le).mp hy1⟩,
    ⟨(le_div_iff₀ hy1).mpr hxl,(div_le_iff₀ hy1).mpr (by linarith only [hxlog,hly',hLo',hlog])⟩,
    ⟨(div_le_iff₀ hRlog).mpr hA.2,(div_le_iff₀ hRlog).mpr hB.2⟩⟩

end
end ImbalancedChen.Part5OriginalH430ClassicalBadPairGeometry
