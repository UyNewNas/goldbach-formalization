import ImbalancedChen.P4AOriginalFiniteFallbackPhysicalRange

namespace ImbalancedChen.P4AOriginalFiniteFallbackCount
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy (F rho)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli compiled_modulus_dvd)

def jointIndex (B : Bank) (m : ℕ) := 76*(m+1)*(B.mesh+1)-1

theorem upper_majorant (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1<L) (hwL : (N:ℝ)^omega≤L) (hwz : (N:ℝ)^omega≤cutoff N)
    (hz : cutoff N≤(N:ℝ)) (x : ℕ) :
    (if x.Coprime (sieveProduct N (Nat.ceil (cutoff N))) then (1:ℝ) else 0) ≤
      physicalDivisorSum (moduli N ((N:ℝ)^omega)) (rho B r n e q a omega N tau L) x := by
  have h := P4AUpperTaggedBetaAttachment.rho_majorant (F B (width r) n (data e q a) omega N) (fun _ => [])
    N N ((N:ℝ)^omega) (cutoff N) tau L hL hwL hwz hz (x:ℤ)
  rw [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at h
  simpa only [Int.natAbs_natCast] using h

theorem count (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (tau L : ℝ)
    (hL : 1<L) (hwL : (N:ℝ)^omega≤L) (hwz : (N:ℝ)^omega≤cutoff N) (hz : cutoff N≤(N:ℝ))
    {b T : ℝ} (hb : 0<b) (hb1 : b<1) (hT : 0<T) (hgate : (Nat.ceil (cutoff N):ℝ)≤T^(b/(1+b))) :
    let Q := moduli N ((N:ℝ)^omega)
    let rho := rho B r n e q a omega N tau L
    (RealB b N:ℝ) ≤ ((realHalfProductSource b N T).card:ℝ)*physicalDensitySum Q rho+
      realPhysicalDistributionError b N T Q rho+(Nat.ceil (cutoff N):ℝ)+(T+1) :=
  RealB_cast_le_same_rho_main_add_distribution_of_gate N _ _ _ hb hb1 hT hgate
    (fun _ hm _ => compiled_modulus_dvd N _ hwz hm)
    (upper_majorant B r n e q a omega N tau L hL hwL hwz hz)

end
end ImbalancedChen.P4AOriginalFiniteFallbackCount
