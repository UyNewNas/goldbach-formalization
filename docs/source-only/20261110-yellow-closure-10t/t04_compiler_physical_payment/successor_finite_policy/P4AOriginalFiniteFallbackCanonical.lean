import ImbalancedChen.P4AFallbackCanonicalBanks
import ImbalancedChen.P4AOriginalFiniteFallbackSchedule
import ImbalancedChen.P4AOriginalFiniteFallbackFirstInterval

namespace ImbalancedChen.P4AOriginalFiniteFallbackCanonical
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P4AOriginalFiniteFallbackPolicy (point choose secondLevel F)
open P4AFallbackCanonicalBanks
open P4AOriginalFiniteFallbackRange (Bounded)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (SecondRegion ThirdRegion secondMask thirdMask)
open VariableEnvelope
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalFull87HistoryCore (width)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P5OriginalCommonPositivePresieve (normalize)

theorem selected_second {m : ℕ} {t : Point 2} {c : ℚ} (h : read m (bank m).second t=some c) :
    SecondRegion (t 0) (t 1) ∧ 3*t 0<v (t 0) ∧ v (t 0)<c ∧ (c:ℝ)<299/500 ∧
    (1/2:ℝ)<c ∧ (∀ i,prefixSquareExpr t i<c) ∧ (∀ i∉secondMask,selectedSquareExpr secondMask t i<c) ∧
      (c:ℝ)<v (t 1) := by
  obtain ⟨j,hj,hr⟩ := read_some_iff.mp h
  obtain ⟨hg,rfl⟩ := (second_some_iff m j c).mp hr
  exact good2_sound m j hg t (meshCell_subset_closedBox m j hj)

theorem selected_third {m : ℕ} {t : Point 3} {c : ℚ} (h : read m (bank m).third t=some c) :
    ThirdRegion (t 0) (t 1) (t 2) ∧ 3*t 0<v (t 0) ∧ t 0+t 1+3*t 2<v (t 0) ∧
    v (t 0)<c ∧ (c:ℝ)<299/500 ∧ (1/2:ℝ)<c ∧ (∀ i,prefixSquareExpr t i<c) ∧
    (∀ i∉thirdMask,selectedSquareExpr thirdMask t i<c) ∧ (c:ℝ)<v (t 1+t 2) := by
  obtain ⟨j,hj,hr⟩ := read_some_iff.mp h
  obtain ⟨hg,rfl⟩ := (third_some_iff m j c).mp hr
  exact good3_sound m j hg t (meshCell_subset_closedBox m j hj)

theorem bounded (m : ℕ) : Bounded (bank m) :=
  ⟨fun t c h => (selected_second h).2.2.2.1.le, fun t c h => (selected_third h).2.2.2.2.1.le⟩

theorem exclusive {m : ℕ} {t : Point 3} {c : ℚ} (h : read m (bank m).third t=some c) :
    read m (bank m).second (fun i => t (i.castLE (by decide : 2≤3)))=none := by
  cases hs : read m (bank m).second (fun i => t (i.castLE (by decide : 2≤3))) with
  | none => rfl
  | some c' =>
    obtain ⟨hR,_,_⟩ := selected_second hs
    obtain ⟨_,_,_,_,_,_,_,_,_,hupper⟩ := (selected_third h).1
    have hlo : (3/16:ℝ)≤t 1 := by
      change SecondRegion (t 0) (t 1) at hR
      obtain ⟨hx,hρ,hy,_⟩ := hR
      rw [v_eq_C hx.le] at hy
      dsimp [C,P5OriginalAboveMuThirdLowerPhysicalCoefficient.rho] at *
      linarith
    exact (not_lt_of_ge hlo hupper).elim

theorem second_floor (m : ℕ) (d : OriginalData) (he : (d.e:ℝ)≤1/2048) (w N : ℝ) (p : List ℕ) :
    P4AOriginalFiniteFallbackSmallThird.floorLevel≤secondLevel (bank m) d w N p := by
  unfold secondLevel
  cases h : read m (bank m).second (point N 2 p) with
  | none => exact P4AOriginalFiniteFallbackFirstInterval.lower_floor he _ _ _ _
  | some c =>
    have H := (selected_second h).2.2.2.2.1
    change (1/2:ℝ)-1/1024≤(c:ℝ)
    linarith

/-- The two finite geometric tables have no expense or support premise. -/
theorem paid (m r n : ℕ) (e : ℚ) (he : 0≤e) (q : ℕ) (a : ℝ) (ha : 0<a)
    (nu v u_c epsilonMax : ℝ) (hnu : 0<nu) (hv : 0<v) (hcut : nu*v=19/96)
    (hu : 0<u_c) (hm : 0<epsilonMax) :
    ∃ eps : ℝ, 0<eps ∧ eps<1/8 ∧ eps<epsilonMax ∧ eps^2<v ∧ nu*eps^2<a ∧ nu*eps<1/1000 ∧
      ∃ k : ℕ, ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
      let omega := nu*eps^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*eps)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (width r) n (data e q a) omega N
      let A := P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
      ((N:ℝ)/Real.log (N:ℝ))*A<u_c*singularNormalization N ∧
      physicalDensitySum Q rho<p4aReserveRawDensity f N N 0 z-p4aActualPresieveCorrection f N N w z+
        u_c*(singularSeries N/Real.log (N:ℝ)) ∧
      (∀ m : ℕ,rho m≠0 → (m:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ, 0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*physicalDensitySum Q rho+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) :=
  P4AOriginalFiniteFallbackSameCoefficient.joined (bank m) (bounded m) r n e he q a ha nu v u_c epsilonMax
    hnu hv hcut hu hm

theorem common_schedule (m : ℕ) (eta : ℝ) (htol : 0<eta) :
    ∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a : ℝ,0<a → ∀ r n : ℕ,∀ nu v u_c epsilonMax : ℝ,0<nu → 0<v → nu*v=19/96 → 0<u_c → 0<epsilonMax →
    ∃ eps : ℝ,0<eps ∧ eps<1/8 ∧ eps<epsilonMax ∧ eps^2<v ∧ nu*eps^2<a ∧ nu*eps<1/1000 ∧
    ∃ k N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*eps^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*eps)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (P4AOriginalFull87HistoryCore.width r) n (data e q a) omega N
      normalize N (rawRoot (fresh (data e q a) omega N) N) < (∑ i,currentUpperEighteenPositive i)+eta ∧
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
          <u_c*singularNormalization N ∧
      physicalDensitySum Q rho<p4aReserveRawDensity f N N 0 z-p4aActualPresieveCorrection f N N w z+
        u_c*(singularSeries N/Real.log (N:ℝ)) ∧
      (∀ m : ℕ,rho m≠0 → (m:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*physicalDensitySum Q rho+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) :=
  P4AOriginalFiniteFallbackSchedule.common_schedule (bank m) (bounded m) eta htol

end
end ImbalancedChen.P4AOriginalFiniteFallbackCanonical
