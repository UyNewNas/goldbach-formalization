import ImbalancedChen.P4AOriginalFiniteFallbackPhysicalRange
import ImbalancedChen.P4AOriginalFiniteFallbackPhysicalSelected

/-! SOURCE_ONLY / UNCOMPILED. Necessary quantifier strengthening of the
original PPSchedule: Payment.paid chooses beta ONCE, then aligned_small
chooses ONE common k below every original bound and fineTolerance beta.
No two independent existential beta/k choices are combined. -/
namespace ImbalancedChen.P4AOriginalFiniteFallbackFinePPSchedule
noncomputable section
open scoped Classical BigOperators
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth aligned_small)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackRange (Bounded)
open P4AOriginalFiniteFallbackPolicy (F rho)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalNewFifthUnion (data)

/-- The physical parameter is below the historical cutoff a. The same
unlabelled rectangular rho has the H_N reserve, density comparison,
strict support and integer RealB majorant on a single aligned mesh. -/
theorem joined (B : Bank) (hB : Bounded B) (r n : ℕ) (e : ℚ) (he : 0≤e) (q : ℕ) (a : ℝ) (ha : 0<a)
    (budget : ℝ) (hb : 0<budget) (nu v u_c epsilonMax : ℝ) (hnu : 0<nu) (hv : 0<v) (hcut : nu*v=19/96)
    (hu : 0<u_c) (hm : 0<epsilonMax)
    (fineTolerance : ℝ→ℝ) (hFine : ∀ beta : ℝ,0<beta → 0<fineTolerance beta) :
    ∃ eps : ℝ, 0<eps ∧ eps<1/8 ∧ eps<epsilonMax ∧ eps^2<v ∧ nu*eps^2<a ∧ nu*eps<1/1000 ∧ nu*eps<budget/32 ∧
      ∃ k : ℕ, alignedWidth (jointIndex B (data e q a).m) k≤fineTolerance eps ∧
        alignedWidth (jointIndex B (data e q a).m) k*((P4AHeldTaggedCompilerSupport.J0 (nu*eps^2):ℝ)+1)≤budget ∧ ∃ N0 : ℕ, 2≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
      let omega := nu*eps^2
      let tau := alignedWidth (jointIndex B (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*eps)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho B r n e q a omega N tau L
      let f := F B (width r) n (data e q a) omega N
      let A := P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
      ((N:ℝ)/Real.log (N:ℝ))*A<u_c*singularNormalization N ∧
      physicalDensitySum Q rho<p4aReserveRawDensity f N N 0 z-p4aActualPresieveCorrection f N N w z+
        u_c*(singularSeries N/Real.log (N:ℝ)) ∧
      (∀ m : ℕ,rho m≠0 → (m:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ, 0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*physicalDensitySum Q rho+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) := by
  let d := data e q a
  obtain ⟨eps,hp,h8,hm',hsq,hell,t0,ht0,N0,hN0,hpay⟩ :=
    P4AOriginalFiniteFallbackPayment.paid B hB (width r) (width_pos _) n d he nu v u_c (min epsilonMax (min (a/nu) (budget/(32*nu))))
      hnu hv (by rw [hcut]; norm_num) hu (lt_min hm (lt_min (div_pos ha hnu) (div_pos hb (by positivity))))
  let omega := nu*eps^2
  have hw : 0<omega := mul_pos hnu (sq_pos_of_pos hp)
  have he1 : eps<1 := by linarith
  have hsq' : eps^2<eps := by nlinarith
  have hwE : omega<nu*eps := mul_lt_mul_of_pos_left hsq' hnu
  have hwa : omega<a := by
    have HH := (lt_div_iff₀ hnu).mp (hm'.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    dsimp only [omega] at hwE ⊢
    linarith
  obtain ⟨t1,ht1,hRange⟩ := P4AOriginalFiniteFallbackPhysicalRange.data_physical_range B hB (width r) (width_pos _)
    n d he omega (nu*eps) hw hell
  have hell' : nu*eps<budget/32 := by
    have H := (lt_div_iff₀ (by positivity : 0<32*nu)).mp
      (hm'.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  let R := (P4AHeldTaggedCompilerSupport.J0 omega:ℝ)+1
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨k,ht,hk⟩ := aligned_small (jointIndex B d.m) (lt_min (lt_min ht0 ht1) (lt_min (div_pos hb hR) (hFine eps hp)))
  have ht' := hk.trans (min_le_left _ _)
  have hbudget := (le_div_iff₀ hR).mp
    ((hk.trans (min_le_right _ _)).trans (min_le_left _ _))
  have hfine := (hk.trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨eps,hp,h8,hm'.trans_le (min_le_left _ _),hsq,hwa,hell,hell',k,hfine,hbudget,N0,hN0,?_⟩
  intro N hN hEven
  have h2 := hN0.trans hN
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  let tau := alignedWidth (jointIndex B d.m) k
  have hz : (N:ℝ)^(nu*v)=cutoff N := by
    simp only [hcut,P4AOriginalFull87RawChronology.cutoff]
  have hcap : (N:ℝ)^(nu*v)≤(N:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn.le
      (by rw [hcut]; norm_num : nu*v≤1)
  obtain ⟨_,hscale,hdens⟩ := hpay N hN hEven N hcap tau ht (ht'.trans (min_le_left _ _))
  rw [hz] at hscale hdens
  have hq := (hRange tau ht (ht'.trans (min_le_right _ _))).2 N N h2 (cutoff N) (fun _ => [])
  have hL := Real.one_lt_rpow hn (mul_pos hnu hp)
  have hwL := Real.rpow_le_rpow_of_exponent_le hn.le hwE.le
  have hwz : (N:ℝ)^omega≤cutoff N := hz ▸ Real.rpow_le_rpow_of_exponent_le hn.le
    (mul_le_mul_of_nonneg_left hsq.le hnu.le)
  exact ⟨hscale,hdens,hq,fun b T hb hb1 hT hgate =>
    P4AOriginalFiniteFallbackCount.count B r n e q a omega N tau _ hL hwL hwz (hz ▸ hcap) hb hb1 hT hgate⟩

end
end ImbalancedChen.P4AOriginalFiniteFallbackFinePPSchedule
