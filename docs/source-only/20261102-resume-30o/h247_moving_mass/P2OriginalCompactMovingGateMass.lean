import ImbalancedChen.P2OriginalBankThetaMassLimits
import ImbalancedChen.AffinePrimeWallReserve
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite-net argument for a moving affine region.  In particular,
pointwise convergence is NOT asserted to imply uniform convergence.
The local estimate below pays every change of gate by an actual closed
prime-wall strip, and every change of kernel by the actual box mass.
The strip width and the finite cover are chosen before the target N.
-/
namespace ImbalancedChen.P2OriginalCompactMovingGateMass

noncomputable section
open MeasureTheory Filter Set
open scoped Classical BigOperators Topology

abbrev Coord (d : ℕ) := Fin d → ℝ
def closedCube (d : ℕ) (a b : ℝ) : Set (Coord d) :=
  Set.univ.pi (fun _ => Icc a b)

theorem box_mem_closedCube {d : ℕ} {a b : ℝ} {x : Coord d}
    (hx : x∈logPrimeBox (fun _ => a) (fun _ => b)) : x∈closedCube d a b := by
  intro i _
  exact ⟨(mem_logPrimeBox.mp hx i).1,(mem_logPrimeBox.mp hx i).2.le⟩

/-- If the strict selectors differ, an original fixed-center wall lies
in the CLOSED strip. Equality prime atoms therefore remain charged. -/
theorem changed_gate_in_strip {d r : ℕ}
    (A : Fin r → Coord d →L[ℝ] ℝ) (c e : Fin r → ℝ) (delta : ℝ)
    (hce : ∀j,|e j-c j|≤delta) {x : Coord d}
    (h : (x∈primeAffineGateRegion A e) ≠ (x∈primeAffineGateRegion A c)) :
    x∈primeAffineWallStrip A c delta := by
  by_cases he : x∈primeAffineGateRegion A e
  · have hc : x∉primeAffineGateRegion A c := fun hc => h (propext ⟨fun _ => hc,fun _ => he⟩)
    obtain ⟨j,hj⟩ : ∃j,c j≤A j x := by
      simpa only [primeAffineGateRegion,mem_setOf_eq,not_forall,not_lt] using hc
    have hdelta : 0≤delta := (abs_nonneg (e j-c j)).trans (hce j)
    refine ⟨j,abs_le.mpr ⟨?_,?_⟩⟩
    · have hd := (abs_le.mp (hce j)).2
      linarith
    · have hd := (abs_le.mp (hce j)).2
      linarith [he j]
  · have hc : x∈primeAffineGateRegion A c := by
      by_contra hc
      exact h (propext ⟨fun he' => (he he').elim,fun hc' => (hc hc').elim⟩)
    obtain ⟨j,hj⟩ : ∃j,e j≤A j x := by
      simpa only [primeAffineGateRegion,mem_setOf_eq,not_forall,not_lt] using he
    refine ⟨j,abs_le.mpr ⟨?_,?_⟩⟩
    · have hd := (abs_le.mp (hce j)).1
      linarith
    · have hd := (abs_le.mp (hce j)).2
      linarith [hc j]

/-- The pointwise sandwich is valid for signed continuous kernels. -/
theorem moving_gate_test_sandwich {d r : ℕ}
    (A : Fin r → Coord d →L[ℝ] ℝ) (c e : Fin r → ℝ)
    (f g : Coord d → ℝ) {eta B delta : ℝ}
    (heta : 0≤eta) (hB : 0≤B) (hce : ∀j,|e j-c j|≤delta)
    (x : Coord d) (hfg : |g x-f x|≤eta) (hf : |f x|≤B) :
    |(primeAffineGateRegion A e).indicator g x-
      (primeAffineGateRegion A c).indicator f x| ≤
      eta+B*(if x∈primeAffineWallStrip A c delta then 1 else 0) := by
  by_cases he : x∈primeAffineGateRegion A e <;>
    by_cases hc : x∈primeAffineGateRegion A c
  · simp only [indicator_of_mem he,indicator_of_mem hc]
    exact hfg.trans (le_add_of_nonneg_right (mul_nonneg hB (by split_ifs <;> norm_num)))
  · have hs := changed_gate_in_strip A c e delta hce
      (show (x∈primeAffineGateRegion A e)≠(x∈primeAffineGateRegion A c) from
        fun hh => hc (hh ▸ he))
    simp only [indicator_of_mem he,indicator_of_notMem hc,sub_zero,if_pos hs,mul_one]
    calc
      |g x| = |(g x-f x)+f x| := by congr 1; ring
      _ ≤ |g x-f x|+|f x| := abs_add _ _
      _ ≤ eta+B := add_le_add hfg hf
  · have hs := changed_gate_in_strip A c e delta hce
      (show (x∈primeAffineGateRegion A e)≠(x∈primeAffineGateRegion A c) from
        fun hh => he (hh.symm ▸ hc))
    simp only [indicator_of_notMem he,indicator_of_mem hc,zero_sub,abs_neg,if_pos hs,mul_one]
    linarith
  · simp only [indicator_of_notMem he,indicator_of_notMem hc,sub_self,abs_zero]
    exact add_nonneg heta (mul_nonneg hB (by split_ifs <;> norm_num))

/-- Exact finite arithmetic estimate, before any limit or net. -/
theorem moving_gate_sum_sandwich {d r N : ℕ} {a b eta B delta : ℝ}
    (hN : 1<N) (heta : 0≤eta) (hB : 0≤B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c e : Fin r → ℝ)
    (f g : Coord d → ℝ) (hce : ∀j,|e j-c j|≤delta)
    (hfg : ∀x∈closedCube d a b,|g x-f x|≤eta)
    (hf : ∀x∈closedCube d a b,|f x|≤B) :
    |actualPrimeBoxTestSum N (fun _ => a) (fun _ => b)
        ((primeAffineGateRegion A e).indicator g)-
      actualPrimeBoxTestSum N (fun _ => a) (fun _ => b)
        ((primeAffineGateRegion A c).indicator f)| ≤
      eta*actualPrimeBoxMass N (fun _ : Fin d => a) (fun _ => b)+
      B*actualPrimeAffineWallStripMass N (fun _ => a) (fun _ => b) A c delta := by
  unfold actualPrimeBoxTestSum actualPrimeBoxMass actualPrimeAffineWallStripMass
  rw [Finset.sum_filter,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hx := box_mem_closedCube ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  have hw := actualPrimeBoxWeight_nonneg hp
  have hh := moving_gate_test_sandwich A c e f g heta hB hce
    (actualPrimeTupleLog N p) (hfg _ hx) (hf _ hx)
  rw [← mul_sub,abs_mul,abs_of_nonneg hw]
  have hm := mul_le_mul_of_nonneg_left hh hw
  split_ifs at * <;> nlinarith only [hm]

/-- Compactness of the kernel's actual product domain DERIVES its
uniform oscillation estimate. No equicontinuity assumption occurs. -/
theorem exists_kernel_oscillation {d : ℕ} {K : Set ℝ} (hK : IsCompact K)
    (a b : ℝ) (F : ℝ × Coord d → ℝ) (hF : Continuous F)
    {eta : ℝ} (heta : 0<eta) :
    ∃ delta : ℝ,0<delta ∧ ∀s∈K,∀L∈K,dist L s<delta →
      ∀x∈closedCube d a b,|F (L,x)-F (s,x)|≤eta := by
  have hc : IsCompact (K ×ˢ closedCube d a b) :=
    hK.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  obtain ⟨delta,hd,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hF.continuousOn) eta heta
  refine ⟨delta,hd,?_⟩
  intro s hs L hL hdist x hx
  have hh := hmod (L,x) ⟨hL,hx⟩ (s,x) ⟨hs,hx⟩
    (by simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg : 0≤dist L s)] using hdist)
  exact (by simpa only [Real.dist_eq] using hh.le)

def gateSum {d r : ℕ} (N : ℕ) (a b : ℝ)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : ℝ → Fin r → ℝ)
    (F : ℝ × Coord d → ℝ) (L : ℝ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ => a) (fun _ => b)
    ((primeAffineGateRegion A (c L)).indicator (fun x => F (L,x)))

def gateIntegral {d r : ℕ} (a b : ℝ)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : ℝ → Fin r → ℝ)
    (F : ℝ × Coord d → ℝ) (L : ℝ) : ℝ :=
  ∫x in logPrimeBox (fun _ => a) (fun _ => b) ∩ primeAffineGateRegion A (c L),
    F (L,x)*(∏i,1/x i)

theorem gateSum_fixed_limit {d r : ℕ} {a b : ℝ} (ha : 0<a) (hab : a<b)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀j,A j≠0)
    (c : ℝ → Fin r → ℝ) (F : ℝ × Coord d → ℝ) (hF : Continuous F) (L : ℝ) :
    Tendsto (fun N : ℕ => gateSum N a b A c F L) atTop
      (𝓝 (gateIntegral a b A c F L)) :=
  tendsto_actualPrimeBoxTestSum_cube_affineGates ha hab A (c L) hA
    (fun x => F (L,x)) (hF.comp (continuous_const.prodMk continuous_id)).continuousOn

/-- Local arithmetic continuity is proved by paying a fixed-center
closed strip, uniformly in ALL nearby parameters and later targets. -/
theorem local_gateSum_oscillation {d r : ℕ} {K : Set ℝ} (hK : IsCompact K)
    {a b B : ℝ} (ha : 0<a) (hab : a<b) (hB : 0≤B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀j,A j≠0)
    (c : ℝ → Fin r → ℝ) (hc : ∀j,Continuous (fun L => c L j))
    (F : ℝ × Coord d → ℝ) (hF : Continuous F)
    (hbound : ∀L∈K,∀x∈closedCube d a b,|F (L,x)|≤B)
    {epsilon : ℝ} (hepsilon : 0<epsilon) (s : ℝ) (hs : s∈K) :
    ∃ delta : ℝ,0<delta ∧ ∃T : ℕ,∀N : ℕ,T≤N →
      ∀L∈K,dist L s<delta → |gateSum N a b A c F L-gateSum N a b A c F s|<epsilon := by
  let M : ℝ := (∏_i : Fin d,Real.log (b/a))+1
  have hM : 0<M := by
    have hprod : 0≤∏_i : Fin d,Real.log (b/a) :=
      Finset.prod_nonneg (fun _ _ => Real.log_nonneg ((one_le_div ha).mpr hab.le))
    dsimp [M]; linarith
  let eta := epsilon/(4*(M+1))
  let zeta := epsilon/(4*(B+1))
  have heta : 0<eta := by dsimp [eta]; positivity
  have hzeta : 0<zeta := by dsimp [zeta]; positivity
  have hebudget : eta*(M+1)=epsilon/4 := by
    dsimp [eta]
    field_simp [show M+1≠0 by linarith] <;> ring
  have hzbudget : zeta*(B+1)=epsilon/4 := by
    dsimp [zeta]
    field_simp [show B+1≠0 by linarith] <;> ring
  obtain ⟨width,hwidth,Tw,hTw,hstrip⟩ :=
    exists_actualPrimeAffineWallStrip_mass_lt ha hab A (c s) hA zeta hzeta
  obtain ⟨df,hdf,hfo⟩ := exists_kernel_oscillation hK a b F hF heta
  have hce : ∀ᶠL : ℝ in 𝓝 s,∀j,|c L j-c s j|<width := by
    apply eventually_all.mpr
    intro j
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp (hc j).continuousAt width hwidth
  obtain ⟨dc,hdc,hco⟩ := Metric.mem_nhds_iff.mp hce
  have hmass : ∀ᶠN : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin d => a) (fun _ => b)<M :=
    (tendsto_actualPrimeBoxMass _ _ (fun _ => ha) (fun _ => hab)).eventually
      (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨Tm,hTm⟩ := eventually_atTop.mp hmass
  refine ⟨min df dc,lt_min hdf hdc,max 2 (max Tw Tm),?_⟩
  intro N hN L hL hd
  have hN1 : 1<N := by omega
  have hS := hstrip N (by omega)
  have hM' := hTm N (by omega)
  have hf' := hfo s hs L hL (hd.trans_le (min_le_left _ _))
  have hc' : ∀j,|c L j-c s j|≤width :=
    fun j => (hco (show L∈Metric.ball s dc from hd.trans_le (min_le_right _ _)) j).le
  have hh := moving_gate_sum_sandwich hN1 heta.le hB A (c s) (c L)
    (fun x => F (s,x)) (fun x => F (L,x)) hc' hf' (hbound s hs)
  change |gateSum N a b A c F L-gateSum N a b A c F s|≤_ at hh
  have hm := mul_le_mul_of_nonneg_left hM'.le heta.le
  have hw := mul_le_mul_of_nonneg_left hS.le hB
  nlinarith only [hh,hm,hw,hebudget,hzbudget,heta,hzeta,hM,hB,hepsilon]

/-- Finite net/sandwich theorem. The cover and its finitely many target
thresholds precede every L in the compact set. -/
theorem compact_uniform_affine_gates {d r : ℕ} {K : Set ℝ} (hK : IsCompact K)
    {a b B : ℝ} (ha : 0<a) (hab : a<b) (hB : 0≤B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀j,A j≠0)
    (c : ℝ → Fin r → ℝ) (hc : ∀j,Continuous (fun L => c L j))
    (F : ℝ × Coord d → ℝ) (hF : Continuous F)
    (hbound : ∀L∈K,∀x∈closedCube d a b,|F (L,x)|≤B)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈K,
      |gateSum N a b A c F L-gateIntegral a b A c F L|<epsilon := by
  have hlocal (s : K) := local_gateSum_oscillation hK ha hab hB A hA c hc F hF
    hbound (by positivity : 0<epsilon/4) s.1 s.2
  choose delta hd T hT using hlocal
  obtain ⟨net,hnet⟩ := hK.elim_finite_subcover (fun s : K => Metric.ball s.1 (delta s))
    (fun _ => Metric.isOpen_ball) (by
      intro L hL
      exact mem_iUnion.mpr ⟨⟨L,hL⟩,Metric.mem_ball_self (hd ⟨L,hL⟩)⟩)
  have hcenters : ∀ᶠN : ℕ in atTop,∀s∈net,
      T s≤N ∧ |gateSum N a b A c F s.1-gateIntegral a b A c F s.1|<epsilon/4 := by
    apply (Finset.eventually_all net).mpr
    intro s hs
    exact (eventually_ge_atTop (T s)).and (by
      simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
        (gateSum_fixed_limit ha hab A hA c F hF s.1) (epsilon/4) (by positivity))
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp hcenters
  refine ⟨T0,?_⟩
  intro N hN L hL
  obtain ⟨s,hs,hsL⟩ := mem_iUnion₂.mp (hnet hL)
  have hnear := hT s N (hT0 N hN s hs).1 L hL hsL
  have hlim : |gateIntegral a b A c F L-gateIntegral a b A c F s.1|≤epsilon/4 := by
    apply le_of_tendsto (((gateSum_fixed_limit ha hab A hA c F hF L).sub
      (gateSum_fixed_limit ha hab A hA c F hF s.1)).abs)
    filter_upwards [eventually_ge_atTop (T s)] with n hn
    exact (hT s n hn L hL hsL).le
  have hcenter := (hT0 N hN s hs).2
  have htri := (abs_sub_le (gateSum N a b A c F L)
    (gateSum N a b A c F s.1) (gateIntegral a b A c F L)).trans
      (add_le_add le_rfl (abs_sub_le _ (gateIntegral a b A c F s.1) _))
  rw [abs_sub_comm (gateIntegral a b A c F s.1)] at htri
  linarith

end
end ImbalancedChen.P2OriginalCompactMovingGateMass
