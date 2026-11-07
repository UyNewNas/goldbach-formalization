import ImbalancedChen.P2OriginalCompactMovingGateMass
import ImbalancedChen.P2OriginalAffineProfilePassage

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing one-real-parameter finite-net proof is extended to a compact
metric parameter space. The actual prime-wall strip estimate is reused.
A second finite cover pays the arithmetic boundary of every affine
sandwich, including singleton/knot fibres, uniformly before the parameter.
No uniform-convergence or boundary-prime-mass estimate is an input.
-/
namespace ImbalancedChen.Part5OriginalCompactParameterSandwich

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalCompactMovingGateMass P2OriginalAffineProfilePassage

variable {P : Type*} [MetricSpace P]

def testSum {d : ℕ} (N : ℕ) (a b : ℝ) (D : Set (Coord d))
    (f : Coord d → ℝ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ => a) (fun _ => b) (D.indicator f)

def testIntegral {d : ℕ} (a b : ℝ) (D : Set (Coord d))
    (f : Coord d → ℝ) : ℝ :=
  ∫ x in logPrimeBox (fun _ => a) (fun _ => b) ∩ D, f x * ∏ i, 1 / x i

theorem kernel_oscillation {d : ℕ} {K : Set P} (hK : IsCompact K)
    (a b : ℝ) (F : P × Coord d → ℝ) (hF : Continuous F)
    {eta : ℝ} (he : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ K, ∀ q ∈ K, dist q s < delta →
      ∀ x ∈ closedCube d a b, |F (q,x) - F (s,x)| ≤ eta := by
  have hc : IsCompact (K ×ˢ closedCube d a b) :=
    hK.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  obtain ⟨delta, hd, hm⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hF.continuousOn) eta he
  refine ⟨delta, hd, ?_⟩
  intro s hs q hq hdist x hx
  have h := hm (q,x) ⟨hq,hx⟩ (s,x) ⟨hs,hx⟩
    (by simpa only [Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg : 0 ≤ dist q s)] using hdist)
  simpa only [Real.dist_eq] using h.le

theorem fixed_limit {d r : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (F : P × Coord d → ℝ) (hF : Continuous F) (q : P) :
    Tendsto (fun N : ℕ => testSum N a b (primeAffineGateRegion A (c q))
      (fun x => F (q,x))) atTop
      (𝓝 (testIntegral a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)))) :=
  tendsto_actualPrimeBoxTestSum_cube_affineGates ha hab A (c q) hA
    (fun x => F (q,x)) (hF.comp (continuous_const.prodMk continuous_id)).continuousOn

theorem local_oscillation {d r : ℕ} {K : Set P} (hK : IsCompact K)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (hc : ∀ j, Continuous (fun q => c q j))
    (F : P × Coord d → ℝ) (hF : Continuous F)
    (hb : ∀ q ∈ K, ∀ x ∈ closedCube d a b, |F (q,x)| ≤ B)
    {epsilon : ℝ} (he : 0 < epsilon) (s : P) (hs : s ∈ K) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ q ∈ K, dist q s < delta →
      |testSum N a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)) -
        testSum N a b (primeAffineGateRegion A (c s)) (fun x => F (s,x))| < epsilon := by
  let M : ℝ := (∏ _i : Fin d, Real.log (b/a)) + 1
  have hM : 0 < M := by
    have hh : 0 ≤ ∏ _i : Fin d, Real.log (b/a) :=
      Finset.prod_nonneg (fun _ _ => Real.log_nonneg ((one_le_div ha).mpr hab.le))
    dsimp [M]; linarith
  let eta := epsilon / (4*(M+1))
  let zeta := epsilon / (4*(B+1))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hzeta : 0 < zeta := by dsimp [zeta]; positivity
  have heb : eta*(M+1) = epsilon/4 := by
    dsimp [eta]; field_simp [show M+1 ≠ 0 by linarith] <;> ring
  have hzb : zeta*(B+1) = epsilon/4 := by
    dsimp [zeta]; field_simp [show B+1 ≠ 0 by linarith] <;> ring
  obtain ⟨width, hw, Tw, hTw, hstrip⟩ :=
    exists_actualPrimeAffineWallStrip_mass_lt ha hab A (c s) hA zeta hzeta
  obtain ⟨df, hdf, hfo⟩ := kernel_oscillation hK a b F hF heta
  have hce : ∀ᶠ q : P in 𝓝 s, ∀ j, |c q j - c s j| < width := by
    apply eventually_all.mpr
    intro j
    simpa only [Real.dist_eq] using
      Metric.tendsto_nhds.mp (hc j).continuousAt width hw
  obtain ⟨dc, hdc, hco⟩ := Metric.mem_nhds_iff.mp hce
  have hm : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin d => a) (fun _ => b) < M :=
    (tendsto_actualPrimeBoxMass _ _ (fun _ => ha) (fun _ => hab)).eventually
      (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨Tm, hTm⟩ := eventually_atTop.mp hm
  refine ⟨min df dc, lt_min hdf hdc, max 2 (max Tw Tm), ?_⟩
  intro N hN q hq hdist
  have hN1 : 1 < N := by omega
  have hf' := hfo s hs q hq (hdist.trans_le (min_le_left _ _))
  have hc' : ∀ j, |c q j-c s j| ≤ width := fun j =>
    (hco (show q ∈ Metric.ball s dc from
      hdist.trans_le (min_le_right _ _)) j).le
  have hh := moving_gate_sum_sandwich hN1 heta.le hB A (c s) (c q)
    (fun x => F (s,x)) (fun x => F (q,x)) hc' hf' (hb s hs)
  have hm' := mul_le_mul_of_nonneg_left (hTm N (by omega)).le heta.le
  have hw' := mul_le_mul_of_nonneg_left (hstrip N (by omega)).le hB
  change |testSum N a b _ _ - testSum N a b _ _| ≤ _ at hh
  nlinarith only [hh, hm', hw', heb, hzb, heta, hzeta, hM, hB, he]

/-- One threshold before every point of the compact parameter set. -/
theorem compact_uniform_open {d r : ℕ} {K : Set P} (hK : IsCompact K)
    {a b B epsilon : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (hc : ∀ j, Continuous (fun q => c q j))
    (F : P × Coord d → ℝ) (hF : Continuous F)
    (hb : ∀ q ∈ K, ∀ x ∈ closedCube d a b, |F (q,x)| ≤ B)
    (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ q ∈ K,
      |testSum N a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)) -
        testIntegral a b (primeAffineGateRegion A (c q)) (fun x => F (q,x))| < epsilon := by
  have hl (s : K) := local_oscillation hK ha hab hB A hA c hc F hF hb
    (by positivity : 0 < epsilon/4) s.1 s.2
  choose delta hd T hT using hl
  obtain ⟨net, hn⟩ := hK.elim_finite_subcover
    (fun s : K => Metric.ball s.1 (delta s)) (fun _ => Metric.isOpen_ball) (by
      intro q hq
      exact mem_iUnion.mpr ⟨⟨q,hq⟩, Metric.mem_ball_self (hd ⟨q,hq⟩)⟩)
  have hcents : ∀ᶠ N : ℕ in atTop, ∀ s ∈ net,
      T s ≤ N ∧
      |testSum N a b (primeAffineGateRegion A (c s.1)) (fun x => F (s.1,x)) -
        testIntegral a b (primeAffineGateRegion A (c s.1)) (fun x => F (s.1,x))| < epsilon/4 := by
    apply (Finset.eventually_all net).mpr
    intro s hs
    exact (eventually_ge_atTop (T s)).and (by
      simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
        (fixed_limit ha hab A hA c F hF s.1) (epsilon/4) (by positivity))
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hcents
  refine ⟨T0, ?_⟩
  intro N hN q hq
  obtain ⟨s, hs, hsq⟩ := mem_iUnion₂.mp (hn hq)
  have hn' := hT s N (hT0 N hN s hs).1 q hq hsq
  have hi : |testIntegral a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)) -
      testIntegral a b (primeAffineGateRegion A (c s.1)) (fun x => F (s.1,x))| ≤ epsilon/4 := by
    apply le_of_tendsto (((fixed_limit ha hab A hA c F hF q).sub
      (fixed_limit ha hab A hA c F hF s.1)).abs)
    filter_upwards [eventually_ge_atTop (T s)] with n hn
    exact (hT s n hn q hq hsq).le
  have hc' := (hT0 N hN s hs).2
  have ht := (abs_sub_le
    (testSum N a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)))
    (testSum N a b (primeAffineGateRegion A (c s.1)) (fun x => F (s.1,x)))
    (testIntegral a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)))).trans
      (add_le_add le_rfl (abs_sub_le _
        (testIntegral a b (primeAffineGateRegion A (c s.1)) (fun x => F (s.1,x))) _))
  rw [abs_sub_comm (testIntegral a b (primeAffineGateRegion A (c s.1))
    (fun x => F (s.1,x)))] at ht
  linarith

/-- A closed/knot atom may have no strict interior. Its finite arithmetic
mass is paid by a fixed-center CLOSED prime strip, not discarded. -/
theorem sandwich_indicator_strip {d r : ℕ}
    (A : Fin r → Coord d →L[ℝ] ℝ) (c e : Fin r → ℝ)
    {D : Set (Coord d)} (hD : AffineSandwich A e D)
    {width B : ℝ} (hB : 0 ≤ B) (hce : ∀ j, |e j-c j| ≤ width)
    (f : Coord d → ℝ) (x : Coord d) (hf : |f x| ≤ B) :
    |D.indicator f x - (primeAffineGateRegion A e).indicator f x| ≤
      B*(if x ∈ primeAffineWallStrip A c width then 1 else 0) := by
  by_cases ho : x ∈ primeAffineGateRegion A e
  · rw [indicator_of_mem ho, indicator_of_mem (hD.1 ho), sub_self, abs_zero]
    exact mul_nonneg hB (by split_ifs <;> norm_num)
  · by_cases hd : x ∈ D
    · obtain ⟨j,hj⟩ := sandwich_boundary A e hD hd ho
      have hw : x ∈ primeAffineWallStrip A c width := ⟨j, by simpa only [hj] using hce j⟩
      simpa only [indicator_of_mem hd, indicator_of_notMem ho, sub_zero, if_pos hw,
        mul_one] using hf
    · simp only [indicator_of_notMem hd, indicator_of_notMem ho, sub_self, abs_zero]
      exact mul_nonneg hB (by split_ifs <;> norm_num)

theorem boundary_sum_le {d r N : ℕ} {a b B width : ℝ}
    (hN : 1 < N) (hB : 0 ≤ B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c e : Fin r → ℝ)
    {D : Set (Coord d)} (hD : AffineSandwich A e D)
    (hce : ∀ j, |e j-c j| ≤ width) (f : Coord d → ℝ)
    (hf : ∀ x ∈ closedCube d a b, |f x| ≤ B) :
    |testSum N a b D f - testSum N a b (primeAffineGateRegion A e) f| ≤
      B*actualPrimeAffineWallStripMass N (fun _ => a) (fun _ => b) A c width := by
  unfold testSum actualPrimeBoxTestSum actualPrimeAffineWallStripMass
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hx := box_mem_closedCube ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  have hw := actualPrimeBoxWeight_nonneg hp
  have hh := mul_le_mul_of_nonneg_left
    (sandwich_indicator_strip A c e hD hB hce f _ (hf _ hx)) hw
  rw [← mul_sub, abs_mul, abs_of_nonneg hw]
  split_ifs at * <;> nlinarith only [hh]

theorem compact_uniform_boundary {d r : ℕ} {K : Set P} (hK : IsCompact K)
    {a b B epsilon : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (hc : ∀ j, Continuous (fun q => c q j))
    (D : P → Set (Coord d)) (hD : ∀ q ∈ K, AffineSandwich A (c q) (D q))
    (F : P × Coord d → ℝ)
    (hb : ∀ q ∈ K, ∀ x ∈ closedCube d a b, |F (q,x)| ≤ B)
    (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ q ∈ K,
      |testSum N a b (D q) (fun x => F (q,x)) -
        testSum N a b (primeAffineGateRegion A (c q)) (fun x => F (q,x))| < epsilon := by
  let eta := epsilon/(B+1)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heb : B*eta < epsilon := by
    have heq : eta*(B+1) = epsilon := by
      dsimp [eta]; field_simp [show B+1 ≠ 0 by linarith]
    nlinarith
  have hl (s : K) : ∃ delta : ℝ, 0 < delta ∧ ∃ T : ℕ,
      ∀ N : ℕ, T ≤ N → ∀ q ∈ K, dist q s.1 < delta →
      |testSum N a b (D q) (fun x => F (q,x)) -
        testSum N a b (primeAffineGateRegion A (c q)) (fun x => F (q,x))| < epsilon := by
    obtain ⟨width, hw, Tw, hTw, hs⟩ :=
      exists_actualPrimeAffineWallStrip_mass_lt ha hab A (c s.1) hA eta heta
    have hce : ∀ᶠ q : P in 𝓝 s.1, ∀ j, |c q j-c s.1 j| < width := by
      apply eventually_all.mpr
      intro j
      simpa only [Real.dist_eq] using
        Metric.tendsto_nhds.mp (hc j).continuousAt width hw
    obtain ⟨delta, hd, hdc⟩ := Metric.mem_nhds_iff.mp hce
    refine ⟨delta, hd, max 2 Tw, ?_⟩
    intro N hN q hq hdist
    have hh := boundary_sum_le (by omega : 1 < N) hB A (c s.1) (c q)
      (hD q hq) (fun j => (hdc hdist j).le) (fun x => F (q,x)) (hb q hq)
    exact hh.trans_lt ((mul_le_mul_of_nonneg_left (hs N (by omega)).le hB).trans_lt heb)
  choose delta hd T hT using hl
  obtain ⟨net, hn⟩ := hK.elim_finite_subcover
    (fun s : K => Metric.ball s.1 (delta s)) (fun _ => Metric.isOpen_ball) (by
      intro q hq
      exact mem_iUnion.mpr ⟨⟨q,hq⟩,Metric.mem_ball_self (hd ⟨q,hq⟩)⟩)
  refine ⟨net.sup T, ?_⟩
  intro N hN q hq
  obtain ⟨s, hs, hsq⟩ := mem_iUnion₂.mp (hn hq)
  exact hT s N ((Finset.le_sup hs).trans hN) q hq hsq

/-- Uniform arithmetic limit for all admitted open/closed boundary
choices. Properness is required only for the actual fixed affine rows. -/
theorem compact_uniform_sandwich {d r : ℕ} {K : Set P} (hK : IsCompact K)
    {a b B epsilon : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (hc : ∀ j, Continuous (fun q => c q j))
    (D : P → Set (Coord d)) (hD : ∀ q ∈ K, AffineSandwich A (c q) (D q))
    (F : P × Coord d → ℝ) (hF : Continuous F)
    (hb : ∀ q ∈ K, ∀ x ∈ closedCube d a b, |F (q,x)| ≤ B)
    (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ q ∈ K,
      |testSum N a b (D q) (fun x => F (q,x)) -
        testIntegral a b (D q) (fun x => F (q,x))| < epsilon := by
  obtain ⟨To, ho⟩ := compact_uniform_open hK ha hab hB A hA c hc F hF hb
    (by positivity : 0 < epsilon/2)
  obtain ⟨Tb, hbd⟩ := compact_uniform_boundary hK ha hab hB A hA c hc D hD F hb
    (by positivity : 0 < epsilon/2)
  refine ⟨max To Tb, ?_⟩
  intro N hN q hq
  have heq : testIntegral a b (D q) (fun x => F (q,x)) =
      testIntegral a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)) := by
    apply setIntegral_congr_set
    filter_upwards [sandwich_ae A (c q) hA (hD q hq)] with x hx
    change (_ ∧ x ∈ D q) ↔ (_ ∧ x ∈ primeAffineGateRegion A (c q))
    exact and_congr Iff.rfl hx
  rw [heq]
  have ht := abs_sub_le (testSum N a b (D q) (fun x => F (q,x)))
    (testSum N a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)))
    (testIntegral a b (primeAffineGateRegion A (c q)) (fun x => F (q,x)))
  linarith [ho N (by omega) q hq, hbd N (by omega) q hq]

end
end ImbalancedChen.Part5OriginalCompactParameterSandwich
