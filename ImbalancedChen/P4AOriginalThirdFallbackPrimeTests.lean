import ImbalancedChen.P4AOriginalThirdFallbackRegions
import ImbalancedChen.ActualPrimeBoxTestFunctions
import ImbalancedChen.AffinePrimeGates
import ImbalancedChen.ActualExtendedThirdCompactResidualProfile

/-! Continuous tests of the literal physical gain on disjoint original
chart images. Trimmed points keep quantitative clearance for the actual
historical first-stop, mesh ordering, and both old third-level cubes. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackPrimeTests
noncomputable section
open Filter Set MeasureTheory
open scoped Classical BigOperators Topology
open P4AOriginalThirdFallbackArchive (Cell)
open P4AOriginalThirdFallbackSlope (physicalIntegrand)
open P4AOriginalThirdFallbackChartIntegral (Point kernel)
open P4AOriginalThirdFallbackJacobian (region slot_le_physical_images)
open P4AOriginalThirdFallbackRegions
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open VariableEnvelope (v)

def cut : ℝ := 1/32
theorem cut_pos : 0 < cut := by norm_num [cut]
abbrev cube : Set Point := logPrimeBox (fun _ => cut) (fun _ => rho)
abbrev primes (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 3 => cut) (fun _ => rho)
def safeFactor (L : ℝ) (p : Point) : ℝ :=
  4*actualExtendedThirdLowerFactor ((L-p 0-p 1-p 2)/max cut (p 2))/max cut (p 2)
def profile (p : Point) : ℝ :=
  max 0 (safeFactor (v (p 1+p 2)) p-safeFactor (v (p 0)) p)

theorem continuous_profile : Continuous profile := by
  have hh : Continuous (fun p : Point => max cut (p 2)) := by fun_prop
  have hn (p : Point) : max cut (p 2) ≠ 0 := (cut_pos.trans_le (le_max_left _ _)).ne'
  have hs (L : Point → ℝ) (hc : Continuous L) : Continuous (fun p => safeFactor (L p) p) :=
    (continuous_const.mul (continuous_actualExtendedThirdLowerFactor.comp
      ((((hc.sub (continuous_apply 0)).sub (continuous_apply 1)).sub (continuous_apply 2)).div hh hn))).div hh hn
  have hV : Continuous v := by unfold v VariableEnvelope.A VariableEnvelope.C; fun_prop
  exact continuous_const.max ((hs _ (hV.comp ((continuous_apply 1).add (continuous_apply 2)))).sub
    (hs _ (hV.comp (continuous_apply 0))))

theorem guard_cube {p : Point} (hg : ThirdRegion (p 0) (p 1) (p 2)) : p ∈ cube := by
  obtain ⟨_,hx,hz,hzy,_,hs,_,_,hcut,_⟩ := hg
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i <;> dsimp [cut] <;> constructor <;> linarith

theorem guard_profile {p : Point} (hg : ThirdRegion (p 0) (p 1) (p 2)) :
    profile p = primeTupleMinusProfile (v (p 1+p 2)) p - primeTupleMinusProfile (v (p 0)) p := by
  have hz := hg.2.2.1
  have hcut := (mem_logPrimeBox.mp (guard_cube hg) 2).1
  have hcap := (third_initial_physical_gates hg).2.2.2.2.2.le
  have harg := div_le_div_of_nonneg_right (by linarith only [hcap] :
    v (p 0)-p 0-p 1-p 2 ≤ v (p 1+p 2)-p 0-p 1-p 2) hz.le
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (monotone_actualExtendedThirdLowerFactor harg) (by norm_num : (0:ℝ) ≤ 4)) hz.le
  rw [profile,safeFactor,safeFactor,max_eq_right hcut,max_eq_right (sub_nonneg.mpr hh)]
  rw [primeTupleMinusProfile_eq_extendedThirdFactor _ _ hz,
    primeTupleMinusProfile_eq_extendedThirdFactor _ _ hz]

theorem kernel_density {p : Point} (hg : ThirdRegion (p 0) (p 1) (p 2)) :
    profile p*(∏ i,1/p i) = kernel p := by
  have hb := mem_logPrimeBox.mp (guard_cube hg)
  have hp (i : Fin 3) := cut_pos.trans_le (hb i).1
  rw [guard_profile hg,primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hp 2),
    primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hp 2)]
  unfold kernel physicalIntegrand
  rw [Fin.prod_univ_three]
  field_simp [(hp 0).ne',(hp 1).ne',(hp 2).ne'] <;> ring

def clearance (p : Point) : Fin 5 → ℝ :=
  ![rho-p 0,p 0-p 1,p 1-p 2,v (p 0)-3*p 0,v (p 0)-p 0-p 1-3*p 2]
abbrev Gate := (Fin 3 × Fin 3) ⊕ Fin 5
def gate (c : Cell) : Gate → Point → ℝ
  | .inl ij => wall c ij.1 ij.2
  | .inr i => fun p => clearance p i
theorem continuous_gate (c : Cell) (g : Gate) : Continuous (gate c g) := by
  rcases g with ⟨i,j⟩ | i
  · exact continuous_wall c i j
  · fin_cases i <;> simp [gate,clearance,v,VariableEnvelope.A,VariableEnvelope.C] <;> fun_prop
theorem region_gate_pos {c : Cell} {p : Point} (hp : p ∈ region c) (g : Gate) : 0 < gate c g p := by
  rcases g with ⟨i,j⟩ | i
  · exact (region_iff_walls c p).mp hp i j
  · have hg := region_guard hp
    have h0 := above_mu_old_cap_gt_cube hg.1 hg.2.1
    have hs := third_initial_physical_gates hg
    obtain ⟨_,hx,hz,hzy,_,hr,_⟩ := hg
    fin_cases i <;> dsimp [gate,clearance] <;> linarith [hs.2.2.2.1]

def ramp (r : ℕ) (c : Cell) (p : Point) : ℝ :=
  ∏ g : Gate,affinePrimeClamp (gate c g p/width r-1)
def test (r : ℕ) (c : Cell) (p : Point) : ℝ := profile p*ramp r c p
def combined (r : ℕ) (p : Point) : ℝ := ∑ c : Cell,test r c p

theorem ramp_bounds (r : ℕ) (c : Cell) (p : Point) : 0 ≤ ramp r c p ∧ ramp r c p ≤ 1 :=
  ⟨Finset.prod_nonneg (fun _ _ => (affinePrimeClamp_bounds _).1),
    Finset.prod_le_one (fun _ _ => (affinePrimeClamp_bounds _).1) (fun _ _ => (affinePrimeClamp_bounds _).2)⟩
theorem continuous_test (r : ℕ) (c : Cell) : Continuous (test r c) :=
  continuous_profile.mul (continuous_finsetProd _ (fun g _ => continuous_affinePrimeClamp.comp
    (((continuous_gate c g).div_const _).sub continuous_const)))
theorem continuous_combined (r : ℕ) : Continuous (combined r) :=
  continuous_finsetSum _ (fun c _ => continuous_test r c)
theorem test_bounds (r : ℕ) (c : Cell) (p : Point) : 0 ≤ test r c p ∧ test r c p ≤ profile p :=
  ⟨mul_nonneg (le_max_left _ _) (ramp_bounds r c p).1,
    (mul_le_mul_of_nonneg_left (ramp_bounds r c p).2 (le_max_left _ _)).trans_eq (mul_one _)⟩

theorem gates_of_ne {r : ℕ} {c : Cell} {p : Point} (hn : test r c p ≠ 0) :
    ∀ g : Gate,width r < gate c g p := by
  intro g
  by_contra! hh
  have hz : affinePrimeClamp (gate c g p/width r-1) = 0 := by
    apply affinePrimeClamp_eq_zero
    linarith only [(div_le_one (width_pos r)).mpr hh]
  exact hn (by rw [test,ramp,Finset.prod_eq_zero (Finset.mem_univ g) hz,mul_zero])

theorem region_of_ne {r : ℕ} {c : Cell} {p : Point} (hn : test r c p ≠ 0) : p ∈ region c :=
  (region_iff_walls c p).mpr (fun i j => (width_pos r).trans (gates_of_ne hn (.inl (i,j))))

theorem combined_bounds (r : ℕ) (p : Point) : 0 ≤ combined r p ∧ combined r p ≤ profile p := by
  constructor
  · exact Finset.sum_nonneg (fun c _ => (test_bounds r c p).1)
  · by_cases he : ∃ c : Cell,test r c p ≠ 0
    · obtain ⟨c,hc⟩ := he
      rw [combined,Finset.sum_eq_single c]
      · exact (test_bounds r c p).2
      · intro d _ hdc
        by_contra h
        exact hdc (unique_region (region_of_ne h) (region_of_ne hc))
      · simp
    · push_neg at he
      simp [combined,he,profile]

theorem region_clearance_of_combined_ne {r : ℕ} {p : Point} (hp : combined r p ≠ 0) :
    ThirdRegion (p 0) (p 1) (p 2) ∧ ∀ j : Fin 5,width r < clearance p j := by
  obtain ⟨c,hc⟩ : ∃ c : Cell,test r c p ≠ 0 := by
    by_contra! h
    exact hp (by simp [combined,h])
  exact ⟨region_guard (region_of_ne hc),fun j => gates_of_ne hc (.inr j)⟩

theorem ramp_one {c : Cell} {p : Point} (hp : p ∈ region c) : ∀ᶠ r in atTop,ramp r c p=1 := by
  have h : ∀ᶠ r : ℕ in atTop,∀ g : Gate,width r < gate c g p/2 := by
    apply eventually_all.mpr
    intro g
    exact width_tendsto.eventually (gt_mem_nhds (half_pos (region_gate_pos hp g)))
  filter_upwards [h] with r hr
  apply Finset.prod_eq_one
  intro g _
  apply affinePrimeClamp_eq_one
  linarith only [(le_div_iff₀ (width_pos r)).mpr (by linarith [hr g]) :
    2 ≤ gate c g p/width r]

def cellTestIntegral (r : ℕ) (c : Cell) : ℝ := ∫ p in cube,test r c p*(∏ i,1/p i)
def testIntegral (r : ℕ) : ℝ := ∫ p in cube,combined r p*(∏ i,1/p i)
def testSum (r N : ℕ) : ℝ := actualPrimeBoxTestSum N (fun _ : Fin 3 => cut) (fun _ => rho) (combined r)
def total : ℝ := ∑ c : Cell,∫ p in region c,kernel p

theorem cell_limit (c : Cell) : Tendsto (fun r => cellTestIntegral r c) atTop (𝓝 (∫ p in region c,kernel p)) := by
  let dens := fun p : Point => ∏ i,1/p i
  have hm := measurableSet_logPrimeBox (fun _ : Fin 3 => cut) (fun _ => rho)
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict cube)
    (F := fun r p => test r c p*dens p) (f := (region c).indicator kernel)
    (fun p => profile p*dens p)
    (fun r => (integrableOn_logPrimeBox_test_cube cut_pos (test r c) (continuous_test r c).continuousOn).aestronglyMeasurable)
    (integrableOn_logPrimeBox_test_cube cut_pos profile continuous_profile.continuousOn)
    (fun r => by
      filter_upwards [ae_restrict_mem hm] with p hp
      have hd : 0 ≤ dens p := Finset.prod_nonneg (fun i _ => (one_div_pos.mpr
        (cut_pos.trans_le ((mem_logPrimeBox.mp hp i).1))).le)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (test_bounds _ _ _).1 hd)]
      exact mul_le_mul_of_nonneg_right (test_bounds _ _ _).2 hd)
    (by
      filter_upwards [ae_restrict_mem hm] with p hp
      apply tendsto_const_nhds.congr'
      by_cases hreg : p ∈ region c
      · filter_upwards [ramp_one hreg] with r hr
        rw [indicator_of_mem hreg,test,hr,mul_one]
        exact (kernel_density (region_guard hreg)).symm
      · filter_upwards with r
        rw [indicator_of_notMem hreg,show test r c p=0 from
          Classical.byContradiction (fun hn => hreg (region_of_ne hn)),zero_mul])
  have he : (∫ p in cube,(region c).indicator kernel p) = ∫ p in region c,kernel p := by
    rw [setIntegral_indicator (region_measurable c),inter_eq_right.mpr (fun _ hp => guard_cube (region_guard hp))]
  simpa only [cellTestIntegral,dens,he] using h

theorem integral_limit : Tendsto testIntegral atTop (𝓝 total) := by
  have he (r : ℕ) : testIntegral r = ∑ c : Cell,cellTestIntegral r c := by
    unfold testIntegral combined cellTestIntegral
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun c _ => integrableOn_logPrimeBox_test_cube cut_pos (test r c)
      (continuous_test r c).continuousOn)]
  have hf : testIntegral = fun r => ∑ c : Cell,cellTestIntegral r c := funext he
  rw [hf]
  apply tendsto_finsetSum
  exact fun c _ => cell_limit c
theorem prime_limit (r : ℕ) : Tendsto (testSum r) atTop (𝓝 (testIntegral r)) :=
  tendsto_actualPrimeBoxTestSum_cube cut_pos (by norm_num [cut,rho]) (combined r) (continuous_combined r).continuousOn

end
end ImbalancedChen.P4AOriginalThirdFallbackPrimeTests

