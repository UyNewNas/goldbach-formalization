import ImbalancedChen.P2OriginalCompactMovingGateMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact ambient reboxing followed by the finite-net theorem. The target is
N throughout. The real power N^L is never made a new integer target.
-/
namespace ImbalancedChen.P2OriginalCompactScaledPrimeMass

noncomputable section
open MeasureTheory Filter Set
open P2OriginalBankChildPrimeMass P2OriginalCompactMovingGateMass
open scoped Classical BigOperators Topology Pointwise

theorem moving_box_subset_ambient {d N : ℕ} (hN : 1<N)
    {Lmin Lmax L : ℝ} (hmin : 0<Lmin) (hL : L∈Icc Lmin Lmax) :
    actualPrimeBoxTuples N (fun _ : Fin d => L/10) (fun _ => 3*L/5) ⊆
      actualPrimeBoxTuples N (fun _ => Lmin/20) (fun _ => Lmax) := by
  intro p hp
  obtain ⟨hprime,hbox⟩ := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp
  apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
  refine ⟨hprime,mem_logPrimeBox.mpr ?_⟩
  intro i
  have hi := mem_logPrimeBox.mp hbox i
  constructor <;> nlinarith only [hi.1,hi.2,hL.1,hL.2,hmin]

theorem moving_box_mass_le_ambient {d N : ℕ} (hN : 1<N)
    {Lmin Lmax L : ℝ} (hmin : 0<Lmin) (hL : L∈Icc Lmin Lmax) :
    actualPrimeBoxMass N (fun _ : Fin d => L/10) (fun _ => 3*L/5) ≤
      actualPrimeBoxMass N (fun _ => Lmin/20) (fun _ => Lmax) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (moving_box_subset_ambient hN hmin hL)
  intro p hp _
  exact actualPrimeBoxWeight_nonneg hp

theorem affine_dilation_mem {d r : ℕ} {L : ℝ} (hL : 0<L)
    (A : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (x : Fin d → ℝ) :
    x∈primeAffineGateRegion A (fun j => L*c j) ↔
      L⁻¹ • x∈primeAffineGateRegion A c := by
  apply forall_congr'
  intro j
  rw [map_smul,smul_eq_mul,← div_eq_inv_mul,div_lt_iff₀ hL]
  simpa only [mul_comm]

/-- The enlarged enumeration is exact: any added tuple has zero gated
summand. Target deletion is inherited from the actual original carrier. -/
theorem scaledPrimeSum_eq_ambient {d r N : ℕ} (hN : 1<N)
    {Lmin Lmax L : ℝ} (hmin : 0<Lmin) (hL : L∈Icc Lmin Lmax)
    (A : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hD : primeAffineGateRegion A c ⊆ cube d) (f : (Fin d → ℝ) → ℝ) :
    scaledPrimeSum N L (primeAffineGateRegion A c) f =
      actualPrimeBoxTestSum N (fun _ : Fin d => Lmin/20) (fun _ => Lmax)
        ((primeAffineGateRegion A (fun j => L*c j)).indicator
          (fun x => f (L⁻¹ • x))) := by
  have hpos : 0<L := hmin.trans_le hL.1
  have he (x : Fin d → ℝ) :
      (primeAffineGateRegion A c).indicator f (L⁻¹ • x) =
      (primeAffineGateRegion A (fun j => L*c j)).indicator
        (fun x => f (L⁻¹ • x)) x := by
    by_cases hx : x∈primeAffineGateRegion A (fun j => L*c j)
    · simp only [indicator_of_mem hx,indicator_of_mem ((affine_dilation_mem hpos A c x).mp hx)]
    · simp only [indicator_of_notMem hx,
        indicator_of_notMem (mt (affine_dilation_mem hpos A c x).mpr hx)]
  unfold scaledPrimeSum actualPrimeBoxTestSum
  simp_rw [he]
  apply Finset.sum_subset (moving_box_subset_ambient hN hmin hL)
  intro p hp hnot
  have hx : actualPrimeTupleLog N p∉primeAffineGateRegion A (fun j => L*c j) := by
    intro hx
    have hd := hD ((affine_dilation_mem hpos A c _).mp hx)
    have hbase := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).1
    apply hnot
    apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
    refine ⟨hbase,mem_logPrimeBox.mpr ?_⟩
    intro i
    have hh := mem_logPrimeBox.mp hd i
    simp only [Pi.smul_apply,smul_eq_mul,← div_eq_inv_mul] at hh
    constructor
    · have hh' := (le_div_iff₀ hpos).mp hh.1
      nlinarith only [hh']
    · have hh' := (div_lt_iff₀ hpos).mp hh.2
      nlinarith only [hh']
  simp only [indicator_of_notMem hx,mul_zero]

theorem ambient_region_eq_dilation {d r : ℕ}
    {Lmin Lmax L : ℝ} (hmin : 0<Lmin) (hL : L∈Icc Lmin Lmax)
    (A : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hD : primeAffineGateRegion A c ⊆ cube d) :
    logPrimeBox (fun _ : Fin d => Lmin/20) (fun _ => Lmax) ∩
      primeAffineGateRegion A (fun j => L*c j) = L • primeAffineGateRegion A c := by
  have hpos : 0<L := hmin.trans_le hL.1
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hpos.ne',mem_inter_iff,
    affine_dilation_mem hpos A c x]
  constructor
  · exact And.right
  · intro hx
    refine ⟨mem_logPrimeBox.mpr ?_,hx⟩
    intro i
    have hh := mem_logPrimeBox.mp (hD hx) i
    simp only [Pi.smul_apply,smul_eq_mul,← div_eq_inv_mul] at hh
    have hlo := (le_div_iff₀ hpos).mp hh.1
    have hhi := (div_lt_iff₀ hpos).mp hh.2
    constructor <;> nlinarith only [hlo,hhi,hmin,hL.1,hL.2]

/-- A globally continuous extension is made only below Lmin/2. On the
admitted interval it is exactly the physical inverse dilation. -/
def dilationKernel {d : ℕ} (Lmin : ℝ) (f : (Fin d → ℝ) → ℝ)
    (q : ℝ × (Fin d → ℝ)) : ℝ := f ((max (Lmin/2) q.1)⁻¹ • q.2)

theorem dilationKernel_continuous {d : ℕ} {Lmin : ℝ} (hmin : 0<Lmin)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) : Continuous (dilationKernel Lmin f) := by
  apply hf.comp
  apply Continuous.smul
  · apply (continuous_const.max continuous_fst).inv₀
    intro q
    exact (lt_of_lt_of_le (by positivity : (0:ℝ)<Lmin/2) (le_max_left _ _)).ne'
  · exact continuous_snd

theorem dilationKernel_on_interval {d : ℕ} {Lmin Lmax L : ℝ}
    (hmin : 0<Lmin) (hL : L∈Icc Lmin Lmax)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    dilationKernel Lmin f (L,x)=f (L⁻¹ • x) := by
  simp only [dilationKernel,max_eq_right (show Lmin/2≤L by linarith [hL.1])]

/-- Main normalized API for finite additional affine gates and signed
continuous tests. The fixed positive compact interval precedes N, L and d.
Only a primitive pointwise bound on the kernel is required. -/
theorem compact_uniform_scaled_affine {d r : ℕ}
    {Lmin Lmax B epsilon : ℝ} (hmin : 0<Lmin) (hmax : Lmin≤Lmax)
    (hB : 0≤B) (hepsilon : 0<epsilon)
    (A : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hA : ∀j,A j≠0) (hD : primeAffineGateRegion A c ⊆ cube d)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (hbound : ∀x,|f x|≤B) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀L∈Icc Lmin Lmax,
      |scaledPrimeSum N L (primeAffineGateRegion A c) f-
        (∫x in primeAffineGateRegion A c,f x*(∏i,1/x i))|<epsilon := by
  obtain ⟨T,hT⟩ := compact_uniform_affine_gates (K:=Icc Lmin Lmax) isCompact_Icc
    (a:=Lmin/20) (b:=Lmax) (by positivity) (by linarith) hB A hA
    (fun L j => L*c j) (fun _ => continuous_id.mul continuous_const)
    (dilationKernel Lmin f) (dilationKernel_continuous hmin f hf)
    (fun L hL x _ => hbound _) hepsilon
  refine ⟨max 2 T,?_⟩
  intro N hN L hL
  have hNL : 1<N := by omega
  have hh := hT N (by omega) L hL
  have hpos : 0<L := hmin.trans_le hL.1
  change |actualPrimeBoxTestSum N (fun _ : Fin d => Lmin/20) (fun _ => Lmax)
      ((primeAffineGateRegion A (fun j => L*c j)).indicator
        (fun x => dilationKernel Lmin f (L,x)))-
      (∫x in logPrimeBox (fun _ : Fin d => Lmin/20) (fun _ => Lmax) ∩
        primeAffineGateRegion A (fun j => L*c j),
        dilationKernel Lmin f (L,x)*(∏i,1/x i))|<epsilon at hh
  simp_rw [dilationKernel_on_interval hmin hL] at hh
  rw [← scaledPrimeSum_eq_ambient hNL hmin hL A c hD f,
    ambient_region_eq_dilation hmin hL A c hD,
    integral_log_density_dilation hpos] at hh
  exact hh

end
end ImbalancedChen.P2OriginalCompactScaledPrimeMass
