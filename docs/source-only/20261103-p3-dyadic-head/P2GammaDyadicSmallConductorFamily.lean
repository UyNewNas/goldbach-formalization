import ImbalancedChen.P2GammaDyadicFamilyEnergy

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The existing prime small-conductor theorem is invoked on every literal
clipped dyadic head interval. Its uniform constant is fixed BEFORE N and
the intervals. Summed beta L1 pays the whole interval family at a scale.
Two prefix lanes and logarithmically many head scales remain explicit.
-/

namespace ImbalancedChen.P2GammaDyadicSmallConductorFamily
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory
open P2GammaDyadicHeadIntervals P2GammaDyadicHeadSource P2GammaDyadicFamilyEnergy
open P2GammaJointRetainedComplement P2GammaRetainedActualNorms
open P2GammaRetainedCompleteScale P2GammaRetainedPhysicalRows
open P2GammaSmallConductorIntervalBridge P2GammaConvolutionLargeConductor
open P2GammaConductorScaleThreshold P2GammaDyadicConductorSum
open P2GammaExactConductorRegrouping P2GammaPrimeCharacterSW
open P2GammaPrimeTargetDeletion P2GammaVariablePrimeProfile
open P2GammaSmoothLogGrid P2GammaChosenLogGridBudget P2GammaOriginalScaleTransport
open P5OriginalU5CausalFinite (pairSupport)

private theorem floor_min (a b : ℝ) :
    Nat.floor (min a b) = min (Nat.floor a) (Nat.floor b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (Nat.floor_mono h)]
  · rw [min_eq_right h,min_eq_right (Nat.floor_mono h)]

private theorem floor_max (a b : ℝ) :
    Nat.floor (max a b) = max (Nat.floor a) (Nat.floor b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (Nat.floor_mono h)]
  · rw [max_eq_left h,max_eq_left (Nat.floor_mono h)]

/-- Monotone clamping normalizes empty intervals too. Both endpoints stay
inside [M,2M], so even empty rows use a legal prime-SW interval. -/
def clamp (M x : ℝ) : ℝ := min (2*M) (max M x)

def windowLo (δ : ℝ) (j d b : ℕ) : ℝ :=
  clamp (lower δ j) (((2*b)*2^d : ℕ) : ℝ)

def windowHi (δ : ℝ) (j d b : ℕ) : ℝ :=
  clamp (lower δ j) (((2*b+1)*2^d : ℕ) : ℝ)

theorem window_bounds (δ : ℝ) (j d b : ℕ) :
    lower δ j ≤ windowLo δ j d b ∧
    windowLo δ j d b ≤ windowHi δ j d b ∧ windowHi δ j d b ≤ 2*lower δ j := by
  have hM := lower_pos δ j
  have hab : (((2*b)*2^d : ℕ) : ℝ) ≤ (((2*b+1)*2^d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right (2^d) (by omega : 2*b ≤ 2*b+1)
  exact ⟨le_min (by linarith) (le_max_left _ _),
    min_le_min_left _ (max_le_max_left _ hab),min_le_left _ _⟩

/-- Exact natural endpoints: no rounding, tail or boundary reserve. -/
theorem clippedCell_eq_primeSWInterval (δ : ℝ) (j d b : ℕ) :
    clippedCell (ambientLo δ j) (ambientHi δ j) d b =
      primeSWInterval (windowLo δ j d b) (windowHi δ j d b) := by
  have hLP : ambientLo δ j ≤ ambientHi δ j :=
    Nat.floor_mono (by nlinarith [lower_pos δ j] : lower δ j ≤ 2*lower δ j)
  have hab : (2*b)*2^d ≤ (2*b+1)*2^d :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [primeSWInterval,windowLo,windowHi,clamp,floor_min,floor_max,
    Nat.floor_natCast]
  rw [clippedCell_eq_Ioc]
  ext p
  simp only [Finset.mem_Ioc]
  change (max (ambientLo δ j) ((2*b)*2^d) < p ∧
      p ≤ min (ambientHi δ j) ((2*b+1)*2^d)) ↔
    (min (ambientHi δ j) (max (ambientLo δ j) ((2*b)*2^d)) < p ∧
      p ≤ min (ambientHi δ j) (max (ambientLo δ j) ((2*b+1)*2^d)))
  omega

def levelLow (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l d : ℕ)
    (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (Q b0 : ℕ) : ℝ :=
  ∑ b ∈ dyadicKeys N d endpoint,
    lowConductorTotal (dyadicAlpha N δ j d b)
      (betaRow N c cs H δ j l d endpoint sigma b) 0 0
      (ambientHi δ j) (ambientHi δ l) Q b0

def lowCost (C height M V x : ℝ) (cs : List ℕ) (A : ℝ) (Q b0 : ℕ) : ℝ :=
  C*M*(height*(2*V)*(1+Real.log (2*V))^(cs.length+2))*
    (((2^b0 : ℕ) : ℝ)^2)*(logGauge Q)^2/(Real.log x)^A

/-- All actual small conductors, all old pairs, both endpoint lanes and
all head scales. The only chart restriction is actual occupancy, which
supplies the complete scale; inactive original charts are exactly zero.
No SW, BV, profile, coefficient-mass or family-conductor estimate is a premise. -/
theorem exists_chosen_all_scales_low (A : ℝ) (B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk : kappa < 1) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ c : ℕ,∀ cs : List ℕ,∀ j l : ℕ,
      (∃ t ∈ pairSupport N,Occupied N t c cs (2*(N : ℝ)^(1-kappa))
        (boundaryLogMesh B N) j l) →
      ∀ (sigma : (ℕ × ℕ) → ℂ) (height : ℝ),0 ≤ height →
      (∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) → ∀ Q b0 : ℕ,
      let δ := boundaryLogMesh B N
      let H := 2*(N : ℝ)^(1-kappa)
      let M := lower δ j
      let V := lower δ l
      (∑ d ∈ Finset.range (depth (ambientHi δ j)),
        (levelLow N c cs H δ j l d (endpointHi N c cs H δ j l) sigma Q b0+
         levelLow N c cs H δ j l d (endpointLo N c cs H δ j l) sigma Q b0)) ≤
        (2*(depth (ambientHi δ j) : ℝ))*lowCost C height M V (M*V) cs A Q b0 := by
  obtain ⟨D,hD,hAbel⟩ := exists_complexWeight_Abel_budget
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hbeta : 0 < 1-kappa := by linarith
  let W : ℝ := 1+2*D/(1-kappa)^B
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨C,hC,x0,hx0,hlow⟩ := actual_variable_prime_lowConductorTotal
    (eta:=34/1135) (J:=(B : ℝ)) (A:=A) (W:=W) (Ctarget:=1/(1-kappa))
    (by norm_num) hW (by positivity)
  obtain ⟨Ts,hTs,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk
  obtain ⟨Tl,hTl,hlarge⟩ := exists_original_scale_common_threshold x0 (1-kappa) hbeta
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (Nat.ceil Ts),eventually_ge_atTop (Nat.ceil Tl),
    eventually_ge_atTop (2 : ℕ),eventually_chosen_mesh_factor_two hB]
    with N hNs hNl hN hm
  intro c cs j l hocc sigma height hheight hsigma Q b0
  dsimp only
  let δ := boundaryLogMesh B N
  let H := 2*(N : ℝ)^(1-kappa)
  let M := lower δ j
  let V := lower δ l
  let x := M*V
  obtain ⟨t,ht,ho⟩ := hocc
  have hTsN : Ts ≤ (N : ℝ) := (Nat.le_ceil Ts).trans (by exact_mod_cast hNs)
  have hTlN : Tl ≤ (N : ℝ) := (Nat.le_ceil Tl).trans (by exact_mod_cast hNl)
  obtain ⟨hlogx,hM,hV,hMp,hVp,hlower,hupper,htarget⟩ :=
    hscale N hTsN t ht c cs δ hm.2.1 hm.2.2 j l ho
  have hxx : x0 ≤ x := hlarge (N : ℝ) hTlN x hlower
  have hbudget : 1+2*D/δ ≤ W*(Real.log x)^(B : ℝ) := by
    simpa only [W,δ,Real.rpow_natCast] using
      chosen_mesh_profile_budget (B:=B) hD0 hbeta (by omega : 0 < N) hm.1 hlogx hlower
  have hlevel (d : ℕ) (endpoint : (ℕ × ℕ) → ℕ) :
      levelLow N c cs H δ j l d endpoint sigma Q b0 ≤
        lowCost C height M V x cs A Q b0 := by
    let S := jointRetainedProducts N c cs H δ j l
    let G : ℝ := C*M*(((2^b0 : ℕ) : ℝ)^2)*(logGauge Q)^2/(Real.log x)^A
    have hG : 0 ≤ G := by
      have hM0 : 0 ≤ M := by linarith
      dsimp [G]
      positivity
    have hrow (b : ℕ) :
        lowConductorTotal (dyadicAlpha N δ j d b)
          (betaRow N c cs H δ j l d endpoint sigma b) 0 0
          (ambientHi δ j) (ambientHi δ l) Q b0 ≤
        G*rowMass S (dyadicBeta N c cs H δ j l d endpoint sigma b) := by
      let u := windowLo δ j d b
      let v := windowHi δ j d b
      obtain ⟨hMu,huv,hvM⟩ := window_bounds δ j d b
      have hsub : Icc u v ⊆ Ioi (0 : ℝ) := fun y hy =>
        (lower_pos δ j).trans_le (hMu.trans hy.1)
      have hfd : ∀ y ∈ Icc u v,DifferentiableAt ℝ (complexWeight δ j) y :=
        fun y hy => (complexWeight_hasDerivAt δ j (hsub hy)).differentiableAt
      have hfi : IntegrableOn (deriv (complexWeight δ j)) (Icc u v) :=
        (((complexWeight_contDiffOn δ j).continuousOn_deriv_of_isOpen
          isOpen_Ioi (by norm_num)).mono hsub).integrableOn_Icc
      have hvar : profileAbelNorm (complexWeight δ j) u v ≤ W*(Real.log x)^(B : ℝ) :=
        (hAbel δ hm.2.1 j M u v (lower_pos δ j) hMu huv hvM).trans hbudget
      have hsize : ∀ y ∈ Icc u v,‖complexWeight δ j y‖ ≤ W*(Real.log x)^(B : ℝ) := by
        intro y hy
        apply (complexWeight_norm_le_one δ j y).trans
        have hz : 0 ≤ 2*D/δ := div_nonneg (by positivity) hm.2.1.le
        exact (show 1 ≤ 1+2*D/δ by linarith).trans hbudget
      have hS : primeSWInterval u v ⊆ Finset.Icc 1 (ambientHi δ j) := by
        rw [← clippedCell_eq_primeSWInterval δ j d b]
        exact clippedCell_subset _ _ _ _
      have hT : S ⊆ Finset.Icc 1 (ambientHi δ l) :=
        jointRetainedProducts_subset_cap N c cs H hm.2.1 hm.2.2 j l
      have hv := hlow x M u v hxx hMp hM hMu huv hvM (complexWeight δ j)
        hfd hfi hvar hsize N (by omega) htarget (ambientHi δ j) (ambientHi δ l)
        Q b0 S (dyadicBeta N c cs H δ j l d endpoint sigma b) hS hT
      calc
        _ ≤ C*M*rowMass S (dyadicBeta N c cs H δ j l d endpoint sigma b)*
            (((2^b0 : ℕ) : ℝ)^2)*(logGauge Q)^2/(Real.log x)^A := by
          simpa only [dyadicAlpha,clippedCell_eq_primeSWInterval,betaRow,
            primeHeadCoefficient,u,v] using hv
        _ = _ := by dsimp [G]; ring
    have hmass := (dyadic_beta_norms N c cs H hm.2.1 hm.2.2 j l d hV
      endpoint sigma hheight hsigma).1
    calc
      _ ≤ ∑ b ∈ dyadicKeys N d endpoint,G*rowMass S
          (dyadicBeta N c cs H δ j l d endpoint sigma b) :=
        Finset.sum_le_sum (fun b hb => hrow b)
      _ = G*(∑ b ∈ dyadicKeys N d endpoint,rowMass S
          (dyadicBeta N c cs H δ j l d endpoint sigma b)) := (Finset.mul_sum _ _ _).symm
      _ ≤ G*(height*(2*V)*(1+Real.log (2*V))^(cs.length+2)) :=
        mul_le_mul_of_nonneg_left hmass hG
      _ = _ := by dsimp [G,lowCost]; ring
  calc
    _ ≤ ∑ _d ∈ Finset.range (depth (ambientHi δ j)),
        2*lowCost C height M V x cs A Q b0 := by
      apply Finset.sum_le_sum
      intro d hd
      have h1 := hlevel d (endpointHi N c cs H δ j l)
      have h2 := hlevel d (endpointLo N c cs H δ j l)
      linarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
                ring

/-- Finite character family reduction covering all nonprincipal characters
exactly through the existing low/high conductor split. No family estimate
is assumed; both ledgers are actual finite sums on the constructed rows. -/
theorem level_character_norm_le (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l d : ℕ) (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (Q b0 : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,‖levelCharacterSource N c cs H δ j l d endpoint sigma q‖) ≤
      levelLow N c cs H δ j l d endpoint sigma Q b0+
      levelHigh N c cs H δ j l d endpoint sigma Q b0 := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,∑ b ∈ dyadicKeys N d endpoint,
        ‖rectangleCharacterDiscrepancy
          (dyadicAlpha N δ j d b) (betaRow N c cs H δ j l d endpoint sigma b)
          0 0 (ambientHi δ j) (ambientHi δ l) q ((N : ZMod q)⁻¹)‖ :=
      Finset.sum_le_sum (fun q hq => norm_sum_le _ _)
    _ = ∑ b ∈ dyadicKeys N d endpoint,∑ q ∈ Finset.Icc 1 Q,
        ‖rectangleCharacterDiscrepancy
          (dyadicAlpha N δ j d b) (betaRow N c cs H δ j l d endpoint sigma b)
          0 0 (ambientHi δ j) (ambientHi δ l) q ((N : ZMod q)⁻¹)‖ := Finset.sum_comm
    _ ≤ ∑ b ∈ dyadicKeys N d endpoint,
        (lowConductorTotal (dyadicAlpha N δ j d b)
          (betaRow N c cs H δ j l d endpoint sigma b) 0 0
          (ambientHi δ j) (ambientHi δ l) Q b0+
        highConductorTotal (dyadicAlpha N δ j d b)
          (betaRow N c cs H δ j l d endpoint sigma b) 0 0
          (ambientHi δ j) (ambientHi δ l) Q b0) := by
      apply Finset.sum_le_sum
      intro b hb
      have h := sum_rectangleCharacterDiscrepancy_norm_le
        (dyadicAlpha N δ j d b) (betaRow N c cs H δ j l d endpoint sigma b)
        0 0 (ambientHi δ j) (ambientHi δ l) Q (fun q => (N : ZMod q)⁻¹)
      rw [allNonprincipalMajorant_eq_inducedTotal _ _ _ _ (by norm_num) (by norm_num),
        inducedTotal_eq_low_add_high _ _ _ _ _ _ _ b0] at h
      exact h
    _ = _ := Finset.sum_add_distrib

end
end ImbalancedChen.P2GammaDyadicSmallConductorFamily
