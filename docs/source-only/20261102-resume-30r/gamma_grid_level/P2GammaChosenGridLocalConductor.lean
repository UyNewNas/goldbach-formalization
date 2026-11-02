import ImbalancedChen.P2GammaChosenLogGridBudget
import ImbalancedChen.P2GammaRetainedLowRankLevel
import ImbalancedChen.P2GammaPrimeLocalConductorSaving
import ImbalancedChen.P2GammaUpperStripPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual Q rows, selected mesh and original literal mother list are inputs
to the implemented P conductor theorem.  Q's L1/L2/cap suppliers and O's
hat regularity are invoked, not added as hypotheses.  One fixed divisor
order is taken from Q17's already-defined literal list maximum.  There
is one original-N threshold before all mothers, marked pairs, grid
labels and moving residues.  This supplies the unweighted rectangle
norm sum on the canonical local cap; the same-rho outer summation and
the enhanced/high-rough-rank branches remain separate.
-/

namespace ImbalancedChen.P2GammaChosenGridLocalConductor
noncomputable section
open Filter Set MeasureTheory
open scoped BigOperators Topology
open P2GammaSmoothLogGrid P2GammaHeadWindowDictionary
open P2GammaRetainedCompleteScale P2GammaRetainedPhysicalRows
open P2GammaRetainedActualNorms P2GammaChosenLogGridBudget
open P2GammaRetainedLowRankLevel P2GammaPrimeLocalConductorSaving
open P2GammaOriginalScaleTransport P2GammaVariablePrimeProfile
open P2GammaConvolutionLargeConductor P2GammaSmallConductorIntervalBridge
open P2GammaCompleteProductTrimPayment P2GammaUpperStripPayment
open Wu2008DoubleSieve
open P5OriginalU5CausalFinite (pairSupport)

def motherNormOrder : ℕ := listMomentOrder originalMotherOccurrences

theorem mother_norm_orders {i c : ℕ} {cs : List ℕ}
    (hi : i ∈ secondFunctionalMotherPrefixIndices)
    (hcs : (c::cs) ∈ secondFunctionalMotherGammaWords i) :
    ((c::cs).length+1)^2-1 ≤ motherNormOrder ∧
      (c::cs).length ≤ motherNormOrder := by
  have hmem : (c::cs) ∈ originalMotherOccurrences :=
    List.mem_flatMap.mpr ⟨i,hi,hcs⟩
  have hmax := le_listMomentOrder hmem
  have hsquare : ((c::cs).length+1)^2 ≤ ((c::cs).length+2)^2 :=
    pow_le_pow_left₀ (Nat.zero_le _) (by omega) 2
  have hlength : (c::cs).length+1 ≤ ((c::cs).length+2)^2 := by nlinarith
  constructor
  · exact (Nat.sub_le_sub_right hsquare 1).trans hmax
  · dsimp [motherNormOrder]
    omega

/-- No physical norm, profile budget, level inequality, conductor bound
or scale comparison is a premise. Occupancy and original membership are
the source conditions; nonoccupied rows are already zero by Q18. -/
theorem exists_chosen_all_mother_local_conductor
    (A : ℝ) (B : ℕ) (hB : 0 < B) (kappa0 : ℝ) (hk : kappa0 < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ t ∈ pairSupport N,
      ∀ i ∈ secondFunctionalMotherPrefixIndices,
      ∀ c : ℕ, ∀ cs : List ℕ, (c::cs) ∈ secondFunctionalMotherGammaWords i →
      ∀ j l : ℕ,
      Occupied N t c cs (2*(N : ℝ)^(1-kappa0)) (boundaryLogMesh B N) j l →
      ∀ z : (q : ℕ) → ZMod q,
      let δ := boundaryLogMesh B N
      let M := lower δ j
      let V := lower δ l
      let x := M*V
      (∑ q ∈ Finset.Icc 1 (localModulusCap x),
        ‖rectangleCharacterDiscrepancy
          (actualAlpha N t c δ j)
          (actualBeta N t c cs (2*(N : ℝ)^(1-kappa0)) δ j l)
          0 0 (Nat.floor (2*M)) (Nat.floor (2*V)) q (z q)‖) ≤
        C*x/(Real.log x)^A := by
  obtain ⟨Dhat,hDhat,hAbel⟩ := exists_actual_head_Abel_budget
  have hDhat0 : 0 ≤ Dhat := zero_le_one.trans hDhat
  let W : ℝ := 1+2*Dhat/(1-kappa0)^B
  have hbeta : 0 < 1-kappa0 := by linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨C,hC,x0,hx0,hlocal⟩ := exists_actual_prime_local_conductor_saving
    A motherNormOrder motherNormOrder (34/1135) (1/20) (B : ℝ) W
      (1/(1-kappa0)) 2 (2*(3 : ℝ)^motherNormOrder) 2
      (2*(3 : ℝ)^motherNormOrder)
      (by norm_num) (by norm_num) hW (by positivity)
      (by norm_num) (by positivity) (by norm_num) (by positivity)
  obtain ⟨Ts,hTs,hscale⟩ := exists_trim_occupied_scale_threshold kappa0 hk
  obtain ⟨Tn,hTn,hnorm⟩ := exists_physical_rows_norm_threshold kappa0 hk
  obtain ⟨Tl,hTl,hlarge⟩ := exists_original_scale_common_threshold x0 (1-kappa0) hbeta
  obtain ⟨Nm,hNm⟩ := eventually_atTop.mp (eventually_chosen_mesh_factor_two hB)
  let N0 : ℕ := max 2 (max Nm (max (Nat.ceil Ts) (max (Nat.ceil Tn) (Nat.ceil Tl))))
  refine ⟨C,hC,N0,le_max_left _ _,?_⟩
  intro N hN t ht i hi c cs hcs j l ho z
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNmN : Nm ≤ N := by dsimp [N0] at hN; omega
  have hTsN : Ts ≤ (N : ℝ) := (Nat.le_ceil Ts).trans (by
    exact_mod_cast (show Nat.ceil Ts ≤ N by dsimp [N0] at hN; omega))
  have hTnN : Tn ≤ (N : ℝ) := (Nat.le_ceil Tn).trans (by
    exact_mod_cast (show Nat.ceil Tn ≤ N by dsimp [N0] at hN; omega))
  have hTlN : Tl ≤ (N : ℝ) := (Nat.le_ceil Tl).trans (by
    exact_mod_cast (show Nat.ceil Tl ≤ N by dsimp [N0] at hN; omega))
  obtain ⟨hlogN,hδ,hwidth⟩ := hNm N hNmN
  let δ := boundaryLogMesh B N
  let M := lower δ j
  let V := lower δ l
  let x := M*V
  obtain ⟨hlog,hM,hV,hMpow,hVpow,hlower,hupper,htarget⟩ :=
    hscale N hTsN t ht c cs δ hδ hwidth j l ho
  have hx0x : x0 ≤ x := hlarge (N : ℝ) hTlN x hlower
  obtain ⟨_hMp,_hVp,_hlo,_hhi,_htarget,hEa,hEb,hmass,hP,hVcap⟩ :=
    hnorm N hTnN t ht i hi c cs hcs δ hδ hwidth j l ho
  obtain ⟨hc,hs⟩ := occupied_head_geometry hδ hwidth ho
  obtain ⟨hlo,huv,hhi⟩ := source_nonempty_geometry hc hs
  have hsub : Icc (clipLo N t c M) (clipHi N t c M) ⊆ Ioi (0 : ℝ) :=
    fun y hy => (lower_pos δ j).trans_le (hlo.trans hy.1)
  have hfd : ∀ y ∈ Icc (clipLo N t c M) (clipHi N t c M),
      DifferentiableAt ℝ (complexWeight δ j) y :=
    fun y hy => (complexWeight_hasDerivAt δ j (hsub hy)).differentiableAt
  have hfi : IntegrableOn (deriv (complexWeight δ j))
      (Icc (clipLo N t c M) (clipHi N t c M)) :=
    (((complexWeight_contDiffOn δ j).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)).mono hsub).integrableOn_Icc
  have hbudget : 1+2*Dhat/δ ≤ W*(Real.log x)^(B : ℝ) := by
    simpa only [W,δ,Real.rpow_natCast] using
      chosen_mesh_profile_budget (B:=B) (zero_le_one.trans hDhat) hbeta
        (by omega : 0 < N) hlogN hlog hlower
  have hvar : profileAbelNorm (complexWeight δ j)
      (clipLo N t c M) (clipHi N t c M) ≤ W*(Real.log x)^(B : ℝ) :=
    (hAbel δ hδ N t c j).trans hbudget
  have hsize : ∀ y ∈ Icc (clipLo N t c M) (clipHi N t c M),
      ‖complexWeight δ j y‖ ≤ W*(Real.log x)^(B : ℝ) := by
    intro y hy
    apply (complexWeight_norm_le_one δ j y).trans
    have hnonneg : 0 ≤ 2*Dhat/δ := div_nonneg (by positivity) hδ.le
    exact (show 1 ≤ 1+2*Dhat/δ by linarith).trans hbudget
  obtain ⟨hDle,hEle⟩ := mother_norm_orders hi hcs
  have hDlog := pow_le_pow_right₀ hlog hDle
  have hElog := pow_le_pow_right₀ hlog hEle
  have hDthree := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hDle
  have hEthree := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hEle
  have hEa' : rowEnergy (actualAlpha N t c δ j) 0 (Nat.floor (2*M)) ≤
      (2 : ℝ)^2*M*(Real.log x)^motherNormOrder := by
    apply hEa.trans
    exact mul_le_mul_of_nonneg_left hDlog (by positivity)
  have hEb' : rowEnergy
      (actualBeta N t c cs (2*(N : ℝ)^(1-kappa0)) δ j l)
      0 (Nat.floor (2*V)) ≤
      (2*(3 : ℝ)^motherNormOrder)^2*V*(Real.log x)^motherNormOrder := by
    apply hEb.trans
    gcongr
  have hmass' : rowMass
      (retainedComplementSupport N t c cs (2*(N : ℝ)^(1-kappa0)) δ j l)
      (retainedBeta N t c cs (2*(N : ℝ)^(1-kappa0)) δ j l) ≤
      (2*(3 : ℝ)^motherNormOrder)*V*(Real.log x)^motherNormOrder := by
    apply hmass.trans
    gcongr
  obtain ⟨hS,hT⟩ := actual_rows_supported ht hδ hwidth j l ho
  have hQ := localModulusCap_below_half
    (show 0 ≤ x by dsimp [x,M,V]; positivity)
  have hout := hlocal x M V (clipLo N t c M) (clipHi N t c M)
    hx0x rfl hMpow hVpow hlo huv hhi (complexWeight δ j) hfd hfi hvar hsize
    N (by omega) htarget (Nat.floor (2*M)) (Nat.floor (2*V)) (localModulusCap x)
    (retainedComplementSupport N t c cs (2*(N : ℝ)^(1-kappa0)) δ j l)
    (retainedBeta N t c cs (2*(N : ℝ)^(1-kappa0)) δ j l) hS hT z
    hEa' hEb' hmass' hP hVcap hQ
  exact hout

end
end ImbalancedChen.P2GammaChosenGridLocalConductor
