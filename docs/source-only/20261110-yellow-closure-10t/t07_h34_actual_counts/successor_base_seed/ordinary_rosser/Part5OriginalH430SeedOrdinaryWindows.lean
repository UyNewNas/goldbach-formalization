import ImbalancedChen.Part5OriginalH430SeedChildRosserDictionary
import ImbalancedChen.Part5OriginalH430W2SignedSingletons

/-! Identify the seed's three literal negative windows with original action
zero and bound their total child normalization, allowing the uniform local
Rosser error to be summed before the external history mark. -/
namespace ImbalancedChen.Part5OriginalH430SeedOrdinaryWindows
noncomputable section
open Set Finset Real MeasureTheory Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2OriginalPositiveSameQMassLift P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2SeedOmegaLiteralFunctional (negative)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430OrdinaryPairWalls (prime_coordinate_ne_rat)
open Part5OriginalH430BankOrdinarySingletons (Lane anchor top integral window ordinaryWindow)
open Part5OriginalH430W2UpperPolygons (parameterQ original_parameters physical)
open Part5OriginalH430OrdinarySingletonKernel (ordinaryLowerIntegral canonical_lower_log clippedLower)
open scoped Classical BigOperators Interval

def lane (j : Fin 3) : Lane := .inr (0,j)
def edge (j : Fin 3) : ℝ := ![5/11,10/29,25/61] j
def stop (j : Fin 3) : ℝ := ![11/5,29/10,61/25] j
def W (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 3) : Finset ℕ :=
  primeWindow N (cutoff Q d (227/50)) (cutoff Q d (stop j))

theorem coordinates (j : Fin 3) : anchor (lane j)=227/50 ∧ top (lane j)=edge j ∧
    a0 (originalW2At 0)=50/227 ∧ singletonTop (originalW2At 0) j=edge j ∧
    edge j=1/stop j ∧ (50/227:ℝ)<edge j ∧ edge j≤5/11 := by
  change (originalW2At 0).s0=_ ∧ singletonTop (originalW2At 0) j=_ ∧ _ ∧ _ ∧ _
  rw [←original_parameters]
  fin_cases j <;> norm_num [physical,parameterQ,edge,stop,singletonTop,a0,b,a2,a3]

theorem W_eq {N d : ℕ} {Q L : ℝ} (hd : 0<d) (hQ : Q=(d:ℝ)*(N:ℝ)^L) (j : Fin 3) :
    W N Q d j=window N Q L d (lane j) := by
  rw [W,window,(coordinates j).1,(coordinates j).2.1,(coordinates j).2.2.2.2.1,
    cutoff_eq_physical_power hd hQ (s:=stop j)]
  congr 2
  ring

theorem integral_eq (j : Fin 3) : integral (lane j)=negative (edge j) := by
  unfold integral ordinaryLowerIntegral negative
  rw [(coordinates j).1,(coordinates j).2.1]
  have hg := (coordinates j).2.2.2.2.2
  have hlo : (1/(227/50):ℝ)=50/227 := by norm_num
  rw [hlo,intervalIntegral.integral_of_le (show P2SeedOmegaLiteralFibre.a0≤edge j by exact hg.1.le),
    ←integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hx := hu.2.trans_le hg.2
  have hl := hu.1
  change (50/227:ℝ)<u at hl
  change P5CanonicalUpperCancellation.lowerBar ((227/50)*(1-u))/(u*(1-u))=
    log ((227/50)*(1-u)-1)/(u*(1-u))
  rw [canonical_lower_log (by linarith : (227/50)*(1-u)≤4),clippedLower,
    min_eq_right (by linarith : (227/50)*(1-u)-1≤3),max_eq_right (by linarith : 1≤(227/50)*(1-u)-1)]

private theorem theta_window {N n p d : ℕ} {k : Root} {t L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hQ : rootQ N n k t p=(d:ℝ)*(N:ℝ)^L) (j : Fin 3) :
    (∑ q∈W N (rootQ N n k t p) d j,thetaAtom N (rootQ N n k t p) (d*q))=
      singleChildTheta N (rootQ N n k t p) L d (a0 (originalW2At 0)) (singletonTop (originalW2At 0) j) := by
  have h := coordinates j
  have hz (s : ℝ) : cutoff (rootQ N n k t p) d s=(N:ℝ)^(L*(1/s)) := by
    rw [cutoff_eq_physical_power hd hQ]; congr 1; ring
  rw [W,hz,hz,h.2.2.1,h.2.2.2.1,←h.2.2.2.2.1,
    show (1/(227/50):ℝ)=50/227 by norm_num,
    single_window_reindex hN hL (by norm_num : (1/5:ℝ)≤50/227)
      (by linarith only [h.2.2.2.2.2.2] : edge j≤1/2)]
  unfold singleChildTheta
  apply sum_congr rfl
  intro x hx
  have hp (i : Fin 1) := (mem_actualPrimeBoxTuples_iff.mp hx i)
  have hne := prime_coordinate_ne_rat hN hL hQ x (fun i => ⟨(hp i).1,(hp i).2.1⟩) 0 (50/227)
  have hh : normalizedLog N L x∈singleHalf (50/227) (edge j) ↔
      L⁻¹ • actualPrimeTupleLog N x∈singleDomain (50/227) (edge j) := by
    change (50/227≤normalizedLog N L x 0 ∧ _) ↔ (50/227<normalizedLog N L x 0 ∧ _)
    push_cast at hne
    exact ⟨fun a => ⟨lt_of_le_of_ne a.1 hne.symm,a.2⟩,fun a => ⟨a.1.le,a.2⟩⟩
  simp only [hh]

theorem ordinary_and_child_mass {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ (l : LevelIndex N n k t p dep) (j : Fin 3),
        let Q := rootQ N n k t p; let d := wordProduct l; let L := wordLevel l
        |ordinaryWindow N Q L d (lane j)-thetaAtom N Q d*negative (edge j)|≤ε*thetaAtom N Q d ∧
        (∑ q∈W N Q d j,thetaAtom N Q (d*q)) ≤ 4*thetaAtom N Q d := by
  have hF : frozenResidualFloor≤1 := by
    unfold frozenResidualFloor
    have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])
  obtain ⟨Ta,h4,ha⟩ := Part5OriginalH430BankOrdinarySingletons.all_original_singletons he
  obtain ⟨Tb,hb⟩ := all36_positive_sameQ_singleton_lift frozenResidualFloor_pos hF (by norm_num : (0:ℝ)<1)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN n k t p dep ht ht' hn hp l j
  have hNa := (le_max_left _ _).trans hN
  have hN4 := h4.trans hNa
  let Q := rootQ N n k t p
  let d := wordProduct l
  let L := wordLevel l
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hL' := frozenResidualFloor_pos.trans_le hL.1
  have hθ := thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one (by omega) hd hL' hQ)
  constructor
  · simpa only [integral_eq j] using ha N hNa n k t p dep ht ht' hn hp l (lane j)
  · rw [theta_window (by omega) hd hL' hQ j]
    have h := hb N ((le_max_right _ _).trans hN) Q {d} (fun _ => (1:ℝ)) (fun _ => L)
      (fun _ => 0) (fun _ => j) (by simpa using hd) (by simp) (by simpa using hL) (by simpa using hQ)
    simp only [Theta_eq_sum_atoms,sum_singleton,one_mul] at h
    have hg := W2SingletonDomain_subset (originalRepairedW2Bank_geometry _ (originalW2At_mem 0)) j
    have hi := singletonMass_le_three hg
    rw [singletonMass_eq_original (measurableSet_W2SingletonDomain _ _) hg] at hi
    linarith only [(abs_le.mp h).2,mul_le_mul_of_nonneg_left hi hθ]

end
end ImbalancedChen.Part5OriginalH430SeedOrdinaryWindows
