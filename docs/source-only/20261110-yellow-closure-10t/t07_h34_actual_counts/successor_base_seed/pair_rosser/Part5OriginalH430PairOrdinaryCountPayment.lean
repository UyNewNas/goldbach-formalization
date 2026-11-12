import ImbalancedChen.Part5OriginalH430PairPhysicalCubeGeometry
import MathlibNt.Wu2008DoubleSieve.PhiMonotone

/-! Four original ordinary pair counts with their signed AP remainders and
their genuine nonnegative upper-polynomial excess. All same-Q refinements
of the predecessor H remain on the original, fixed or moving, query. -/
namespace ImbalancedChen.Part5OriginalH430PairOrdinaryCountPayment
noncomputable section
open Set Real Finset Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2OriginalBankChildPrimeMass P2OriginalPositiveSameQMassLift
open P2OriginalHalfOpenProfileCarrier P2OriginalW2CountTupleReindex
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2ActualMarkedCountState (rootLevel root_level_geometry)
open P2SameQPhysicalRosserSeed (cutoff_log_coordinate)
open P2FrozenReceiverCountActions P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430OriginalRootQBound Part5OriginalH430SeedHistoryMass
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430ImmutableBankProfiles (precedingH)
open P5OriginalFeedbackTableKernels (tableFunction)
open Part5OriginalH430OrdinaryPairCounts (childDiscrepancy)
open Part5OriginalH430OrdinaryPairWalls (actual_half_iff_open)
open Part5OriginalH430SameQCanonicalMains (model physical_main_sides)
open Part5OriginalH430PairPhysicalCubeGeometry (pair_scale)
open P5CanonicalUpperCancellation (upperA upperA_eq_one)
open scoped Classical BigOperators

def window (N : ℕ) (L : ℝ) (j : Fin 36) (k : Fin 4) : Finset (Fin 2 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5)).filter
    (fun x => normalizedLog N L x∈pairHalf (originalW2At j) k)

def signedAP (N : ℕ) (Q : ℝ) (b : ℕ) (z : ℝ) : ℝ :=
  ordinaryRosserRemainder true N b (rootLevel Q b) z

def upperExcess (N : ℕ) (Q : ℝ) (b : ℕ) (z : ℝ) : ℝ :=
  model true N Q b z + signedAP N Q b z - (frozenCount N b (receiver N) z:ℝ)

theorem upperExcess_eq_source_polynomial (N : ℕ) (Q : ℝ) (b : ℕ) (z : ℝ) :
    upperExcess N Q b z =
      (∑ e∈(ordinarySievePrimeProduct (b*N) z).divisors,
        ordinaryRosserWeight true N b (rootLevel Q b) z e*(sourceSequenceCount N b e:ℝ))-
          (frozenCount N b (receiver N) z:ℝ) := by
  rw [ordinaryRosser_density_identity] <;> rfl

def laneExcess (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4) : ℝ :=
  ∑ x∈window N L j k,upperExcess N Q (d*x 0*x 1) (occurrenceCutoff Q d (originalW2At j) k (x 0) (x 1))

def laneAP (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4) : ℝ :=
  ∑ x∈window N L j k,signedAP N Q (d*x 0*x 1) (occurrenceCutoff Q d (originalW2At j) k (x 0) (x 1))

def oldHMass (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4) (g : Fin 430) : ℝ :=
  ∑ x∈window N L j k,thetaAtom N Q (d*x 0*x 1)*
    tableFunction false (precedingH g) (pairProfile (originalW2At j) k (normalizedLog N L x))

theorem owned_child_mass {N n p d : ℕ} {r : Root} {t L : ℝ}
    (hN : 1<N) (hL : 0<L) (hQ : rootQ N n r t p=(d:ℝ)*(N:ℝ)^L) (j : Fin 36) (k : Fin 4) :
    (∑ x∈window N L j k,thetaAtom N (rootQ N n r t p) (d*x 0*x 1))=
      pairChildTheta N (rootQ N n r t p) L d (originalW2At j) k := by
  rw [window,sum_filter]
  unfold pairChildTheta
  apply sum_congr rfl
  intro x hx
  rw [actual_half_iff_open hN hL hQ j k x (fun i =>
    ⟨(mem_actualPrimeBoxTuples_iff.mp hx i).1,(mem_actualPrimeBoxTuples_iff.mp hx i).2.1⟩)]

private theorem mass_thirteen :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r →
      ∀ (l : LevelIndex N n r t p dep) (j : Fin 36) (k : Fin 4),
      let Q := rootQ N n r t p; let d := wordProduct l; let L := wordLevel l
      (∑ x∈window N L j k,thetaAtom N Q (d*x 0*x 1))≤13*thetaAtom N Q d := by
  have hF : frozenResidualFloor≤1 := by
    unfold frozenResidualFloor
    have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])
  obtain ⟨T,hT⟩ := all36_positive_sameQ_pair_lift frozenResidualFloor_pos hF (show (0:ℝ)<1 by norm_num)
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN n r t p dep ht ht' hn hp l j k
  have h4 := (le_max_left 4 T).trans hN
  let Q := rootQ N n r t p; let d := wordProduct l; let L := wordLevel l
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hLp := frozenResidualFloor_pos.trans_le hL.1
  have hθ := thetaAtom_nonneg h4 hd (sameQ_residual_gt_one (by omega) hd hLp hQ)
  change _≤13*thetaAtom N Q d
  rw [owned_child_mass (by omega) hLp hQ j k]
  have h := hT N ((le_max_right _ _).trans hN) Q {d} (fun _ => (1:ℝ)) (fun _ => L)
    (fun _ => j) (fun _ => k) (by simpa using hd) (by simp) (by simpa using hL) (by simpa using hQ)
  simp only [Theta_eq_sum_atoms,sum_singleton,one_mul] at h
  have hag := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hsub := W2PairDomain_subset hag k
  have hi := pairMass_le_45_fourths hsub
  rw [pairMass_eq_original (measurableSet_W2PairDomain _ _) hsub (fun _ hx => (W2PairDomain_geometry hag k hx).2)] at hi
  linarith only [(abs_le.mp h).2,mul_le_mul_of_nonneg_left hi hθ,hθ]

/-- Each old-table term stays at the actual pair profile. The AP polynomial
and the source sieve count in the excess both use the original cutoff. -/
theorem all_good_pair_count_means {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r →
      ∀ (l : LevelIndex N n r t p dep) (j : Fin 36) (k : Fin 4) (g : Fin 430),
      let Q := rootQ N n r t p; let d := wordProduct l; let L := wordLevel l
      0≤laneExcess N Q L d j k ∧
        childDiscrepancy N Q L (actualState N) d j k g+laneExcess N Q L d j k ≤
          laneAP N Q L d j k+oldHMass N Q L d j k g+ε*thetaAtom N Q d := by
  obtain ⟨Ta,h4,ha⟩ := mass_thirteen
  obtain ⟨Tb,_,hb⟩ := physical_main_sides (div_pos frozenResidualFloor_pos (by norm_num : (0:ℝ)<15))
    (div_pos he (by norm_num : (0:ℝ)<13))
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n r t p dep ht ht' hn hp l j k g
  have hNa := (le_max_left Ta Tb).trans hN
  have hNb := (le_max_right Ta Tb).trans hN
  have hN1 : 1<N := by have := h4.trans hNa; omega
  let Q := rootQ N n r t p; let d := wordProduct l; let L := wordLevel l
  let b (x : Fin 2 → ℕ) := d*x 0*x 1
  let z (x : Fin 2 → ℕ) := occurrenceCutoff Q d (originalW2At j) k (x 0) (x 1)
  let s (x : Fin 2 → ℕ) := pairProfile (originalW2At j) k (normalizedLog N L x)
  let H (x : Fin 2 → ℕ) := tableFunction false (precedingH g) (s x)
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hQN := original_root_Q_le_target N n r t p (by omega) ht ht' hp
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have point (x : Fin 2 → ℕ) (hx : x∈window N L j k) :
      0≤upperExcess N Q (b x) (z x) ∧
      ((actualState N).upper (b x) (z x)-thetaAtom N Q (b x)*(upperA (s x)-H x))+
          upperExcess N Q (b x) (z x) ≤
        signedAP N Q (b x) (z x)+thetaAtom N Q (b x)*H x+(ε/13)*thetaAtom N Q (b x) := by
    obtain ⟨hw,hm⟩ := mem_filter.mp hx
    obtain ⟨hbpos,hbN,hR,hc,hz,hmEq,haEq⟩ := pair_scale hN1 hd frozenResidualFloor_pos hL.1 hQ hQN j k x hw hm
    have hh := (hb N hNb hEven Q (cutoff Q (b x) 3) 3 (b x) hbpos hbN hR hc
      (cutoff_log_coordinate hR (by norm_num : (0:ℝ)<3)) (by norm_num) (by norm_num)).1
    rw [upperA_eq_one (by norm_num : (0:ℝ)<3) le_rfl] at hh
    have hfinite := ordinaryRosser_upper_finite (N:=N) (d:=b x)
      (root_level_geometry hR (show (1:ℝ)≤3 by norm_num)).1
      (root_level_geometry hR (show (1:ℝ)≤3 by norm_num)).2
    change (sourceSieveCount N (b x) ((b x)*N) (cutoff Q (b x) 3):ℝ)≤
      model true N Q (b x) (cutoff Q (b x) 3)+signedAP N Q (b x) (cutoff Q (b x) 3) at hfinite
    have hcount : (frozenCount N (b x) (receiver N) (z x):ℝ)≤
          (sourceSieveCount N (b x) ((b x)*N) (cutoff Q (b x) 3):ℝ) := by
      have hfilter : (frozenCount N (b x) (receiver N) (z x):ℝ)≤
          (sourceSieveCount N (b x) ((b x)*N) (z x):ℝ) := by
        simp only [frozenCount,frozenCarrier,Int.cast_natCast,sourceSieveCount]
        exact_mod_cast card_le_card (filter_subset _ _)
      exact hfilter.trans (by exact_mod_cast sourceSieveCount_antitone N (b x) ((b x)*N) hz)
    have hopen := (actual_half_iff_open hN1 (frozenResidualFloor_pos.trans_le hL.1) hQ j k x
      (fun i => ⟨(mem_actualPrimeBoxTuples_iff.mp hw i).1,(mem_actualPrimeBoxTuples_iff.mp hw i).2.1⟩)).mp hm
    have hr := W2PairDomain_profile_bounds hg k hopen
    have hone : upperA (s x)=1 := upperA_eq_one (zero_lt_one.trans hr.1) (hr.2.1.le.trans hr.2.2)
    change model true N Q (b x) (z x)=model true N Q (b x) (cutoff Q (b x) 3) at hmEq
    change signedAP N Q (b x) (z x)=signedAP N Q (b x) (cutoff Q (b x) 3) at haEq
    constructor
    · unfold upperExcess
      rw [hmEq,haEq]
      linarith only [hcount,hfinite]
    · rw [hone]
      change (frozenCount N (b x) (receiver N) (z x):ℝ)-thetaAtom N Q (b x)*(1-H x)+
          (model true N Q (b x) (z x)+signedAP N Q (b x) (z x)-(frozenCount N (b x) (receiver N) (z x):ℝ))≤_
      rw [hmEq]
      linarith only [hh]
  have hdisc : childDiscrepancy N Q L (actualState N) d j k g=
      ∑ x∈window N L j k,((actualState N).upper (b x) (z x)-thetaAtom N Q (b x)*(upperA (s x)-H x)) := by
    unfold childDiscrepancy window
    rw [sum_filter]
  constructor
  · exact sum_nonneg (fun x hx => (point x hx).1)
  · have hsum := sum_le_sum (s:=window N L j k) (fun x hx => (point x hx).2)
    simp only [sum_add_distrib,←mul_sum] at hsum
    have hmass := ha N hNa n r t p dep ht ht' hn hp l j k
    rw [hdisc]
    unfold laneExcess laneAP oldHMass
    linarith only [hsum,mul_le_mul_of_nonneg_left hmass (div_nonneg he.le (by norm_num : (0:ℝ)≤13))]

end
end ImbalancedChen.Part5OriginalH430PairOrdinaryCountPayment
