import ImbalancedChen.P2Historical246QualifiedStrictBook
import ImbalancedChen.ActualPrimeReciprocalMass

/-! SOURCE ONLY / UNEVALUATED. An explicit rank-zero root and the actual
original W1 row 69 singleton constructor at Q=N^(49/100). A target-N-deleted
prime in a fixed logarithmic interval gives a qualifying tuple; this is
an example causal source, not an identification with the signed manuscript
base or a licence for any H247 endpoint. -/
namespace ImbalancedChen.P2Historical246W1QualifiedWitness
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open Wu2008DoubleSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply
open P2CausalSuccessorOccurrence P2CausalSuccessorTheta
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedLowerPrimeChildMarks P2EnhancedSwitchedTrueNormalization
open P2EnhancedTwentyOneSameQWeighted
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open P2OriginalBankThetaMassLimits P2OriginalBankChildPrimeMass
open P2Historical246QualifiedStrictBook P2Historical246ActualRectangleDebit
open P2Historical246StrictRectangleIntegral P2Historical246StrictDebit
open P2Historical246SuccessorParentWindow P5OriginalActionMassBound

def emptyRootBox : PrimeBox 0 where
  lower := Fin.elim0
  upper := Fin.elim0

def emptyRoot : Mark where
  rootRank := 0
  rank := 0
  box := emptyRootBox
  history := .root
  ceiling := 1
  coefficient := 1

def row69 : SingleRule := .w1 6 9
def row69Choice : SuccessorChoice := .inl row69

theorem root_boxRows : emptyRoot.BoxRows (49/100) (1/100) 0 := by
  norm_num [Mark.BoxRows,emptyRoot,emptyRootBox,History.depth]

theorem row69_domain : W1Domain 6 9 = Ioo (1/5:ℝ) (1/3) := by
  ext x
  norm_num [W1Domain,W1Anchor,W1Target]

/-- Existing target-deleted reciprocal-prime mass provides a genuine
prime in this fixed interval for every sufficiently large N. -/
theorem eventual_deleted_prime : ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N ∧
      (N:ℝ)^(21/200:ℝ) ≤ p ∧ (p:ℝ) < (N:ℝ)^(11/100:ℝ) := by
  have hpos : 0 < Real.log ((11/100:ℝ)/(21/200:ℝ)) := Real.log_pos (by norm_num)
  have ht := tendsto_actualPrimeReciprocalMass
    (a := (21/200:ℝ)) (b := (11/100:ℝ)) (by norm_num) (by norm_num)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN
  have hm := hT N (by omega)
  have hne : (roughPrimeFinset N (Nat.ceil ((N:ℝ)^(11/100:ℝ)))
      ((N:ℝ)^(21/200:ℝ)) ((N:ℝ)^(11/100:ℝ))).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [actualPrimeReciprocalMass,hz] at hm
  obtain ⟨p,hp⟩ := hne
  exact ⟨p,(mem_roughPrimeFinset.mp hp).2⟩

/-- A tuple supplied by the original W1 row is literally in the old
qualifyingSource. No equality of products identifies distinct paths. -/
theorem row69_prime_qualifies {N p : ℕ} (hN : 1 < N) (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hlo : (N:ℝ)^(21/200:ℝ) ≤ p)
    (hhi : (p:ℝ) < (N:ℝ)^(11/100:ℝ)) :
    ∃ t ∈ qualifyingSource emptyRoot row69Choice N (49/100) (19/50) (77/200),
      parentProduct (oldWord t) = p := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by positivity
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos hNR
  have hlowlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hlo
  have hhighlog := Real.log_lt_log (Nat.cast_pos.mpr hp.pos) hhi
  rw [Real.log_rpow hNp] at hlowlog hhighlog
  have hphyslo : (21/200:ℝ) ≤ physicalPrime N p := by
    unfold physicalPrime
    exact (le_div_iff₀ hlog).2 (by nlinarith)
  have hphyshi : physicalPrime N p < (11/100:ℝ) := by
    unfold physicalPrime
    exact (div_lt_iff₀ hlog).2 (by nlinarith)
  have hbhalf : (N:ℝ)^(11/100:ℝ) ≤ (N:ℝ)^(49/100:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNR.le (by norm_num)
  have hbN : (N:ℝ)^(11/100:ℝ) ≤ N := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hNR.le (show (11/100:ℝ) ≤ 1 by norm_num))
  have hpQ : (p:ℝ) < (N:ℝ)^(49/100:ℝ) := hhi.trans_le hbhalf
  have hpNlt : p < N := by exact_mod_cast hhi.trans_le hbN
  let pp : Fin (N+1) := ⟨p,by omega⟩
  let root : Fin 0 → Fin (N+1) := Fin.elim0
  have hword : oldWord root = [] := by simp [oldWord,root]
  have hroot : root ∈ emptyRoot.history.family N ((N:ℝ)^(49/100:ℝ)) emptyRoot.ceiling emptyRoot.box := by
    apply mem_rootFamily.mpr
    intro i
    exact Fin.elim0 i
  have hrelative : relativePrime ((N:ℝ)^(49/100:ℝ)) (oldWord root) pp.val =
      (100/49:ℝ)*physicalPrime N p := by
    simp only [relativePrime,residualLevel,hword,parentProduct,List.prod_nil,Nat.cast_one,div_one,
      pp,physicalPrime,Real.log_rpow hNp]
    field_simp [hlog.ne']
    <;> ring
  have hdomain : singleDomain row69 ((N:ℝ)^(49/100:ℝ)) (oldWord root) pp.val := by
    change relativePrime ((N:ℝ)^(49/100:ℝ)) (oldWord root) pp.val ∈ W1Domain 6 9
    rw [row69_domain,hrelative]
    constructor <;> linarith
  have hQone : (1:ℝ) < (N:ℝ)^(49/100:ℝ) := Real.one_lt_rpow hNR (by norm_num)
  have hparent : parentWindow N ((N:ℝ)^(49/100:ℝ)) (oldWord root) emptyRoot.ceiling := by
    have hQN : (N:ℝ)^(49/100:ℝ) ≤ N := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hNR.le (show (49/100:ℝ) ≤ 1 by norm_num))
    simp [parentWindow,hN,hword,parentProduct,emptyRoot,hQone,hQN]
  have hchild : pp ∈ singleChildren row69 N ((N:ℝ)^(49/100:ℝ)) (oldWord root) emptyRoot.ceiling := by
    apply mem_singleChildren.mpr
    refine ⟨?_,hparent,hdomain,?_,?_⟩
    · simpa [hword,parentProduct,pp] using And.intro hp (hp.coprime_iff_not_dvd.mpr hpN)
    · simpa [emptyRoot,pp] using (show physicalPrime N p < 1 by linarith)
    · simpa [hword,parentProduct,pp] using hpQ
  let t := singleTuple root pp
  have hsource : t ∈ (advance emptyRoot row69Choice).source N (49/100) := by
    change t ∈ (History.single emptyRoot.history row69).family N ((N:ℝ)^(49/100:ℝ))
      emptyRoot.ceiling emptyRoot.box
    exact mem_single_family.mpr ⟨root,hroot,pp,hchild,rfl⟩
  have hprod : parentProduct (oldWord t) = p := by
    rw [oldWord_product]
    change Part3.labelledProduct (singleTuple root pp) = p
    rw [singleTuple_product,(singleWord_history _ _).2.2,hword]
    simp [parentProduct,pp]
  have hL : residualExponent N (parentProduct (oldWord t)) (49/100) =
      (49/100:ℝ)-physicalPrime N p := by
    rw [hprod]
    rfl
  have hchi : (advance emptyRoot row69Choice).history.ceiling
      (advance emptyRoot row69Choice).ceiling t = physicalPrime N p := by
    simp [advance,row69Choice,singleSuccessor,History.ceiling,t,singleTuple,pp]
  refine ⟨t,?_,hprod⟩
  apply Finset.mem_filter.mpr
  refine ⟨hsource,?_⟩
  dsimp only
  rw [hL,hchi]
  constructor
  · constructor <;> linarith
  · nlinarith

/-- Actual qualifying source exists for every large N for this explicit
original row and root; it does not assert that this root is the frozen
signed manuscript base or that the positive profile has a count licence. -/
theorem eventual_row69_qualifying_nonempty : ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    (qualifyingSource emptyRoot row69Choice N (49/100) (19/50) (77/200)).Nonempty := by
  obtain ⟨T,hT,hprime⟩ := eventual_deleted_prime
  refine ⟨T,hT,?_⟩
  intro N hN
  obtain ⟨p,hp,hpN,hlo,hhi⟩ := hprime N hN
  obtain ⟨t,ht,_⟩ := row69_prime_qualifies (by omega) hp hpN hlo hhi
  exact ⟨t,ht⟩

/-- The existing normalization is strictly positive when its actual
same-Q residual exceeds one. No division by a marked total is used. -/
theorem thetaAtom_strictly_positive {N d : ℕ} {Q : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hR : 1 < Q/(d:ℝ)) : 0 < thetaAtom N Q d := by
  have hNpos : 0 < N := by omega
  have hNR : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hli : 0 < logarithmicIntegral N :=
    (div_pos (Nat.cast_pos.mpr hNpos)
      (mul_pos (by norm_num) (Real.log_pos hNR))).trans_le (box_trueLi_lower hN)
  have hden : 0 < (Nat.totient d:ℝ)*Real.log (Q/d) :=
    mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)) (Real.log_pos hR)
  have hs : 0 < wuSingularSeries (d*N) := wuSingularSeries_pos _ (Nat.mul_pos hd hNpos)
  unfold thetaAtom
  positivity

theorem row69_weight : (advance emptyRoot row69Choice).weight = (1/2:ℝ) := by
  norm_num [advance,row69Choice,row69,singleSuccessor,Mark.weight,emptyRoot,
    History.scalar,singleEdgeScalar]

/-- The filtered marked family has a genuinely positive same-Q Theta for
this explicit example root, after the threshold. -/
theorem eventual_example_qualifyingTheta_positive : ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    0 < Theta N ((N:ℝ)^(49/100:ℝ))
      (qualifyingSupport ({()} : Finset Unit) (fun _ => emptyRoot) (fun _ => row69Choice)
        N (49/100) (19/50) (77/200))
      (qualifyingSigma ({()} : Finset Unit) (fun _ => emptyRoot) (fun _ => row69Choice)
        N (49/100) (19/50) (77/200)) := by
  obtain ⟨T,hT,hexists⟩ := eventual_row69_qualifying_nonempty
  refine ⟨T,hT,?_⟩
  intro N hN
  have hN4 : 4 ≤ N := hT.trans hN
  obtain ⟨t,ht⟩ := hexists N hN
  have hpositive (t : Fin (advance emptyRoot row69Choice).rank → Fin (N+1))
      (ht : t ∈ qualifyingSource emptyRoot row69Choice N (49/100) (19/50) (77/200)) :
      0 < (advance emptyRoot row69Choice).weight *
        thetaAtom N ((N:ℝ)^(49/100:ℝ)) (parentProduct (oldWord t)) := by
    have hsrc := (Finset.mem_filter.mp ht).1
    obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level (by omega)
      (show (0:ℝ) < 1/100 by norm_num) emptyRoot row69Choice root_boxRows hsrc
    have hR := sameQ_residual_gt_one (by omega) hd hL hQ
    rw [row69_weight]
    exact mul_pos (by norm_num) (thetaAtom_strictly_positive hN4 hd hR)
  rw [qualifying_Theta_exact]
  simp only [Finset.sum_singleton]
  have hsingle := Finset.single_le_sum
    (fun x hx => (hpositive x hx).le) ht
  exact (hpositive t ht).trans_le hsingle

/-- Conditional on the inherited unevaluated pointwise and book proofs,
the original strict book is strictly positive for this one explicit
actual W1 source. This is not a payment or a bound for all sources. -/
theorem eventual_example_strictBook_positive : ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    0 < strictBook ({()} : Finset Unit) (fun _ => emptyRoot) (fun _ => row69Choice) N (49/100) 0 := by
  obtain ⟨Tp,hTp,hpos⟩ := eventual_example_qualifyingTheta_positive
  obtain ⟨Tb,hTb,hbound⟩ := qualifying_Theta_le_original_strictBook
    (Lmin := (19/50:ℝ)) (Lmax := (77/200:ℝ))
    (eta := (1/100:ℝ)) (by norm_num) (by norm_num) (by norm_num) 0
  refine ⟨max Tp Tb, hTp.trans (le_max_left _ _), ?_⟩
  intro N hN
  have ht := hpos N (by omega)
  have hb := hbound N (by omega) (49/100) (by norm_num) Unit ({()} : Finset Unit)
    (fun _ => emptyRoot) (fun _ => row69Choice) (by simpa using root_boxRows)
  exact (mul_pos (div_pos h52_positive (by norm_num)) ht).trans_le hb

end
end ImbalancedChen.P2Historical246W1QualifiedWitness
