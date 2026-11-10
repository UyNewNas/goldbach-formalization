import ImbalancedChen.Part5OriginalH430SeedOrdinaryWindows

/-! All three actual negative seed Rosser means pay their ordinary constants
on the true fixed-word subfamilies, leaving their original signed pi-centred
arithmetic packet. -/
namespace ImbalancedChen.Part5OriginalH430SeedThreeNegativeMeans
noncomputable section
open Set Finset Real Wu2008DoubleSieve
open P2EnhancedNegativeChildRosser (windowMean childMean)
open P2EnhancedTwentyOneChildCorrection (negativeMean localNegativeMean)
open P2EnhancedNegativeChildModulusPrimePayment (piCenteredPhysicalError)
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2SeedOmegaLiteralFunctional (negative)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift P2OriginalW2CentreThetaPayment (groupedSigma weighted_fiber_sum)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430BankOrdinarySingletons (ordinaryWindow argument)
open Part5OriginalH430SeedOrdinaryWindows (W lane stop edge coordinates W_eq ordinary_and_child_mass)
open Part5OriginalH430SameQCanonicalMains (physical_main_sides)
open Part5OriginalH430SeedUpperAnchorsAP (scaled_cutoff)
open Part5OriginalH430SeedChildRosserDictionary (true_child_mean_eq_model)
open Part5OriginalH430SignedSeedCount (signedSingles)
open P5CanonicalUpperCancellation (lowerBar)
open scoped Classical BigOperators

private theorem coprime_list {N : ℕ} (xs : List ℕ) (h : ∀ q∈xs,q.Coprime N) : xs.prod.Coprime N := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      exact (h a (by simp)).mul_left (ih (fun q hq => h q (by simp [hq])))

private theorem window_geometry {N n p d q : ℕ} {k : Root} {t : ℝ}
    (hd : 0<d) (hQN : rootQ N n k t p≤(N:ℝ)) (hR : 1<rootQ N n k t p/(d:ℝ))
    (j : Fin 3) (hq : q∈W N (rootQ N n k t p) d j) :
    let Q := rootQ N n k t p; let z := cutoff Q d (227/50)
    let s := argument N Q d q (lane j)
    q.Prime ∧ q.Coprime N ∧ z≤(q:ℝ) ∧ d*q≤N ∧
      1<Q/((d*q:ℕ):ℝ) ∧ s=log (Q/((d*q:ℕ):ℝ))/log z ∧ 2≤s ∧ s≤10 := by
  let Q := rootQ N n k t p
  let R := Q/(d:ℝ)
  let u := log (q:ℝ)/log R
  have hr0 : 0<R := zero_lt_one.trans hR
  have hr := log_pos hR
  obtain ⟨hp,hcop,hlo,hhi⟩ := mem_primeWindow.mp hq
  have hq0 : (0:ℝ)<q := Nat.cast_pos.mpr hp.pos
  have hz : cutoff Q d (227/50)=R^(1/(227/50:ℝ)) := rfl
  have hz' : cutoff Q d (stop j)=R^(1/stop j) := rfl
  have ht := coordinates j
  have hzpos := rpow_pos_of_pos hr0 (1/(227/50:ℝ))
  have hlogl := log_le_log (show 0<cutoff Q d (227/50) from hzpos) hlo
  have hlogh := log_lt_log hq0 hhi
  rw [hz,log_rpow hr0] at hlogl
  rw [hz',log_rpow hr0,←ht.2.2.2.2.1] at hlogh
  have hu0 : 50/227≤u := (le_div_iff₀ hr).mpr (by linarith only [hlogl])
  have hu1 : u<edge j := (div_lt_iff₀ hr).mpr hlogh
  have huB := hu1.trans_le ht.2.2.2.2.2.2
  have hsr : argument N Q d q (lane j)=(227/50)*(1-u) := by
    unfold argument; rw [ht.1]
  have hqR : (q:ℝ)<R := (log_lt_log_iff hq0 hr0).mp (by
    have hx : u<1 := by linarith
    simpa only [one_mul] using (div_lt_iff₀ hr).mp hx)
  have hchild : Q/((d*q:ℕ):ℝ)=R/(q:ℝ) := by
    dsimp only [R]
    rw [Nat.cast_mul,div_div_eq_div_mul]
  have hc : 1<Q/((d*q:ℕ):ℝ) := by rw [hchild]; exact (one_lt_div hq0).mpr hqR
  have hqc : (d*q:ℕ)≤N := by
    have hq' := (lt_div_iff₀ (Nat.cast_pos.mpr (Nat.mul_pos hd hp.pos) : (0:ℝ)<(d*q:ℕ))).mp hc
    have hh : ((d*q:ℕ):ℝ)<Q := by simpa only [one_mul] using hq'
    exact_mod_cast (hh.trans_le hQN).le
  have hh : argument N Q d q (lane j)=log (Q/((d*q:ℕ):ℝ))/log (cutoff Q d (227/50)) := by
    rw [hsr,hchild,hz,log_div hr0.ne' hq0.ne',log_rpow hr0]
    dsimp only [u]
    field_simp [hr.ne'] <;> ring
  exact ⟨hp,hcop,hlo,hqc,hc,hh,by rw [hsr]; linarith,by rw [hsr]; linarith⟩

theorem window_mean_payment {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ (l : LevelIndex N n k t p dep) (j : Fin 3),
        let Q := rootQ N n k t p; let d := wordProduct l
        thetaAtom N Q d*negative (edge j) -
          windowMean N Q d (cutoff Q d (stop j)) ≤ ε*thetaAtom N Q d := by
  obtain ⟨Ta,hTa,ha⟩ := ordinary_and_child_mass (half_pos he)
  obtain ⟨Tb,hTb,hb⟩ := physical_main_sides (div_pos frozenResidualFloor_pos (by norm_num : (0:ℝ)<10))
    (div_pos he (by norm_num : (0:ℝ)<8))
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN hEven n k t p dep ht ht' hn hp l j
  have hNa := (le_max_left _ _).trans hN
  have hNb := (le_max_right _ _).trans hN
  have hN4 := hTa.trans hNa
  have hN1 : 1<N := by omega
  let Q := rootQ N n k t p
  let d := wordProduct l
  let L := wordLevel l
  obtain ⟨hd,hL,hQ,hcut,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hR := sameQ_residual_gt_one hN1 hd (frozenResidualFloor_pos.trans_le hL.1) hQ
  have hQpos : 0<Q := by
    rw [show Q=(d:ℝ)*(N:ℝ)^L from hQ]; positivity
  have hz := scaled_cutoff hN1 frozenResidualFloor_pos hcut
    (by norm_num : (1:ℝ)≤227/50) (by norm_num : (227/50:ℝ)≤10)
  have hQN := Part5OriginalH430OriginalRootQBound.original_root_Q_le_target N n k t p (by omega) ht ht' hp
  have hc := rootHistory_coherent hN1 ht ht' hn (original_band_prime hp)
    (original_band_geometry (by omega) hp) (levelOccurrence_source l).1
  have hcop : d.Coprime N := coprime_list _ (fun q h => (hc.letters q h).2)
  have hpoint (q : ℕ) (hq : q∈W N Q d j) :
      thetaAtom N Q (d*q)*lowerBar (argument N Q d q (lane j)) -
        childMean N Q d q ≤ ε/8*thetaAtom N Q (d*q) := by
    obtain ⟨hpr,hqn,hzq,hdq,hcR,hs,hs2,hs10⟩ := window_geometry hd hQN hR j hq
    have hh := (hb N hNb hEven Q (cutoff Q d (227/50)) (argument N Q d q (lane j)) (d*q)
      (Nat.mul_pos hd hpr.pos) hdq hcR hz hs hs2 hs10).2
    rw [true_child_mean_eq_model k t hd hcop hpr hqn hQpos.le hzq]
    linarith only [hh]
  have hsum := sum_le_sum (s:=W N Q d j) (fun q hq => hpoint q hq)
  rw [sum_sub_distrib,←mul_sum] at hsum
  have hordinary : ordinaryWindow N Q L d (lane j)=
      ∑ q∈W N Q d j,thetaAtom N Q (d*q)*lowerBar (argument N Q d q (lane j)) := by
    rw [ordinaryWindow,W_eq hd hQ j]
  rw [←hordinary] at hsum
  have hmean : (∑ q∈W N Q d j,childMean N Q d q)=windowMean N Q d (cutoff Q d (stop j)) := rfl
  rw [hmean] at hsum
  obtain ⟨hband,hmass⟩ := ha N hNa n k t p dep ht ht' hn hp l j
  linarith only [(abs_le.mp hband).1,hsum,mul_le_mul_of_nonneg_left hmass
    (div_nonneg he.le (by norm_num : (0:ℝ)≤8))]

theorem three_negative_mean_payment {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ B : Finset (LevelIndex N n k t p dep),
        let Q := rootQ N n k t p; let D := B.image wordProduct; let σ := groupedSigma B wordProduct levelMark
        signedSingles N Q D σ ≤ -(piCenteredPhysicalError N Q D σ)+ε*markedTheta B := by
  obtain ⟨T,h4,hT⟩ := window_mean_payment (div_pos he (by norm_num : (0:ℝ)<3))
  refine ⟨T,h4,?_⟩
  intro N hN hEven n k t p dep ht ht' hn hp B
  let Q := rootQ N n k t p
  let D := B.image wordProduct
  let σ := groupedSigma B wordProduct levelMark
  have hlocal (l : LevelIndex N n k t p dep) :
      thetaAtom N Q (wordProduct l)*(negative P2SeedOmegaLiteralFibre.b+
        negative P2SeedOmegaLiteralFibre.a2+negative P2SeedOmegaLiteralFibre.a3)-
        localNegativeMean N Q (wordProduct l)≤ε*thetaAtom N Q (wordProduct l) := by
    have h := hT N hN hEven n k t p dep ht ht' hn hp l
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    let d := wordProduct l
    let θ := thetaAtom N Q d
    change θ*negative (5/11)-windowMean N Q d (cutoff Q d (11/5))≤ε/3*θ at h0
    change θ*negative (10/29)-windowMean N Q d (cutoff Q d (29/10))≤ε/3*θ at h1
    change θ*negative (25/61)-windowMean N Q d (cutoff Q d (61/25))≤ε/3*θ at h2
    change θ*(negative (5/11)+negative (10/29)+negative (25/61))-
      (windowMean N Q d (cutoff Q d (11/5))+windowMean N Q d (cutoff Q d (29/10))+
        windowMean N Q d (cutoff Q d (61/25)))≤ε*θ
    linarith only [h0,h1,h2]
  have hsum := sum_le_sum (s:=B) (fun l hl => mul_le_mul_of_nonneg_left (hlocal l)
    (mark_pos (levelOccurrence l)).le)
  unfold signedSingles negativeMean
  dsimp only
  rw [real_word_theta,weighted_fiber_sum]
  unfold markedTheta
  rw [mul_sum,mul_sum]
  simp only [mul_sub,sum_sub_distrib,mul_assoc,mul_left_comm,mul_comm] at hsum ⊢
  linarith only [hsum]

end
end ImbalancedChen.Part5OriginalH430SeedThreeNegativeMeans
