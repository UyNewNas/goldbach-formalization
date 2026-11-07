import ImbalancedChen.P2OriginalCompactThetaMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Arbitrary finite nonnegative sigma at ONE Q. The conclusion is absolute
and remains meaningful when Theta=0. No division by the marked mass is
performed. Prefixes, residuals and action labels may all depend on N.
-/
namespace ImbalancedChen.P2OriginalPositiveSameQMassLift

noncomputable section
open MeasureTheory Filter Set
open P5OriginalActionMassBound P2OriginalChildPhysicalNormalization
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalCompactThetaMass
open Wu2008DoubleSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical BigOperators Topology

/-- Finite positive lifting has no nonzero-total-mass premise. -/
theorem finite_nonnegative_absolute_lift {ι : Type*} (S : Finset ι)
    (w mass limit : ι → ℝ) {epsilon : ℝ}
    (hw : ∀i∈S,0≤w i) (herror : ∀i∈S,|mass i-limit i|≤epsilon) :
    |(∑i∈S,w i*mass i)-(∑i∈S,w i*limit i)|≤epsilon*(∑i∈S,w i) := by
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub,abs_mul,abs_of_nonneg (hw i hi)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (herror i hi) (hw i hi)

theorem thetaAtom_nonneg {N d : ℕ} {Q : ℝ}
    (hN : 4≤N) (hd : 0<d) (hR : 1<Q/(d:ℝ)) : 0≤thetaAtom N Q d := by
  have hNpos : 0<N := by omega
  have hNR : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hli : 0<logarithmicIntegral N :=
    (div_pos (Nat.cast_pos.mpr hNpos)
      (mul_pos (by norm_num) (Real.log_pos hNR))).trans_le (box_trueLi_lower hN)
  have hden : 0<(Nat.totient d:ℝ)*Real.log (Q/d) :=
    mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)) (Real.log_pos hR)
  have hs : 0<wuSingularSeries (d*N) := wuSingularSeries_pos _ (Nat.mul_pos hd hNpos)
  unfold thetaAtom
  positivity

theorem sameQ_residual_gt_one {N d : ℕ} {Q L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hQ : Q=(d:ℝ)*(N:ℝ)^L) :
    1<Q/(d:ℝ) := by
  have he : Q/(d:ℝ)=(N:ℝ)^L := by
    rw [hQ]
    field_simp [(Nat.cast_pos.mpr hd).ne']
  rw [he]
  exact Real.one_lt_rpow (by exact_mod_cast hN) hL

/-- The actual moving residual is an admissible assignment to the
uniform theorem. This identity does not choose a threshold after L. -/
def residualExponent (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  Real.log (Q/(d:ℝ))/Real.log (N:ℝ)

theorem sameQ_eq_residualExponent {N d : ℕ} {Q : ℝ}
    (hN : 1<N) (hd : 0<d) (hR : 0<Q/(d:ℝ)) :
    Q=(d:ℝ)*(N:ℝ)^(residualExponent N Q d) := by
  have hNR : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (N:ℝ)^(residualExponent N Q d)=Q/(d:ℝ) := by
    apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hNR) hR).mp
    exact div_mul_cancel₀ _ (Real.log_pos hNR).ne'
  rw [hp]
  field_simp [(Nat.cast_pos.mpr hd).ne']

theorem residualExponent_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1<N) (hd : 0<d) (hQ : Q=(d:ℝ)*(N:ℝ)^L) :
    residualExponent N Q d=L := by
  have hNR : (1:ℝ)<N := by exact_mod_cast hN
  have he : Q/(d:ℝ)=(N:ℝ)^L := by
    rw [hQ]
    field_simp [(Nat.cast_pos.mpr hd).ne']
  rw [residualExponent,he,Real.log_rpow (zero_lt_one.trans hNR)]
  exact mul_div_cancel_right₀ L (Real.log_pos hNR).ne'

/-- Literal singleton children at the common Q. -/
def singleChildTheta (N : ℕ) (Q L : ℝ) (d : ℕ) (lo hi : ℝ) : ℝ :=
  ∑p∈actualPrimeBoxTuples N (fun _ : Fin 1 => L/10) (fun _ => 3*L/5),
    if L⁻¹ • actualPrimeTupleLog N p∈singleDomain lo hi then thetaAtom N Q (d*p 0) else 0

/-- Literal ordered pair children; fresh/repeated lanes remain in the
existing exact physical normalization and are not redefined here. -/
def pairChildTheta (N : ℕ) (Q L : ℝ) (d : ℕ) (a : W2Parameters) (k : Fin 4) : ℝ :=
  ∑p∈actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
    if L⁻¹ • actualPrimeTupleLog N p∈W2PairDomain a k then thetaAtom N Q (d*p 0*p 1) else 0

theorem singleChildTheta_eq {N d : ℕ} {Q L lo hi : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (hhi : hi≤1/2)
    (hA : 4≤(N:ℝ)^(L/10)) (hQ : Q=(d:ℝ)*(N:ℝ)^L) :
    singleChildTheta N Q L d lo hi=thetaAtom N Q d*trueSingleMass N L d lo hi := by
  rw [hQ]
  exact trueSingleMass_is_child_Theta hN hd hL hhi hA

theorem pairChildTheta_eq {N d : ℕ} {Q L : ℝ}
    (hN : 1<N) (hd : 0<d) (hL : 0<L) (a : W2Parameters) (ha : W2Geometry a)
    (k : Fin 4) (hA : 4≤(N:ℝ)^(L/10)) (hQ : Q=(d:ℝ)*(N:ℝ)^L) :
    pairChildTheta N Q L d a k=thetaAtom N Q d*truePairMass N L d a k := by
  rw [hQ]
  exact truePairMass_is_child_Theta hN hd hL a ha k hA

/-- The actual manuscript normalizer is the total positive weight. -/
theorem finite_positive_theta_error {N : ℕ} (hN : 4≤N) (Q : ℝ)
    (D : Finset ℕ) (sigma mass limit : ℕ → ℝ) {epsilon : ℝ}
    (hd : ∀d∈D,0<d) (hsigma : ∀d∈D,0≤sigma d) (hR : ∀d∈D,1<Q/(d:ℝ))
    (herror : ∀d∈D,|mass d-limit d|≤epsilon) :
    |(∑d∈D,sigma d*thetaAtom N Q d*mass d)-
      (∑d∈D,sigma d*thetaAtom N Q d*limit d)| ≤
      epsilon*P2EnhancedTwentyOneSameQWeighted.Theta N Q D sigma := by
  rw [Theta_eq_sum_atoms]
  exact finite_nonnegative_absolute_lift D (fun d => sigma d*thetaAtom N Q d) mass limit
    (fun d hdD => mul_nonneg (hsigma d hdD) (thetaAtom_nonneg hN (hd d hdD) (hR d hdD)))
    herror

/-- Threshold precedes every finite family, every nonnegative sigma,
the common Q, and every moving residual/action assignment. -/
theorem all70_positive_sameQ_single_lift {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀Q : ℝ,∀D : Finset ℕ,∀sigma L : ℕ → ℝ,
      ∀i : ℕ → Fin 7,∀j : ℕ → Fin 10,
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) → (∀d∈D,L d∈Icc Lmin Lmax) →
      (∀d∈D,Q=(d:ℝ)*(N:ℝ)^(L d)) →
      |(∑d∈D,sigma d*singleChildTheta N Q (L d) d (1/W1Anchor (j d)) (1/W1Target (i d)))-
        (∑d∈D,sigma d*thetaAtom N Q d*(∫u in W1Domain (i d) (j d),1/(u*(1-u))))| ≤
        epsilon*P2EnhancedTwentyOneSameQWeighted.Theta N Q D sigma := by
  obtain ⟨Tm,hTm⟩ := all70_compact_uniform_single_mass hmin hmax hepsilon
  obtain ⟨Ta,hTa⟩ := compact_multiplier_error (k:=1) hmin hmax (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)<1)
  refine ⟨max 4 (max Tm Ta),?_⟩
  intro N hN Q D sigma L i j hd hsigma hL hQ
  have hN4 : 4≤N := by omega
  have hN1 : 1<N := by omega
  have hR (d : ℕ) (hdD : d∈D) : 1<Q/(d:ℝ) :=
    sameQ_residual_gt_one hN1 (hd d hdD) (hmin.trans_le (hL d hdD).1) (hQ d hdD)
  have heq : (∑d∈D,sigma d*singleChildTheta N Q (L d) d (1/W1Anchor (j d)) (1/W1Target (i d)))=
      ∑d∈D,sigma d*thetaAtom N Q d*
        trueSingleMass N (L d) d (1/W1Anchor (j d)) (1/W1Target (i d)) := by
    apply Finset.sum_congr rfl
    intro d hdD
    have hhi : 1/W1Target (i d)≤(1/2:ℝ) := by
      apply one_div_le_one_div_of_le (by norm_num)
      unfold W1Target
      linarith [show (0:ℝ)≤(i d).val from Nat.cast_nonneg _]
    rw [singleChildTheta_eq hN1 (hd d hdD) (hmin.trans_le (hL d hdD).1) hhi
      (hTa N (by omega) (L d) (hL d hdD)).1 (hQ d hdD)]
    ring
  rw [heq]
  exact finite_positive_theta_error hN4 Q D sigma _ _ hd hsigma hR
    (fun d hdD => (hTm N (by omega) (L d) (hL d hdD) d (i d) (j d)).le)

theorem all36_positive_sameQ_pair_lift {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀Q : ℝ,∀D : Finset ℕ,∀sigma L : ℕ → ℝ,
      ∀j : ℕ → Fin 36,∀k : ℕ → Fin 4,
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) → (∀d∈D,L d∈Icc Lmin Lmax) →
      (∀d∈D,Q=(d:ℝ)*(N:ℝ)^(L d)) →
      |(∑d∈D,sigma d*pairChildTheta N Q (L d) d (originalW2At (j d)) (k d))-
        (∑d∈D,sigma d*thetaAtom N Q d*
          (∫x in W2PairDomain (originalW2At (j d)) (k d),1/(x 0*x 1*(1-x 0-x 1))))| ≤
        epsilon*P2EnhancedTwentyOneSameQWeighted.Theta N Q D sigma := by
  obtain ⟨Tm,hTm⟩ := all36_compact_uniform_pair_mass hmin hmax hepsilon
  obtain ⟨Ta,hTa⟩ := compact_multiplier_error (k:=2) hmin hmax (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)<1)
  refine ⟨max 4 (max Tm Ta),?_⟩
  intro N hN Q D sigma L j k hd hsigma hL hQ
  have hN4 : 4≤N := by omega
  have hN1 : 1<N := by omega
  have hR (d : ℕ) (hdD : d∈D) : 1<Q/(d:ℝ) :=
    sameQ_residual_gt_one hN1 (hd d hdD) (hmin.trans_le (hL d hdD).1) (hQ d hdD)
  have heq : (∑d∈D,sigma d*pairChildTheta N Q (L d) d (originalW2At (j d)) (k d))=
      ∑d∈D,sigma d*thetaAtom N Q d*truePairMass N (L d) d (originalW2At (j d)) (k d) := by
    apply Finset.sum_congr rfl
    intro d hdD
    rw [pairChildTheta_eq hN1 (hd d hdD) (hmin.trans_le (hL d hdD).1)
      (originalW2At (j d)) (originalRepairedW2Bank_geometry _ (originalW2At_mem (j d)))
      (k d) (hTa N (by omega) (L d) (hL d hdD)).1 (hQ d hdD)]
    ring
  rw [heq]
  exact finite_positive_theta_error hN4 Q D sigma _ _ hd hsigma hR
    (fun d hdD => (hTm N (by omega) (L d) (hL d hdD) d (j d) (k d)).le)

theorem all36_positive_sameQ_singleton_lift {Lmin Lmax epsilon : ℝ}
    (hmin : 0<Lmin) (hmax : Lmin≤Lmax) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀Q : ℝ,∀D : Finset ℕ,∀sigma L : ℕ → ℝ,
      ∀j : ℕ → Fin 36,∀k : ℕ → Fin 3,
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) → (∀d∈D,L d∈Icc Lmin Lmax) →
      (∀d∈D,Q=(d:ℝ)*(N:ℝ)^(L d)) →
      |(∑d∈D,sigma d*singleChildTheta N Q (L d) d
          (a0 (originalW2At (j d))) (singletonTop (originalW2At (j d)) (k d)))-
        (∑d∈D,sigma d*thetaAtom N Q d*
          (∫u in W2SingletonDomain (originalW2At (j d)) (k d),1/(u*(1-u))))| ≤
        epsilon*P2EnhancedTwentyOneSameQWeighted.Theta N Q D sigma := by
  obtain ⟨Tm,hTm⟩ := all36_compact_uniform_singleton_mass hmin hmax hepsilon
  obtain ⟨Ta,hTa⟩ := compact_multiplier_error (k:=1) hmin hmax (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)<1)
  refine ⟨max 4 (max Tm Ta),?_⟩
  intro N hN Q D sigma L j k hd hsigma hL hQ
  have hN4 : 4≤N := by omega
  have hN1 : 1<N := by omega
  have hR (d : ℕ) (hdD : d∈D) : 1<Q/(d:ℝ) :=
    sameQ_residual_gt_one hN1 (hd d hdD) (hmin.trans_le (hL d hdD).1) (hQ d hdD)
  have heq : (∑d∈D,sigma d*singleChildTheta N Q (L d) d
        (a0 (originalW2At (j d))) (singletonTop (originalW2At (j d)) (k d)))=
      ∑d∈D,sigma d*thetaAtom N Q d*trueSingleMass N (L d) d
        (a0 (originalW2At (j d))) (singletonTop (originalW2At (j d)) (k d)) := by
    apply Finset.sum_congr rfl
    intro d hdD
    have hhi : singletonTop (originalW2At (j d)) (k d)≤(1/2:ℝ) := by
      rcases originalRepairedW2Bank_geometry _ (originalW2At_mem (j d)) with
        ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
      have htop (kk : Fin 3) : singletonTop (originalW2At (j d)) kk≤(1/2:ℝ) := by
        fin_cases kk <;> simp only [singletonTop,Matrix.cons_val_zero,Matrix.cons_val_one,
          Matrix.cons_val_two] <;> linarith
      exact htop (k d)
    rw [singleChildTheta_eq hN1 (hd d hdD) (hmin.trans_le (hL d hdD).1) hhi
      (hTa N (by omega) (L d) (hL d hdD)).1 (hQ d hdD)]
    ring
  rw [heq]
  exact finite_positive_theta_error hN4 Q D sigma _ _ hd hsigma hR
    (fun d hdD => (hTm N (by omega) (L d) (hL d hdD) d (j d) (k d)).le)

/-- Zero marked mass forces exact equality in the absolute formulation;
there is no hidden 0/0 branch or positivity premise on the total. -/
theorem zero_mass_absolute {A B epsilon Theta : ℝ}
    (h : |A-B|≤epsilon*Theta) (hzero : Theta=0) : A=B := by
  rw [hzero,mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

end
end ImbalancedChen.P2OriginalPositiveSameQMassLift
