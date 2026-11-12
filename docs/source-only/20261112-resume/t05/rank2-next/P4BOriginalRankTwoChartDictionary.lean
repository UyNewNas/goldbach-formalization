import ImbalancedChen.P4BOriginalRankTwoConductorWindows

/-! Return the two conductor rectangles to the original, labelled,
independent pair, with the original residue and its exact coprime mean. -/
namespace ImbalancedChen.P4BOriginalRankTwoChartDictionary
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalRankTwoChartScales P4BOriginalRankTwoConductorWindows
open P4BOuterRampRoughness (baseline)
open P5Z.ActualEtaPsiOccurrenceBudget (chi eta psi)
open P5Z.ActualLabelledPrimeSmoothCharts (primeAlphabet primeTuples)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel sourceWord residueKernel_real)
open P5Z.LicensedOriginalIntegerProfile (listExtension listExtension_ofFn integerExtension_eq_on_primes)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart)
open P4BOriginalFiniteSignedTrim (pairLicence)
open P4BLabelledPairDictionary (pairTuple tuplePair geometry)
open P2GammaSmallConductorIntervalBridge (naturalRectangleDiscrepancy)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem alphabet {N p : ℕ} (h : p∈primeAlphabet N) : p≤N ∧ p.Prime :=
  ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp h).1),(Finset.mem_filter.mp h).2⟩

theorem restrict_row {N : ℕ} {V : ℝ} (hV : 0<V) (hcap : 2*V≤N) (F : ℕ → ℂ) :
    (∑ p∈primeAlphabet N,profile V p*F p)=
      ∑ p∈primeSWInterval (V/2) (2*V),primeRow V p*F p := by
  calc
    _ = ∑ p∈Finset.range (N+1),primeRow V p*F p := by
      rw [primeAlphabet,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      rw [row_apply]
      split_ifs <;> simp
    _ = _ := by
      symm
      apply Finset.sum_subset
      · intro p hp
        have hh := (Finset.mem_Ioc.mp hp).2
        apply Finset.mem_range.mpr
        have hN : Nat.floor (2*V)≤N := by simpa using Nat.floor_mono hcap
        omega
      · intro p hp hout
        rw [row_apply]
        by_cases hh : psi ((p:ℝ)/V)=0
        · simp [profile,hh]
        · obtain ⟨hl,hr⟩ := psi_window hV hh
          exact (hout (Finset.mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity : 0≤V/2)).mpr hl,
            Nat.le_floor hr.le⟩)).elim

private theorem head_split (u : ℝ) (hu : 0<u) (F : ℕ → ℂ) :
    (∑ p∈primeSWInterval (u/2) (2*u),F p)=
      (∑ p∈primeSWInterval (u/2) u,F p)+(∑ p∈primeSWInterval u (2*u),F p) := by
  let S := primeSWInterval (u/2) u
  let T := primeSWInterval u (2*u)
  have h1 := Nat.floor_mono (show u/2≤u by linarith)
  have h2 := Nat.floor_mono (show u≤2*u by linarith)
  have he : primeSWInterval (u/2) (2*u)=S∪T := by
    ext p
    simp only [S,T,primeSWInterval,Finset.mem_union,Finset.mem_Ioc]
    omega
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hp).2) (Finset.mem_Ioc.mp hq).1
  rw [he,Finset.sum_union hdis]

theorem eventually_original_rectangles {b kappa kappa0 : ℝ} (hb : 0<b) (hb1 : b<1)
    (hk : 0<kappa) (hk0 : 0<kappa0) :
    ∀ᶠ N : ℕ in atTop,∀ s : ℝ,∀ hs : 0<s,∀ hg : 2*s≤baseline b kappa-19/96,
      ∀ (S : Finset ℕ) (c : ℕ → ℝ),
       (∑ ps∈primeTuples N 2, originalChart (pairLicence hb hs hg N) N kappa0 (labels N) ps*
           wordKernel S (fun d => (c d:ℂ)) N ps)=
       (∑ d∈S,(c d:ℂ)*rectangle true N d)+(∑ d∈S,(c d:ℂ)*rectangle false N d) := by
  filter_upwards [eventually_ge_atTop (2^12:ℕ),eventually_plateau hb hb1 hk hk0] with N hN HP
  intro s hs hg S c
  let L := pairLicence hb hs hg N
  let u := U N
  let A := primeAlphabet N
  have hu := U_pos N
  have hu1 : 1≤u := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hc : 16*u≤(N:ℝ) := by
    have h := (scales hN).2.1
    change 1024*u^2≤(N:ℝ) at h
    nlinarith [sq_nonneg (u-1)]
  let GK := fun (d p j : ℕ) => ((P2OriginalGammaUpperLowRankConsumer.gammaKernel N d (p*j):ℝ):ℂ)
  have hdict (p j : ℕ) (hp : p∈A) (hj : j∈A) :
      originalChart L N kappa0 (labels N) [p,j]=profile u p*profile (8*u) j := by
    change (P5Z.ExactOriginalSmoothDyadicPartition.psi chi ((p:ℝ)/u)*
      (P5Z.ExactOriginalSmoothDyadicPartition.psi chi ((j:ℝ)/P5Z.ExactOriginalSmoothDyadicPartition.R (index N+3))*1))*
      ((eta ((([p,j]:List ℕ).prod:ℝ)/(N:ℝ)^(1-kappa0)):ℂ)*(listExtension L [p,j]:ℂ))=_
    rw [second_scale,mul_one,show ([p,j]:List ℕ).prod=p*j by simp]
    change (profile u p*profile (8*u) j)*((eta (((p*j:ℕ):ℝ)/(N:ℝ)^(1-kappa0)):ℂ)*
      (listExtension L [p,j]:ℂ))=_
    by_cases h₀ : psi ((p:ℝ)/u)=0
    · simp only [profile,h₀,Complex.ofReal_zero,zero_mul]
    by_cases h₁ : psi ((j:ℝ)/(8*u))=0
    · simp only [profile,h₁,Complex.ofReal_zero,mul_zero,zero_mul]
    obtain ⟨ho,hb',hl,hh,heta⟩ := HP p j h₀ h₁
    let t := pairTuple N (p,j) (alphabet hp).1 (alphabet hj).1
    have ht : t∈Part3.labelledPrimeTuples 2 N := P4BOriginalPairFibreDictionary.pair_mem
      (mem_chenPrimePrefix.mpr (alphabet hp)) (mem_chenPrimePrefix.mpr (alphabet hj))
    have hword : sourceWord t=[p,j] := by simp [sourceWord,t,pairTuple,List.ofFn_succ]
    have hmap : P4BOriginalFiniteSmoothCount.weight b kappa s N t=listExtension L [p,j] := by
      rw [← hword,sourceWord,listExtension_ofFn,integerExtension_eq_on_primes L _ (Finset.mem_filter.mp ht).2]
      exact P4BArbitraryWidthUpperPairProfile.original_caller b kappa s (by omega) t ht
    have hgeom : geometry b N (manuscriptHalfProductCutoff kappa N) t := by
      simpa only [geometry,t,P4BLabelledPairDictionary.tuplePair_pairTuple]
        using And.intro ho (And.intro hb' (And.intro hl hh))
    have hT : 0<manuscriptHalfProductCutoff kappa N := by
      unfold manuscriptHalfProductCutoff
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _)
    have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    have hone := P4B.smoothPhysicalPairOuterRamp_eq_one_of_affineRegion hn hs
      ((P4BLabelledLogGeometry.geometry_iff_affineRegion hn hT ht).mp hgeom)
    have hreal : listExtension L [p,j]=1 := hmap.symm.trans hone
    simp only [heta,hreal,Complex.ofReal_one,mul_one]
  have hw (p j : ℕ) : wordKernel S (fun d => (c d:ℂ)) N [p,j]=∑ d∈S,(c d:ℂ)*GK d p j := by
    unfold wordKernel
    apply Finset.sum_congr rfl
    intro d _
    simp only [residueKernel_real,show ([p,j]:List ℕ).prod=p*j by simp,GK,
      P2OriginalGammaUpperLowRankConsumer.gammaKernel]
  let I := primeSWInterval (u/2) (2*u)
  let J := primeSWInterval (4*u) (16*u)
  have hsum (d : ℕ) :
      (∑ p∈A,∑ j∈A,profile u p*profile (8*u) j*GK d p j)=rectangle true N d+rectangle false N d := by
    have hJ (p : ℕ) := restrict_row (N:=N) (V:=8*u) (by positivity)
      (by linarith : 2*(8*u)≤N) (fun j => GK d p j)
    have hscale₁ : 8*u/2=4*u := by ring
    have hscale₂ : 2*(8*u)=16*u := by ring
    let F := fun p => ∑ j∈J,primeRow (8*u) j*GK d p j
    calc
      _ = ∑ p∈A,profile u p*F p := by
        apply Finset.sum_congr rfl
        intro p _
        calc
          _ = profile u p*(∑ j∈A,profile (8*u) j*GK d p j) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
          _ = _ := congrArg (fun z : ℂ => profile u p*z) (by simpa only [hscale₁,hscale₂] using hJ p)
      _ = ∑ p∈I,primeRow u p*F p := restrict_row (by exact hu) (by linarith : 2*u≤N) _
      _ = _ := by
        rw [head_split u hu]
        simp only [F,J,Finset.mul_sum,rectangle,headScale,if_true,Bool.false_eq_true,if_false,
          naturalRectangleDiscrepancy,GK,show 2*(u/2)=u by ring,mul_assoc]
  calc
    _ = ∑ p∈A,∑ j∈A,originalChart L N kappa0 (labels N) [p,j]*
          wordKernel S (fun d => (c d:ℂ)) N [p,j] := by
      change (∑ ps∈P5Z.ExactOriginalSmoothDyadicPartition.words A (1+1),_)=_
      rw [P5Z.ExactOriginalSmoothDyadicPartition.words_sum_cons]
      apply Finset.sum_congr rfl
      intro p _
      rw [P5Z.ExactOriginalSmoothDyadicPartition.words_sum_cons]
      simp [P5Z.ExactOriginalSmoothDyadicPartition.words]
    _ = ∑ p∈A,∑ j∈A,∑ d∈S,(c d:ℂ)*(profile u p*profile (8*u) j*GK d p j) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      rw [hdict p j hp hj,hw,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = ∑ d∈S,(c d:ℂ)*(∑ p∈A,∑ j∈A,profile u p*profile (8*u) j*GK d p j) := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ p∈A,∑ d∈S,∑ j∈A,(c d:ℂ)*(profile u p*profile (8*u) j*GK d p j) :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ = _ := by simp_rw [hsum,mul_add,Finset.sum_add_distrib]

end
end ImbalancedChen.P4BOriginalRankTwoChartDictionary
