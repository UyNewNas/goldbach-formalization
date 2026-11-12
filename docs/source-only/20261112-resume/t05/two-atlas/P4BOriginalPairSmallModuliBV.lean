import ImbalancedChen.P4BOriginalPairFibreDictionary
import ImbalancedChen.U9SemiprimeSwitchedPrimeAP

/-! Small moduli in the original two-prime discrepancy. BV is invoked at
the length of the free prime, with the smaller prime fixed and the
least inverse residue varying with the true modulus. -/
namespace ImbalancedChen.P4BOriginalPairSmallModuliBV
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalPairFibreVariation
open P4BOriginalPairFibreDictionary
open P5Z.RoughSquareWeightedBudget (harmonic_Icc_le_logBudget logBudget)
open U9SemiprimeSwitch (residue residue_coprime product_AP_iff)

theorem inverse_rows (N p X : ℕ) (S : Finset ℕ) (c f : ℕ → ℝ)
    (hpN : ∀ d∈S,0<d ∧ N.Coprime d) :
    (∑ d∈S,c d*(∑ j∈chenPrimePrefix X,f j*kernel N d (p*j))) =
      ∑ d∈S.filter (fun d => p.Coprime d),c d*
        finitePrimitiveDiscrepancy (chenPrimePrefix X) f (residue N p d) d := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdpos,hprim⟩ := hpN d hd
  by_cases hp : p.Coprime d
  · rw [if_pos hp,finitePrimitiveDiscrepancy_eq_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hres : Nat.ModEq d (p*j) N ↔ Nat.ModEq d j (residue N p d) := by
      simpa only [hp,true_and] using (product_AP_iff (m:=p) (r:=j) hdpos hprim)
    have hcop : (p*j).Coprime d ↔ j.Coprime d := by simp [Nat.coprime_mul_iff_left,hp]
    simp only [kernel,hres,hcop]
    split_ifs <;> ring
  · rw [if_neg hp]
    have hzero (j : ℕ) : kernel N d (p*j)=0 := by
      have hc : ¬(p*j).Coprime d := fun h => hp (Nat.coprime_mul_iff_left.mp h).1
      have ha : ¬Nat.ModEq d (p*j) N := fun h => hp ((product_AP_iff hdpos hprim).mp h).1
      simp [kernel,ha,hc]
    simp [hzero]

theorem cap_lower {N p : ℕ} (hN : (1:ℝ)≤N) (hp : p∈outer N) :
    Real.sqrt (N:ℝ)≤(cap N p:ℝ) := by
  obtain ⟨hpin,hp2⟩ := Finset.mem_filter.mp hp
  have hpos : (0:ℝ)<p := by exact_mod_cast (mem_chenPrimePrefix.mp hpin).2.pos
  have he : (1:ℝ)≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have hs := Real.sq_sqrt (Nat.cast_nonneg N)
  have hNexp : (N:ℝ)≤Real.exp 1*(N:ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _) he
  have hprod : Real.sqrt (N:ℝ)*(p:ℝ)≤Real.exp 1*(N:ℝ) := by
    rcases le_total (p:ℝ) (Real.sqrt (N:ℝ)) with h|h
    · exact (mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)).trans
        (by nlinarith only [hs,hNexp])
    · exact (mul_le_mul_of_nonneg_right h hpos.le).trans (by simpa [pow_two] using hp2)
  rw [cap,Nat.cast_min,le_min_iff]
  exact ⟨(Real.sqrt_le_left (Nat.cast_nonneg N)).mpr
    (by nlinarith only [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hN)]),
    ((le_div_iff₀ hpos).mpr hprod).trans (Nat.le_ceil _)⟩

theorem modulus_at_cap {N p d : ℕ} (hN : (1:ℝ)≤N) (hp : p∈outer N)
    (hd : (d:ℝ)≤(N:ℝ)^(1/5:ℝ)) : d≤Nat.floor ((cap N p:ℝ)^(9/20:ℝ)) := by
  apply Nat.le_floor
  apply hd.trans
  calc
    _ ≤ (N:ℝ)^((1/2:ℝ)*(9/20)) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = (Real.sqrt (N:ℝ))^(9/20:ℝ) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul (Nat.cast_nonneg N)]
    _ ≤ _ := Real.rpow_le_rpow (Real.sqrt_nonneg _) (cap_lower hN hp) (by norm_num)

theorem cap_sum (N : ℕ) (hN : (1:ℝ)≤N) :
    (∑ p∈outer N,(cap N p:ℝ))≤2*Real.exp 1*(N:ℝ)*(1+Real.log (N:ℝ)) := by
  have he : (1:ℝ)≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have hsub : outer N⊆Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hle,hprime⟩ := mem_chenPrimePrefix.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨hprime.one_le,hle⟩
  have HH := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => show 0≤1/(p:ℝ) by positivity)).trans (harmonic_Icc_le_logBudget N)
  rw [logBudget,max_eq_right hN] at HH
  calc
    _ ≤ ∑ p∈outer N,(2*Real.exp 1*(N:ℝ))*(1/(p:ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpin := Finset.mem_Icc.mp (hsub hp)
      have hp1 : (0:ℝ)<p := by exact_mod_cast (show 0<p from hpin.1)
      have hle : (p:ℝ)≤N := Nat.cast_le.mpr hpin.2
      have hratio : (1:ℝ)≤Real.exp 1*(N:ℝ)/(p:ℝ) := (one_le_div hp1).mpr
        (hle.trans (le_mul_of_one_le_left (Nat.cast_nonneg N) he))
      have hceil := (Nat.ceil_lt_add_one (le_trans zero_le_one hratio)).le
      have hcap : (cap N p:ℝ)≤(Nat.ceil (Real.exp 1*(N:ℝ)/(p:ℝ)):ℝ) :=
        Nat.cast_le.mpr (min_le_right _ _)
      calc
        _ ≤ 2*(Real.exp 1*(N:ℝ)/(p:ℝ)) := by linarith only [hcap,hceil,hratio]
        _ = _ := by ring
    _ = 2*Real.exp 1*(N:ℝ)*(∑ p∈outer N,1/(p:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left HH (by positivity)

private theorem local_bv (A : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p∈outer N,∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ d∈S,0<d ∧ (d:ℝ)≤(N:ℝ)^(1/5:ℝ) ∧ Squarefree d ∧ |c d|≤1 ∧ N.Coprime d) →
      ∀ (swap : Bool) (b kappa s kappa0 : ℝ),0<s →
      |row N S c swap b kappa s kappa0 p| ≤ C*(cap N p:ℝ)/Real.log (N:ℝ)^A := by
  obtain ⟨B,hB,hbv⟩ := P4BPositiveUpperPrimeBV.eventually_profile_log_saving A
  obtain ⟨X0,H⟩ := Filter.eventually_atTop.mp hbv
  refine ⟨7*B*2^A,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (X0^2),eventually_ge_atTop (2:ℕ)] with N hlarge hN
  intro p hp S c hS swap b kappa s kappa0 hs
  let X := cap N p
  let U := S.filter (fun d => p.Coprime d)
  let f := fibre swap b kappa s kappa0 N p
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N from hN)
  have hxl : Real.sqrt (N:ℝ)≤(X:ℝ) := cap_lower hn.le hp
  have hx0 : X0≤X := by
    apply Nat.cast_le.mp
    apply le_trans _ hxl
    exact (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast hlarge)
  have hsqrt := Real.sqrt_pos.2 (zero_lt_one.trans hn)
  have hlogN := Real.log_pos hn
  have hlogX := Real.log_le_log hsqrt hxl
  rw [Real.log_sqrt (Nat.cast_nonneg N)] at hlogX
  have hxpos : 0<Real.log (X:ℝ) := by linarith
  have hUf {d : ℕ} (hd : d∈U) := (Finset.mem_filter.mp hd).1
  have hU : U⊆Finset.Icc 1 (Nat.floor ((X:ℝ)^(9/20:ℝ))) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(hS d (hUf hd)).1,
      modulus_at_cap hn.le hp (hS d (hUf hd)).2.1⟩
  let I : Finset (Fin (X+1)) := Finset.univ
  let g := P4BPositiveUpperPrimeBV.prefixProfile I (fun i => abelCoefficient f X i.val) Fin.val
  have hfg (d : ℕ) := finitePrimitiveDiscrepancy_congr (chenPrimePrefix X) f g (residue N p d) d
    (fun j hj => (abel_on f (mem_chenPrimePrefix.mp hj).1).symm)
  have h := H X hx0 U c hU (fun d hd => (hS d (hUf hd)).2.2.1)
    (fun d hd => (hS d (hUf hd)).2.2.2.1) (residue N p)
    (fun d hd => residue_coprime N (hS d (hUf hd)).1 (Finset.mem_filter.mp hd).2
      (hS d (hUf hd)).2.2.2.2)
    (X+1) I (fun i => abelCoefficient f X i.val) Fin.val
    (fun i _ => Nat.lt_succ_iff.mp i.isLt)
  change |∑ d∈S,c d*(∑ j∈chenPrimePrefix X,f j*kernel N d (p*j))| ≤ _
  rw [inverse_rows N p X S c f (fun d hd => ⟨(hS d hd).1,(hS d hd).2.2.2.2⟩)]
  simp_rw [hfg]
  have hm : (∑ i : Fin (X+1),|abelCoefficient f X i.val|)≤7 := by
    simpa only [show (6+1:ℝ)=7 by norm_num] using
      abel_mass (fibre_control swap b kappa s kappa0 N X p hn hs)
  have hpow : Real.log (N:ℝ)^A≤2^A*Real.log (X:ℝ)^A := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlogN.le (by linarith) A
  calc
    _ ≤ _ := h
    _ ≤ 7*(B*(X:ℝ)/Real.log (X:ℝ)^A) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = (7*B*(X:ℝ))/Real.log (X:ℝ)^A := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (pow_pos hxpos A) (pow_pos hlogN A)).mpr
      have hnum := mul_le_mul_of_nonneg_left hpow (by positivity : 0≤7*B*(X:ℝ))
      convert hnum using 1 <;> ring

/-- Uniform arithmetic estimate for both original ordered slots. The cost
of all fixed-prime fibres is paid before any physical policy is selected. -/
theorem eventually_pair_sum (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ d∈S,0<d ∧ (d:ℝ)≤(N:ℝ)^(1/5:ℝ) ∧ Squarefree d ∧ |c d|≤1 ∧ N.Coprime d) →
      ∀ (b kappa s kappa0 : ℝ),0<s → s≤1 →
      |Part3.primeProductSignedError 2 N N S c
        (P4BOriginalFiniteSignedTrim.trimmedWeight b kappa s kappa0 N)| ≤
        delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  obtain ⟨C,hC,hrow⟩ := local_bv (A+2)
  have hlog : ∀ᶠ N : ℕ in atTop,8*C*Real.exp 1/delta≤Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [hrow,hlog,eventually_one_le_nat_log,eventually_ge_atTop (2:ℕ)] with
    N hn hcost hlogN hN
  intro S c hS b kappa s kappa0 hs hs1
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N from hN)
  let L := Real.log (N:ℝ)
  have hL : 0<L := Real.log_pos hNr
  have H (swap : Bool) :
      |∑ p∈outer N,row N S c swap b kappa s kappa0 p| ≤
        C*(2*Real.exp 1*(N:ℝ)*(1+L))/L^(A+2) := by
    calc
      _ ≤ ∑ p∈outer N,|row N S c swap b kappa s kappa0 p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p∈outer N,C*(cap N p:ℝ)/L^(A+2) :=
        Finset.sum_le_sum (fun p hp => hn p hp S c hS swap b kappa s kappa0 hs)
      _ = C*(∑ p∈outer N,(cap N p:ℝ))/L^(A+2) := by rw [Finset.mul_sum,Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (cap_sum N hNr.le) hC.le)
        (pow_nonneg hL.le _)
  rw [signed_rows hNr hs hs1 S c]
  apply (abs_add_le _ _).trans ((add_le_add (H false) (H true)).trans ?_)
  have h1 : 1+L≤2*L := by dsimp only [L]; linarith only [hlogN]
  have h2 : 8*C*Real.exp 1≤delta*L := by
    simpa only [mul_comm L delta] using (div_le_iff₀ hd).mp hcost
  have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : 0≤(N:ℝ)*L)
  have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : 0≤4*C*Real.exp 1*(N:ℝ))
  have Hnum : 2*(C*(2*Real.exp 1*(N:ℝ)*(1+L))) ≤ delta*(N:ℝ)*L^2 := by
    nlinarith only [h3,h4]
  change _ ≤ delta*(N:ℝ)/L^A
  rw [← add_div,pow_add]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hL A) (pow_pos hL 2)) (pow_pos hL A)).mpr
  convert mul_le_mul_of_nonneg_right Hnum (pow_nonneg hL.le A) using 1 <;> ring

end
end ImbalancedChen.P4BOriginalPairSmallModuliBV
