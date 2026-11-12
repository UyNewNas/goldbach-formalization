import ImbalancedChen.P4AFiniteFallbackLowRankRho
import ImbalancedChen.P4BPositiveUpperPrimeBV

/-! SOURCE_ONLY / UNCOMPILED.
Local-x support for the COMPLETE beta-expanded low-rank rectangles and
the same actual rho, then a direct instance of the EXISTING classical
PRIME BV source. It controls genuine finite prime-prefix profiles with
moving primitive residues. It is not a generalized BV theorem for an
arbitrary smooth W or prime-product convolution source.
-/
namespace ImbalancedChen.P4AFiniteFallbackLowRankLocalBV
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P4AFiniteFallbackLowRankBoxes P4AFiniteFallbackLowRankRho
open P4BPositiveUpperPrimeBV (prefixProfile)

theorem local_short_support {N Q : ℕ} {x zeta : ℝ} (hx : 1<x)
    (hz : 0≤zeta) (hz' : zeta≤1/400)
    (hlo : x^(1-zeta)≤(N : ℝ)) (hhi : (N : ℝ)≤x^(1+zeta))
    (hQ : (Q : ℝ)<(N : ℝ)^(2/5 : ℝ)) :
    (Q : ℝ)<x^(9/20 : ℝ) ∧ (Q : ℝ)<x^(1/2-zeta) := by
  have hx0 := zero_lt_one.trans hx
  have hNpos : (0 : ℝ)<N := (Real.rpow_pos_of_pos hx0 _).trans_le hlo
  have hsmall : (N : ℝ)^(2/5 : ℝ)<x^(9/20 : ℝ) := by
    calc
      (N : ℝ)^(2/5 : ℝ) ≤ (x^(1+zeta))^(2/5 : ℝ) :=
        Real.rpow_le_rpow hNpos.le hhi (by norm_num)
      _ = x^((1+zeta)*(2/5 : ℝ)) := (Real.rpow_mul hx0.le _ _).symm
      _ < _ := (Real.rpow_lt_rpow_left_iff hx).mpr (by linarith)
  have hb := hQ.trans hsmall
  refine ⟨hb,hb.trans_le ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)

/-- Every ordered tuple of the cropped rectangle, including collisions,
and either nonzero actual beta weight has the same local-x short cap.
No tuple chooses a partition or changes its original repeated-label
factorial. The local scale and zeta precede the entire rectangle. -/
theorem whole_rectangle_local {N : ℕ} (hN : 1<N) (omega tau ell : ℝ)
    (hell : ell<1/1000) (J : List ℕ) (hJ : J.length≤2) (ps : List ℕ)
    (hps : ps∈slots N omega tau J) (b : ℕ)
    (hb : actualSmallRosserPlus N N ((N : ℝ)^omega) ((N : ℝ)^ell) b≠0 ∨
      actualSmallRosserMinus N N ((N : ℝ)^omega) ((N : ℝ)^ell) b≠0)
    {x zeta : ℝ} (hx : 1<x) (hz : 0≤zeta) (hz' : zeta≤1/400)
    (hlo : x^(1-zeta)≤(N : ℝ)) (hhi : (N : ℝ)≤x^(1+zeta)) :
    (b : ℝ)<(N : ℝ)^ell ∧ Nat.Coprime (b*ps.prod) N ∧
      ((b*ps.prod : ℕ) : ℝ)<x^(9/20 : ℝ) ∧ ((b*ps.prod : ℕ) : ℝ)<x^(1/2-zeta) := by
  have H := whole_rectangle_beta_bound hN omega tau ell hell J hJ ps hps b hb
  exact ⟨H.1,H.2.1,local_short_support hx hz hz' hlo hhi H.2.2⟩

theorem actual_low_local_subset (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N X : ℕ) (hN : 1<N) (hX : 1<X) (tau ell zeta : ℝ) (hell : ell<1/1000)
    (hz : 0≤zeta) (hz' : zeta≤1/400)
    (hlo : (X : ℝ)^(1-zeta)≤N) (hhi : (N : ℝ)≤(X : ℝ)^(1+zeta)) :
    activeLow m r n e q a omega N tau ell⊆Finset.Icc 1 (Nat.floor ((X : ℝ)^(9/20 : ℝ))) := by
  intro Q hQ
  have hpos : 0<Q := Nat.pos_of_ne_zero (activeLow_squarefree m r n e q a omega N tau ell hQ).ne_zero
  have hXr : (1 : ℝ)<X := by exact_mod_cast hX
  have hb := (local_short_support hXr hz hz' hlo hhi (activeLow_power m r n e q a omega N hN tau ell hell hQ)).1
  exact Finset.mem_Icc.mpr ⟨hpos,Nat.le_floor hb.le⟩

/-- The classical BV threshold is chosen before ALL finite bank, history,
mesh, local-N, beta, interval-endpoint and primitive-residue choices.
The original squarefree support and the exact same rho are used.
-/
theorem actual_low_prime_profiles (A : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ),1<N →
      ∀ tau ell zeta : ℝ,ell<1/1000 → 0≤zeta → zeta≤1/400 →
      (X : ℝ)^(1-zeta)≤N → (N : ℝ)≤(X : ℝ)^(1+zeta) →
      ∀ res : ℕ→ℕ,(∀ Q∈activeLow m r n e q a omega N tau ell,(res Q).Coprime Q) →
      ∀ (k : ℕ) (I : Finset (Fin k)) (c : Fin k→ℝ) (Y : Fin k→ℕ),
      (∀ i∈I,Y i≤X) →
      |∑ Q∈activeLow m r n e q a omega N tau ell,
        actualRho m r n e q a omega N tau ell Q*
          finitePrimitiveDiscrepancy (chenPrimePrefix X) (prefixProfile I c Y) (res Q) Q|≤
        (∑ i∈I,|c i|)*(C*(X : ℝ)/Real.log (X : ℝ)^A) := by
  obtain ⟨C,hC,hBV⟩ := P4BPositiveUpperPrimeBV.eventually_profile_log_saving A
  refine ⟨C,hC,?_⟩
  filter_upwards [hBV,eventually_ge_atTop (2 : ℕ)] with X hBVX hX
  intro m r n e q a omega N hN tau ell zeta hell hz hz' hlo hhi res hres k I c Y hY
  exact hBVX (activeLow m r n e q a omega N tau ell) (actualRho m r n e q a omega N tau ell)
    (actual_low_local_subset m r n e q a omega N X hN (by omega : 1<X) tau ell zeta hell hz hz' hlo hhi)
    (fun Q hQ => activeLow_squarefree m r n e q a omega N tau ell hQ)
    (fun Q _ => actualRho_abs_le_one m r n e q a omega N tau ell Q)
    res hres k I c Y hY

/-- In particular the target-deleted original carrier supplies its OWN
primitive target residue. No caller coprimality or distribution premise
is needed. Finite prefix profiles include a complete original interval
as its two endpoint prefixes, with the exact primitive coprime mean.
-/
theorem actual_low_target_prime_profiles (A : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ),1<N →
      ∀ tau ell zeta : ℝ,ell<1/1000 → 0≤zeta → zeta≤1/400 →
      (X : ℝ)^(1-zeta)≤N → (N : ℝ)≤(X : ℝ)^(1+zeta) →
      ∀ (k : ℕ) (I : Finset (Fin k)) (c : Fin k→ℝ) (Y : Fin k→ℕ),
      (∀ i∈I,Y i≤X) →
      |∑ Q∈activeLow m r n e q a omega N tau ell,
        actualRho m r n e q a omega N tau ell Q*
          finitePrimitiveDiscrepancy (chenPrimePrefix X) (prefixProfile I c Y) N Q|≤
        (∑ i∈I,|c i|)*(C*(X : ℝ)/Real.log (X : ℝ)^A) := by
  obtain ⟨C,hC,hBV⟩ := actual_low_prime_profiles A
  refine ⟨C,hC,?_⟩
  filter_upwards [hBV] with X hX
  intro m r n e q a omega N hN tau ell zeta hell hz hz' hlo hhi k I c Y hY
  exact hX m r n e q a omega N hN tau ell zeta hell hz hz' hlo hhi (fun _ => N)
    (fun Q hQ => activeLow_target_coprime m r n e q a omega N tau ell hQ) k I c Y hY

/-- Exact left-open/right-closed prime interval, with BOTH endpoints
chosen after the common BV threshold. This is the two-prefix instance,
not an estimate at a representative endpoint of the interval. -/
theorem actual_low_target_prime_intervals (A : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ),1<N →
      ∀ tau ell zeta : ℝ,ell<1/1000 → 0≤zeta → zeta≤1/400 →
      (X : ℝ)^(1-zeta)≤N → (N : ℝ)≤(X : ℝ)^(1+zeta) →
      ∀ L U : ℕ,L≤U → U≤X →
      |∑ Q∈activeLow m r n e q a omega N tau ell,
        actualRho m r n e q a omega N tau ell Q*
          finitePrimitiveDiscrepancy (chenPrimePrefix X)
            (fun p => if L<p ∧ p≤U then (1 : ℝ) else 0) N Q|≤
        2*(C*(X : ℝ)/Real.log (X : ℝ)^A) := by
  obtain ⟨C,hC,hBV⟩ := actual_low_target_prime_profiles A
  refine ⟨C,hC,?_⟩
  filter_upwards [hBV] with X hX
  intro m r n e q a omega N hN tau ell zeta hell hz hz' hlo hhi L U hLU hUX
  have hp : prefixProfile (Finset.univ : Finset (Fin 2)) ![(1 : ℝ),-1] ![U,L]=
      (fun p => if L<p ∧ p≤U then (1 : ℝ) else 0) := by
    funext p
    by_cases hL : p≤L
    · have hU : p≤U := hL.trans hLU
      simp [P4BPositiveUpperPrimeBV.prefixProfile,Fin.sum_univ_two,hL,hU,not_lt.mpr hL]
    · have hLp : L<p := by omega
      by_cases hU : p≤U <;>
        simp [P4BPositiveUpperPrimeBV.prefixProfile,Fin.sum_univ_two,hL,hLp,hU]
  have h := hX m r n e q a omega N hN tau ell zeta hell hz hz' hlo hhi
    2 Finset.univ ![(1 : ℝ),-1] ![U,L] (by
      intro i _
      fin_cases i <;> simp <;> omega)
  simpa only [hp,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    abs_one,abs_neg,one_add_one_eq_two] using h

end
end ImbalancedChen.P4AFiniteFallbackLowRankLocalBV
