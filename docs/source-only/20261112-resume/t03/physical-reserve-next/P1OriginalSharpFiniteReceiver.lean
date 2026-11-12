import ImbalancedChen.P4BPositiveUpperPrimeBV
import ImbalancedChen.P4AOriginalFull87SharpFrozenLog4
import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import ImbalancedChen.P5zElevenErrorTransport
import ImbalancedChen.CurrentChenInitialSource

/-! The true target-deleted prime receiver on one finite physical
coefficient. The low complete-modulus saving is uniform in the
coefficient and comes from the pinned prime Bombieri--Vinogradov theorem. -/
namespace ImbalancedChen.P1OriginalSharpFiniteReceiver
noncomputable section
open Filter
open scoped Classical BigOperators Topology
open P4AOriginalFull87EighthPrimeMeanLedger (primeMass densityTest receiverTest centrePrimeTerm_nonneg)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError receiver_eq_sharp_density_minus_centre)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87CentrePrimeFibres (weighted_centre_fibre_sum)
open P4AOriginalFull87CentreCoprimeDivisors (centreCoprimeDivisorBudget finite_coprime_fibre_bound)
open P4AOriginalFull87CentreFrozenHN (frozenHN frozenHN_pos tendsto_original87_centre_budget_div_frozenHN_zero)
open P4BPositiveUpperPrimeBV (primeError eventually_primeError_log_saving belowHalfCap_le_target)

abbrev cut (N : ℕ) := Nat.floor ((N:ℝ)^(9/20:ℝ))
def read (Q : Finset ℕ) (c G : ℕ→ℝ) : ℝ := ∑ d∈Q,c d*G d

/-- The receiver integers are the original target-deleted shifts. -/
def literal (N : ℕ) (Q : Finset ℕ) (c : ℕ→ℝ) : ℝ :=
  ∑ x∈chenPrimeReceiverSource N,∑ d∈Q.filter (fun d => d∣x),c d

/-- The strict endpoint in the real upper cutoff includes every active
integer, also when N^.599 is itself an integer. -/
def middle (N : ℕ) (Q : Finset ℕ) (c : ℕ→ℝ) : ℝ :=
  ∑ d∈Q.filter (fun d => cut N<d ∧ (d:ℝ)<(N:ℝ)^(599/1000:ℝ)),c d*sharpPrimeError N d

theorem same_normalization (N : ℕ) : singularNormalization N=frozenHN N := by
  rw [singularNormalization,frozenHN,currentChen_singularSeries_eq_liuSingularSeries]

theorem literal_eq (N : ℕ) (Q : Finset ℕ) (c : ℕ→ℝ) : literal N Q c=read Q c (receiverTest N) := by
  unfold literal read receiverTest
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_comm]

theorem read_density (Q : Finset ℕ) (c : ℕ→ℝ) :
    read Q c densityTest=physicalDensitySum Q c := by
  simp only [read,densityTest,physicalDensitySum,mul_one_div]

private theorem recenter (N : ℕ) (Q : Finset ℕ) (c : ℕ→ℝ) :
    literal N Q c-primeMass N*read Q c densityTest=
      read Q c (sharpPrimeError N)-read Q c (chenCentrePrimeAPCount N N) := by
  rw [literal_eq]
  unfold read
  rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [receiver_eq_sharp_density_minus_centre]
  ring

private theorem centre_paid (N : ℕ) (Q : Finset ℕ) (c : ℕ→ℝ) (hN : ¬N.Prime)
    (hcop : ∀d∈Q,d.Coprime N) (hc : ∀d∈Q,|c d|≤1) :
    |read Q c (chenCentrePrimeAPCount N N)|≤centreCoprimeDivisorBudget N := by
  calc
    _ ≤ ∑ d∈Q,|c d*chenCentrePrimeAPCount N N d| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d∈Q,|c d|*chenCentrePrimeAPCount N N d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [abs_mul,abs_of_nonneg (centrePrimeTerm_nonneg N d)]
    _ ≤ _ := by
      rw [weighted_centre_fibre_sum]
      exact finite_coprime_fibre_bound N hN Q c hcop (fun d hd => (hc d hd).trans (by norm_num))

private theorem low_part (N : ℕ) (Q : Finset ℕ) (c : ℕ→ℝ) :
    read Q c (sharpPrimeError N)-read Q c (highQTest (cut N) (sharpPrimeError N))=
      read (Q.filter (fun d => d≤cut N)) c (sharpPrimeError N) := by
  unfold read
  rw [Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : d≤cut N
  · simp only [highQTest,if_pos h,if_neg (not_lt.mpr h),mul_zero,sub_zero]
  · simp only [highQTest,if_neg h,if_pos (lt_of_not_ge h),sub_self]

theorem eventual_receiver (u : ℝ) (hu : 0<u) :
    ∀ᶠ N : ℕ in atTop,Even N → ∀ (Q : Finset ℕ) (c : ℕ→ℝ),
    (∀d∈Q,Squarefree d ∧ d.Coprime N ∧ |c d|≤1) →
      |literal N Q c-primeMass N*read Q c densityTest-read Q c (highQTest (cut N) (sharpPrimeError N))|
        ≤u*frozenHN N := by
  obtain ⟨C,hC,hBV⟩ := eventually_primeError_log_saving 3
  have hcentre := tendsto_original87_centre_budget_div_frozenHN_zero.eventually_lt_const (by positivity : 0<u/3)
  filter_upwards [hBV,eventually_ge_atTop (4:ℕ),hcentre,
    p5z_eventually_logCube_le_singularNormalization C (u/3) (by positivity),
    P5PrimeDivisorMean.eventually_log_square_cap_le_normalization (u/3) (by positivity)]
    with N hPrime hN hCen hDist hMod
  intro hev Q c hQ
  let S := Q.filter (fun d => d≤cut N)
  have hs (d : ℕ) (hd : d∈S) := hQ d (Finset.mem_filter.mp hd).1
  have hSc : S⊆Finset.Icc 1 (cut N) := fun d hd =>
    Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hs d hd).1.ne_zero,(Finset.mem_filter.mp hd).2⟩
  have hb := hPrime S hSc (fun d hd => (hs d hd).1) (fun _ => N) (fun _ => N)
    (fun _ _ => le_rfl) (fun d hd => (hs d hd).2.1.symm)
  have hpay : |read S c (primeError N N)|≤u/3*singularNormalization N := by
    calc
      _ ≤ ∑ d∈S,|c d*primeError N N d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d∈S,|primeError N N d| := Finset.sum_le_sum fun d hd => by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hs d hd).2.2
      _ ≤ _ := hb.trans hDist
  have hden := P5PrimeDivisorMean.abs_singleton_PP_sub_total_pi_error_le N (cut N) S c hSc
    (fun d hd => (hs d hd).1) (fun d hd => (hs d hd).2.2)
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq] at hden
  have hdiff : |read S c (primeError N N)-read S c (sharpPrimeError N)|≤u/3*singularNormalization N := by
    simpa only [read,primeError,sharpPrimeError,primeMass,densityTest,mul_one_div] using
      hden.trans (hMod (cut N) (belowHalfCap_le_target (X:=N) (by omega)).2)
  have hlow : |read S c (sharpPrimeError N)|≤2*(u/3*singularNormalization N) := by
    let pp := read S c (primeError N N)
    let sh := read S c (sharpPrimeError N)
    have H := abs_sub_le pp (pp-sh)
    rw [show pp-(pp-sh)=sh by ring] at H
    change |pp|≤_ at hpay
    change |pp-sh|≤_ at hdiff
    change |sh|≤_
    linarith only [H,hpay,hdiff]
  have hz := (centre_paid N Q c (chen_not_prime_of_even_four_le hev hN)
    (fun d hd => (hQ d hd).2.1) (fun d hd => (hQ d hd).2.2)).trans
    ((div_lt_iff₀ (frozenHN_pos N (by omega))).mp hCen).le
  rw [same_normalization] at hlow
  rw [recenter,sub_right_comm,low_part]
  exact (abs_sub_le _ _).trans (by linarith only [hlow,hz])

/-- Exact removal of the high cutoff from this particular finite
coefficient. Its already-proved support is checked only on live moduli. -/
theorem above_eq_middle (N : ℕ) (Q : Finset ℕ) (c : ℕ→ℝ)
    (hactive : ∀d∈Q,c d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) :
    read Q c (highQTest (cut N) (sharpPrimeError N))=middle N Q c := by
  rw [read,middle,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : cut N<d
  · by_cases hi : (d:ℝ)<(N:ℝ)^(599/1000:ℝ)
    · simp [highQTest,h,hi]
    · have hzero : c d=0 := by by_contra hn; exact hi (hactive d hd hn)
      simp [highQTest,h,hi,hzero]
  · simp [highQTest,h]

end
end ImbalancedChen.P1OriginalSharpFiniteReceiver
