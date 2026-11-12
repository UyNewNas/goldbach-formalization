import ImbalancedChen.P4BOriginalRankTwoSampleConductor

/-! Fit all cells of one dyadic block to the same local BV supplier, then
telescope the five nonnegative restoring masses at each companion prime. -/
namespace ImbalancedChen.P4BOriginalRankTwoBlockPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalRankTwoGateVariation
open P4BOriginalRankTwoPositiveRestoration
open P4BOriginalRankTwoPrimeMesh
open P4BOriginalPairFibreDictionary (naturalWeight)

theorem exists_block_bound (D : ℕ) : ∃ K : ℝ,0<K ∧ ∃ x0 : ℝ,1<x0 ∧
    ∀ N P V H J : ℕ,∀ (S T : Finset ℕ) (c : ℕ → ℝ) (b kap s kap0 : ℝ),
      let x := (P:ℝ)*(V:ℝ)
      (1:ℝ)<N → 0<s → x0≤x → x^(1/10:ℝ)≤P → x^(1/10:ℝ)≤V →
      P≤H → H≤2*P → 0<J → J≤P → T⊆Finset.Icc 1 (2*V) → T.card≤V →
      (∀ d∈S,0<d ∧ (d:ℝ)≤x^(9/20:ℝ) ∧ N.Coprime d ∧ |c d|≤1) →
      |discrepancy N S c (primes P H) T (naturalWeight b kap s kap0 N)|≤
        2*(J:ℝ)*(K*x/(Real.log x)^D)+20*reciprocalMass S c*x/J := by
  obtain ⟨K,hK,x0,hx0,HB⟩ := P4BOriginalRankTwoSampleConductor.exists_bound D
  refine ⟨K,hK,x0,hx0,?_⟩
  intro N P V H J S T c b kap s kap0
  dsimp only
  intro hN hs hx hP hV hPH hH hJ hJP hT hcard hS
  let E := edge P H J
  let M := reciprocalMass S c
  let x := (P:ℝ)*(V:ℝ)
  let B := K*x/(Real.log x)^D
  let F := naturalWeight b kap s kap0 N
  let G := fun i t => oscillation b kap s kap0 N t (E i) (E (i+1))
  have hM : 0≤M := reciprocalMass_nonneg _ _
  have hG (i t : ℕ) : 0≤G i t := oscillation_nonneg _ _ _ _ _ _ _ _
  have ht (t : ℕ) : (∑ i∈Finset.range J,G i t)≤5 :=
    total_oscillation b kap kap0 hN hs t J E (edge_mono P H J)
  have hGsum : (∑ i∈Finset.range J,∑ t∈T,G i t)≤5*(V:ℝ) := by
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum (fun t _ => ht t)).trans ?_
    simp only [Finset.sum_const,nsmul_eq_mul]
    linarith [show (T.card:ℝ)≤(V:ℝ) by exact_mod_cast hcard]
  have hi (i : ℕ) (hi : i∈Finset.range J) :
      |discrepancy N S c (cell P H J i) T F|≤2*B+
        (2*M*(stride P J:ℝ))*(∑ t∈T,G i t) := by
    have core (cc g : ℕ → ℝ) (hc : ∀ d∈S,|cc d|≤1) (hg : ∀ t∈T,|g t|≤5) :
        |separated N S cc (cell P H J i) T g|≤B :=
      HB N P V (E i) (E (i+1)) S T cc g hx hP hV (edge_bounds hPH i).1
        (edge_mono _ _ _ (Nat.le_succ i)) ((edge_bounds hPH _).2.trans hH) hT hg
        (fun d hd => ⟨(hS d hd).1,(hS d hd).2.1,(hS d hd).2.2.1,hc d hd⟩)
    have hf := core c (F (E i)) (fun d hd => (hS d hd).2.2.2) (fun t _ => by
      have hh := weight_unit b kap s kap0 N (E i) t
      rw [abs_of_nonneg hh.1]
      exact hh.2.trans (by norm_num))
    have he := core (fun d => |c d|) (G i) (fun d hd => by simpa using (hS d hd).2.2.2)
      (fun t _ => by
        rw [abs_of_nonneg (hG i t)]
        exact (Finset.single_le_sum (fun k _ => hG k t) hi).trans (ht t))
    have hh := actual_window hN hs b kap kap0 S c (cell P H J i) T (E i) (E (i+1))
      (fun p hp => ⟨(mem_primes.mp hp).1.le,(mem_primes.mp hp).2.1⟩)
    have hc' : ((cell P H J i).card:ℝ)≤stride P J := by exact_mod_cast cell_card P H J i
    have hpay := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' (by positivity : 0≤2*M))
      (Finset.sum_nonneg (fun t _ => hG i t))
    exact hh.trans ((add_le_add (add_le_add hf he) hpay).trans_eq (by ring))
  have hsplit : discrepancy N S c (primes P H) T F=
      ∑ i∈Finset.range J,discrepancy N S c (cell P H J i) T F := by
    unfold discrepancy
    calc
      _ = ∑ d∈S,∑ i∈Finset.range J,c d*(∑ p∈cell P H J i,
          ∑ t∈T,F p t*P4BOriginalPairFibreDictionary.kernel N d (p*t)) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [cells_sum hPH hH hJ,Finset.mul_sum]
      _ = _ := Finset.sum_comm
  change |discrepancy N S c (primes P H) T F|≤_
  rw [hsplit]
  apply (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hi).trans ?_)
  have fold : (∑ i∈Finset.range J,(2*M*(stride P J:ℝ))*(∑ t∈T,G i t))=
      (2*M*(stride P J:ℝ))*(∑ i∈Finset.range J,∑ t∈T,G i t) := (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_add_distrib,fold]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hscale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stride_bound hJ hJP) (by positivity : 0≤2*M))
    (by positivity : 0≤5*(V:ℝ))
  have hm := mul_le_mul_of_nonneg_left hGsum (by positivity : 0≤2*M*(stride P J:ℝ))
  calc
    _ ≤ (J:ℝ)*(2*B)+(2*M*(2*(P:ℝ)/J))*(5*(V:ℝ)) :=
      add_le_add_left (hm.trans hscale) _
    _ = _ := by dsimp only [M,B,x]; ring

end
end ImbalancedChen.P4BOriginalRankTwoBlockPayment
