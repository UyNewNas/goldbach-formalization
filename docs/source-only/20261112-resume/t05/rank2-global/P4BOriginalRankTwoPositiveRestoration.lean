import ImbalancedChen.P4BOriginalRankTwoGateVariation

/-! A true nonnegative envelope for the progression term and the same
coprime mean. The two uses of the conductor bound have weights c and |c|. -/
namespace ImbalancedChen.P4BOriginalRankTwoPositiveRestoration
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalPairFibreDictionary (kernel naturalWeight)
open P4BOriginalRankTwoGateVariation

def discrepancy (N : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) (H T : Finset ℕ) (W : ℕ → ℕ → ℝ) :=
  ∑ d∈S,c d*(∑ p∈H,∑ t∈T,W p t*kernel N d (p*t))

def separated (N : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) (H T : Finset ℕ) (g : ℕ → ℝ) :=
  discrepancy N S c H T (fun _ t => g t)

def reciprocalMass (S : Finset ℕ) (c : ℕ → ℝ) := ∑ d∈S,|c d|/(d.totient:ℝ)

theorem reciprocalMass_nonneg (S : Finset ℕ) (c : ℕ → ℝ) :
    0≤reciprocalMass S c := Finset.sum_nonneg (fun _ _ => by positivity)

theorem modulus_budget {N : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}
    (hS : S⊆Finset.Icc 1 N) (hc : ∀ d∈S,|c d|≤1) :
    reciprocalMass S c≤4*(1+Real.log (max 1 (N:ℝ))) :=
  (Finset.sum_le_sum (fun d hd => div_le_div_of_nonneg_right (hc d hd) (Nat.cast_nonneg _))).trans
    (sum_reciprocal_totient_subset_le_log S N hS)

private theorem kernel_envelope (N d x : ℕ) :
    |kernel N d x|≤kernel N d x+2/(d.totient:ℝ) := by
  let A : ℝ := if Nat.ModEq d x N then 1 else 0
  let B : ℝ := (if x.Coprime d then 1 else 0)/(d.totient:ℝ)
  have hA : 0≤A := by dsimp [A]; split_ifs <;> norm_num
  have hB : 0≤B := by dsimp [B]; split_ifs <;> positivity
  have hB' : B≤1/(d.totient:ℝ) :=
    div_le_div_of_nonneg_right (by split_ifs <;> norm_num) (Nat.cast_nonneg _)
  change |A-B|≤A-B+2/(d.totient:ℝ)
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg hA,abs_of_nonneg hB]
  linarith

theorem discrepancy_sub (N : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) (H T : Finset ℕ)
    (F G : ℕ → ℕ → ℝ) :
    discrepancy N S c H T F-discrepancy N S c H T G=
      discrepancy N S c H T (fun p t => F p t-G p t) := by
  simp only [discrepancy,sub_mul,Finset.sum_sub_distrib,mul_sub]

/-- All three sums have the exact same finite carrier; no estimate for
an unweighted coprime correction replaces the underlying discrepancy. -/
theorem envelope_error (N : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) (H T : Finset ℕ)
    (F : ℕ → ℕ → ℝ) (E : ℕ → ℝ)
    (hE : ∀ p∈H,∀ t∈T,|F p t|≤E t) :
    |discrepancy N S c H T F|≤|separated N S (fun d => |c d|) H T E|+
      2*reciprocalMass S c*(H.card:ℝ)*(∑ t∈T,E t) := by
  let top := fun (d p t : ℕ) => |c d|*(E t*kernel N d (p*t)+E t*(2/(d.totient:ℝ)))
  have hpt (d p t : ℕ) (hp : p∈H) (ht : t∈T) :
      |c d*(F p t*kernel N d (p*t))|≤top d p t := by
    rw [abs_mul,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      _ ≤ E t*(kernel N d (p*t)+2/(d.totient:ℝ)) := mul_le_mul (hE p hp t ht)
        (kernel_envelope _ _ _) (abs_nonneg _) ((abs_nonneg _).trans (hE p hp t ht))
      _ = _ := mul_add _ _ _
  have hrewrite :
      (∑ d∈S,∑ p∈H,∑ t∈T,top d p t)=
        separated N S (fun d => |c d|) H T E+2*reciprocalMass S c*(H.card:ℝ)*(∑ t∈T,E t) := by
    let B := ∑ t∈T,E t
    have ht (d : ℕ) : (∑ t∈T,|c d|*(E t*(2/(d.totient:ℝ))))=
        (|c d|*(2/(d.totient:ℝ)))*B := by
      rw [show B=∑ t∈T,E t from rfl,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have hc (d : ℕ) : (∑ _p∈H,(|c d|*(2/(d.totient:ℝ)))*B)=
        (2*(H.card:ℝ)*B)*(|c d|/(d.totient:ℝ)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    calc
      _ = separated N S (fun d => |c d|) H T E+
          (∑ d∈S,(2*(H.card:ℝ)*B)*(|c d|/(d.totient:ℝ))) := by
        simp only [top,separated,discrepancy,mul_add,Finset.sum_add_distrib,Finset.mul_sum,ht,hc]
      _ = _ := by rw [←Finset.mul_sum]; unfold reciprocalMass; dsimp only [B]; ring
  calc
    _ = |∑ d∈S,∑ p∈H,∑ t∈T,c d*(F p t*kernel N d (p*t))| := by
      simp only [discrepancy,Finset.mul_sum]
    _ ≤ ∑ d∈S,∑ p∈H,∑ t∈T,top d p t := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun t ht => hpt d p t hp ht))
    _ ≤ _ := hrewrite.le.trans (add_le_add_right (le_abs_self _) _)

theorem actual_window {N : ℕ} (hN : (1:ℝ)<N) {s : ℝ} (hs : 0<s)
    (b kap kap0 : ℝ) (S : Finset ℕ) (c : ℕ → ℝ) (H T : Finset ℕ)
    (l u : ℕ) (hH : ∀ p∈H,l≤p ∧ p≤u) :
    |discrepancy N S c H T (naturalWeight b kap s kap0 N)|≤
      |separated N S c H T (naturalWeight b kap s kap0 N l)|+
      |separated N S (fun d => |c d|) H T (fun t => oscillation b kap s kap0 N t l u)|+
      2*reciprocalMass S c*(H.card:ℝ)*(∑ t∈T,oscillation b kap s kap0 N t l u) := by
  let D := discrepancy N S c H T (naturalWeight b kap s kap0 N)
  let D₀ := separated N S c H T (naturalWeight b kap s kap0 N l)
  have h := envelope_error N S c H T (fun p t => naturalWeight b kap s kap0 N p t-
    naturalWeight b kap s kap0 N l t) (fun t => oscillation b kap s kap0 N t l u)
    (fun p hp t ht => local_oscillation b kap kap0 hN hs t (hH p hp).1 (hH p hp).2)
  have he : |D-D₀|≤_ := by
    dsimp only [D,D₀,separated]
    rw [discrepancy_sub]
    exact h
  have tri := abs_add_le D₀ (D-D₀)
  rw [show D₀+(D-D₀)=D by ring] at tri
  exact tri.trans ((add_le_add_left he _).trans_eq (by ring))

end
end ImbalancedChen.P4BOriginalRankTwoPositiveRestoration
