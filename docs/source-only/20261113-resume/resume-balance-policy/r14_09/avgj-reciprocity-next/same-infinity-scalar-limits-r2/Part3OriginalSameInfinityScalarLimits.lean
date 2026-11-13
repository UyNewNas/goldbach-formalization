import ImbalancedChen.Part3OriginalSameInfinityScalarGeometry

/-! Both positive-orbit limiting operations over the physical modulus
progression N|k, with a k-majorant valid simultaneously for every N. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityScalarLimits20261113
noncomputable section
open Set Filter Topology Complex
open scoped BigOperators
open OriginalSameInfinityScalarGeometry20261113 OriginalPositiveScalarGeometry20261112
open OriginalPositiveHeightTest20261112 (original) OriginalPositiveRatioWindows20261112 (ratio)
open OriginalPositiveStrip20261112 (residual) ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open OriginalOppositeMarkedKuznetsov20261112 (modulusTerm)
open P3NativePeriod64SamplingSourceOnly (D4) P3Period64NativeReconstructionSourceOnly (spectralTest)
open private bound bound_summable modulus_price term_tendsto from ImbalancedChen.Part3OriginalPositiveOrbitModuli

private theorem price {Φ : ℝ→ℂ} {B : ℝ} (bp : 0≤B) (h : ∀ x>0,‖Φ x‖≤B*x)
    (q m n k : ℕ+) : ‖term Φ q m n k‖≤bound 1 m.val (n.val:ℤ) B k := by
  have np : (0:ℤ)<n.val := by exact_mod_cast n.property
  have raw := modulus_price bp h (by decide : 0<1) m.property np k
  rw [term_filter]
  split_ifs
  · exact raw
  · exact (show ‖(0:ℂ)‖≤‖modulusTerm Φ 1 m.val (n.val:ℤ) k‖ by simp).trans raw

private theorem limit_term {ι : Type*} {l : Filter ι} {F : ι→ℝ→ℂ} {G : ℝ→ℂ}
    (P : ∀ x>0,Tendsto (fun i => F i x) l (𝓝 (G x)))
    (q m n k : ℕ+) : Tendsto (fun i => term (F i) q m n k) l (𝓝 (term G q m n k)) := by
  simp only [term_filter]
  split_ifs
  · exact term_tendsto P (by decide : 0<1) m.property (by exact_mod_cast n.property : (0:ℤ)<n.val) k
  · exact tendsto_const_nhds

def window (ell : D4→ℤ) {Y : ℝ} (yp : 0<Y) (j : ℕ) (q m n : ℕ+) :=
  (if (m.val:ℤ)=(n.val:ℤ) then (ratio ell yp j).function 0/2 else 0)+
    ∑' k : ℕ+,term (response (ratio ell yp j)) q m n k

def target (ell : D4→ℤ) (Y : ℝ) (q m n : ℕ+) :=
  (if (m.val:ℤ)=(n.val:ℤ) then diagonalMoment 0 (spectralTest ell Y)/(2*(Real.pi:ℂ)) else 0)+
    ∑' k : ℕ+,term (residual ell Y) q m n k

/-- The majorant is chosen before the group level, either limit, or
the full modulus. It depends on the fixed positive marks and test.
No uniform large sieve in the marks is asserted by this domination. -/
theorem scalar_moduli (ell : D4→ℤ) {Y : ℝ} (yp : 0<Y) (m n : ℕ+) :
    ∃ U : ℕ+→ℝ,Summable U ∧ ∀ (q k : ℕ+),
      (∀ (j : ℕ) (R : ℝ),‖term (induced (original ell yp R j)) q m n k‖≤U k) ∧
      (∀ j : ℕ,‖term (response (ratio ell yp j)) q m n k‖≤U k) ∧
      ‖term (residual ell Y) q m n k‖≤U k := by
  obtain ⟨B,bp,X,H,W⟩ := joint_price ell yp
  exact ⟨bound 1 m.val (n.val:ℤ) B,bound_summable 1 m.property _ _,fun q k =>
    ⟨fun j R => price bp (X j R) q m n k,fun j => price bp (H j) q m n k,price bp W q m n k⟩⟩

/-- At every actual level q the common collision m=n survives both
limits; only the positive full moduli divisible by q occur. -/
theorem scalar_limits (ell : D4→ℤ) {Y : ℝ} (yp : 0<Y) (q m n : ℕ+) :
    (∀ (j : ℕ) (R : ℝ),Summable (fun k : ℕ+ => ‖term (induced (original ell yp R j)) q m n k‖)) ∧
    (∀ j : ℕ,Summable (fun k : ℕ+ => ‖term (response (ratio ell yp j)) q m n k‖)) ∧
    Summable (fun k : ℕ+ => ‖term (residual ell Y) q m n k‖) ∧
    (∀ j : ℕ,Tendsto (fun R : ℝ => diagonal (original ell yp R j) 1 m.val (n.val:ℤ)+
      ∑' k : ℕ+,term (induced (original ell yp R j)) q m n k) atTop (𝓝 (window ell yp j q m n))) ∧
    Tendsto (fun j => window ell yp j q m n) atTop (𝓝 (target ell Y q m n)) := by
  obtain ⟨U,S,B⟩ := scalar_moduli ell yp m n
  refine ⟨fun j R => S.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (B q k).1 j R),
    fun j => S.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (B q k).2.1 j),
    S.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (B q k).2.2),?_,?_⟩
  · intro j
    have H : Tendsto (fun R : ℝ => ∑' k : ℕ+,term (induced (original ell yp R j)) q m n k)
        atTop (𝓝 (∑' k : ℕ+,term (response (ratio ell yp j)) q m n k)) := by
      apply tendsto_tsum_of_dominated_convergence S
        (fun k => limit_term (fun _ xp => original_pointwise ell yp j xp) q m n k)
      exact Eventually.of_forall (fun R k => (B q k).1 j R)
    simpa only [original_diagonal,eq_self,true_and,window] using
      H.const_add (if (m.val:ℤ)=(n.val:ℤ) then (ratio ell yp j).function 0/2 else 0)
  · have H : Tendsto (fun j : ℕ => ∑' k : ℕ+,term (response (ratio ell yp j)) q m n k)
        atTop (𝓝 (∑' k : ℕ+,term (residual ell Y) q m n k)) := by
      apply tendsto_tsum_of_dominated_convergence S
        (fun k => limit_term (fun _ xp => response_limit ell yp xp.le) q m n k)
      exact Eventually.of_forall (fun j k => (B q k).2.1 j)
    have D := original_diagonal_limit ell yp 1 m.val (n.val:ℤ)
    simpa only [eq_self,true_and,window,target] using D.add H

end
end ImbalancedChen.Part3.OriginalSameInfinityScalarLimits20261113
