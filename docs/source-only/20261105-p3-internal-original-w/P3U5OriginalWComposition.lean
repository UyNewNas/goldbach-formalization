import ImbalancedChen.P3FiniteMixedLeibniz

/-!
P3.6 / MANUSCRIPT-INTERNAL SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

The genuine, arbitrary fixed geometric W is composed with the PREVIOUS
physical HB chart, using ordinary mixed derivatives. The new hypotheses
concern W itself: derivative legitimacy and a fixed-order supremum budget.
They are primitive geometric class conditions of the manuscript, not
a PP estimate, Fourier norm, or an assumption on the desired product.

No arbitrary arithmetic filters are introduced; W is independent of q and
the exact same rho is retained. This packet DOES NOT prove every original
W satisfies the class bounds; that requires each actual geometric family.
-/
namespace ImbalancedChen.P3U5OriginalWComposition
noncomputable section
open scoped Classical BigOperators Topology
open P3AffineTransitionJets P3FiniteMixedLeibniz
open P3SmoothScalarJets P3U5RootAtlas P3U5HBLogChart
open P3U5HBLogMixedL1 P3U5ChartMixedL1Budget

/-- Primitive allowed W class: real, genuine ordinary partials and their
fixed-order magnitude. Neither the Fourier norm nor the W*HB bound occurs
in these hypotheses. W may depend on N through the later caller. -/
def WDerivCompatible {d : ℕ} (W : Point d → ℝ) : Prop :=
  Compatible (fun is => mixed is W)

/-- The concrete HB multiplier has genuine repeated derivatives: the
finite normalized scalar jets are identified with the ordinary derivs. -/
theorem hb_compatible {d g : ℕ} (a : ℝ) (ha : 0 < a) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) :
    Compatible (fun is => mixed is (hbProfile a ell R slot group b trim u v pick m l)) := by
  intro is i x
  let f := P3HBLogScalarProfiles.scalar a ∘ hbKind
  let b' := hbOffsets ell R m b trim u v pick
  let a' := hbSlopes ell slot m group pick
  let e := hbExpr d g l
  have hf : ∀ j,ContDiff ℝ ∞ (f j) := by
    intro j
    exact P3HBLogScalarProfiles.scalar_contDiff ha (hbKind j)
  have hnorm (js : List (Fin d)) :
      mixed js (hbProfile a ell R slot group b trim u v pick m l) =
        fun x => (m+1 : ℝ)^js.length*evalS f b' a' (m+1 : ℝ) (jets js e) x := by
    rw [← eval_hbExpr]
    exact mixed_evalS js e f hf b' a' (m+1 : ℝ)
  have h := ((evalS_hasDerivAt (jets is e) f hf b' a' (m+1 : ℝ) x i).
    const_mul ((m+1 : ℝ)^is.length))
  convert h using 1
  · funext t
    rw [hnorm is]
  · rw [hnorm (i::is)]
    simp only [jets,List.length_cons,pow_succ]
    ring

/-- The previous HB bound has a single constant for EVERY ordered partial
up to the fixed order q, chosen before all chart data and W itself. -/
theorem exists_hb_upto_mixed_bound (d g q : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,∀ l : Lane,
      ∀ is : List (Fin d),is.length ≤ q → ∀ x : Point d,
      |mixed is (hbProfile a ell R slot group b trim u v pick m l) x| ≤
        C*(m+1 : ℝ)^q := by
  have hh : ∀ n : Fin (q+1),∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell →
      ∀ R : Fin 2 → ℝ,∀ slot : Fin d → Option (Fin 2),
      ∀ group : Fin d → Fin g,∀ b : Fin g → ℝ,∀ trim : ℝ,
      ∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,∀ pick : Fin g → Fin d,
      ∀ m : ℕ,∀ l : Lane,∀ is : Fin (n : ℕ) → Fin d,∀ x : Point d,
      |mixed (List.ofFn is) (hbProfile a ell R slot group b trim u v pick m l) x| ≤
        C*(m+1 : ℝ)^(n : ℕ) :=
    fun n => exists_hbProfile_mixed_bound d g n a ha
  choose c hc hb using hh
  let C := 1 + ∑ n : Fin (q+1),c n
  have hc0 (n : Fin (q+1)) : 0 ≤ c n := zero_le_one.trans (hc n)
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hn := Finset.sum_nonneg (s:=Finset.univ) (fun n _ => hc0 n)
    linarith
  intro ell hell R slot group b trim u v pick m l is hlen x
  let n : Fin (q+1) := ⟨is.length,by omega⟩
  have heq : List.ofFn (fun i : Fin is.length => is[i])=is := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'; simp
  have h := hb n ell hell R slot group b trim u v pick m l
    (fun i : Fin is.length => is[i]) x
  rw [heq] at h
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  have hpow : (m+1 : ℝ)^is.length ≤ (m+1 : ℝ)^q :=
    pow_le_pow_right₀ hm hlen
  have hconst : c n ≤ C :=
    (Finset.single_le_sum (fun u _ => hc0 u) (Finset.mem_univ n)).trans
      (by dsimp [C]; linarith)
  exact h.trans ((mul_le_mul_of_nonneg_left hpow (hc0 n)).trans
    (mul_le_mul_of_nonneg_right hconst (by positivity)))

/-- The actual combined extension; W is not replaced with a specially
constructed product of transition functions. -/
def withOriginalW {d g : ℕ} (W : Point d → ℝ) (a ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) (x : Point d) : ℝ :=
  W x*hbProfile a ell R slot group b trim u v pick m l x

/-- Source-only conditional W class theorem, with NO assumption on the
desired product. C is fixed after d,g,q,a but before N, W, and chart scales.
The primitive W bound is uniform over its own ordinary partials up to q. -/
theorem exists_withOriginalW_mixed_bound (d g q : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ group : Fin d → Fin g,
      ∀ b : Fin g → ℝ,∀ trim : ℝ,∀ u : Fin d → ℝ,∀ v : Fin g → ℝ,
      ∀ pick : Fin g → Fin d,∀ m : ℕ,∀ l : Lane,
      ∀ W : Point d → ℝ,WDerivCompatible W →
      ∀ M : ℝ,0 ≤ M →
      (∀ is : List (Fin d),is.length ≤ q →
        ∀ x,|mixed is W x| ≤ M) →
      ∀ is : Fin q → Fin d,∀ x : Point d,
      |mixed (List.ofFn is)
        (withOriginalW W a ell R slot group b trim u v pick m l) x| ≤
        C*M*(m+1 : ℝ)^q := by
  obtain ⟨Ch,hCh,hH⟩ := exists_hb_upto_mixed_bound d g q a ha
  let C : ℝ := (2 : ℝ)^q*Ch
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hp : (1 : ℝ) ≤ 2^q := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  intro ell hell R slot group b trim u v pick m l W hW M hM hWb is x
  have hHbound (js : List (Fin d)) (hjs : js.length ≤ q) :
      |mixed js (hbProfile a ell R slot group b trim u v pick m l) x| ≤
        Ch*(m+1 : ℝ)^q :=
    hH ell hell R slot group b trim u v pick m l js hjs x
  have h := mixed_mul_bound W
    (hbProfile a ell R slot group b trim u v pick m l)
    hW (hb_compatible a ha ell R slot group b trim u v pick m l)
    (List.ofFn is) x M (Ch*(m+1 : ℝ)^q) hM (by positivity)
    (fun js hj => hWb js (by simpa using hj) x)
    (fun js hj => hHbound js (by simpa using hj))
  have hEq : (2 : ℝ)^q*(M*(Ch*(m+1 : ℝ)^q)) =
      C*M*(m+1 : ℝ)^q := by dsimp [C]; ring
  simpa only [withOriginalW,List.length_ofFn,hEq] using h

/-- The old fixed compact cutoff protects W*HB for arbitrary W, without
claiming W itself vanishes outside the chart. -/
theorem withOriginalW_zero_outside {d g : ℕ} (W : Point d → ℝ)
    (a ell : ℝ) (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2))
    (group : Fin d → Fin g) (b : Fin g → ℝ) (trim : ℝ)
    (u : Fin d → ℝ) (v : Fin g → ℝ) (pick : Fin g → Fin d)
    (m : ℕ) (l : Lane) {x : Point d} (hx : x ∉ cube d) :
    withOriginalW W a ell R slot group b trim u v pick m l x=0 := by
  rw [withOriginalW,hbProfile_zero_outside a ell R slot group b trim u v pick m l hx,
    mul_zero]

/-- Exact physical-source identity, with W unaltered and the same
physical group products, pick slots and original pair coordinates. -/
theorem withOriginalW_eq_physical {d g : ℕ} {a ell : ℝ} (ha : 0 < a)
    (hell : 0 < ell) (W : Point d → ℝ) (U : Fin d → ℝ)
    (hU : ∀ i,0 < U i) (R : Fin g → ℝ) (hR : ∀ j,0 < R j)
    (group : Fin d → Fin g) (pair : Fin 2 → Fin g) (hne : pair 0 ≠ pair 1)
    (pick : Fin g → Fin d) {T : ℝ} (hT : 0 < T) (m : ℕ)
    (l : Lane) (x : Point d)
    (hslot : ∀ i,0 ≤ Real.log (U i*Real.exp (x i))/ell ∧
      Real.log (U i*Real.exp (x i))/ell ≤ 2)
    (hgroup : ∀ j,a ≤ Real.log
      (P3HBLogSourceDictionary.groupProduct group
        (fun i => U i*Real.exp (x i)) j)/ell ∧
      Real.log (P3HBLogSourceDictionary.groupProduct group
        (fun i => U i*Real.exp (x i)) j)/ell ≤ 2) :
    withOriginalW W a ell (fun j => P3U5PhysicalProductChart.groupBase U group (pair j))
      (P3U5PhysicalProductChart.pairSlots group pair) group
      (fun j => Real.log (P3U5PhysicalProductChart.groupBase U group j/R j))
      (Real.log ((∏ j,P3U5PhysicalProductChart.groupBase U group j)/T))
      (fun i => Real.log (U i))
      (fun j => Real.log (P3U5PhysicalProductChart.groupBase U group j))
      pick m l x =
      W x*P3U5PhysicalProductChart.physicalProfile ell
        (P3U5PhysicalProductChart.groupBase U group) R group pair T m l x*
        P3HBLogSourceDictionary.originalLogFactor group pick
          (fun i => U i*Real.exp (x i)) := by
  rw [withOriginalW,hbProfile_eq_physical ha hell U hU R hR
    group pair hne pick hT m l x hslot hgroup]
  ring

/-- No q-dependent W or changed rho is introduced by the finite partition;
the test can have any signed arithmetic coefficients. -/
theorem same_rho_withOriginalW {ι : Type*} {d g : ℕ}
    (Q : Finset ℕ) (S : Finset ι) (rho : ℕ → ℝ)
    (F : ℕ → ι → ℝ) (z : ι → Point d) (W : Point d → ℝ)
    (a ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (group : Fin d → Fin g)
    (b : Fin g → ℝ) (trim : ℝ) (u : Fin d → ℝ) (v : Fin g → ℝ)
    (pick : Fin g → Fin d) (m : ℕ) :
    (∑ l : Lane,∑ q ∈ Q,rho q*∑ t ∈ S,
      F q t*withOriginalW W a ell R slot group b trim u v pick m l (z t)) =
      ∑ q ∈ Q,rho q*∑ t ∈ S,F q t*W (z t)*
        (window (z t)*
          (P3LogProductTransitionJets.logStep (trim+∑ i,z t i)*
            ∏ j,P3LogProductTransitionJets.logHat (b j+
              P3U5PhysicalProductChart.groupSum group (z t) j))*
          hbFactor a ell group u v pick (z t)) := by
  simp only [withOriginalW]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mul_sum,← Finset.mul_sum,hbProfile_sum]
  ring

end
end ImbalancedChen.P3U5OriginalWComposition
