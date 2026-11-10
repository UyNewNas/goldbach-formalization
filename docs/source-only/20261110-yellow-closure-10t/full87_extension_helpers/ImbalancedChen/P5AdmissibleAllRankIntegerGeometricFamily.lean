import ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- This is a finite all-rank class of ORIGINAL geometric test profiles.
-- Its hypotheses are support, rank, product and mixed Euler bounds, not PP.
-- The physical signed coefficient is independent of these test coordinates.
namespace ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
noncomputable section
open Classical
open scoped BigOperators
open LicensedOriginalIntegerProfile PerGroupIntegerHBAtlasPushforward

-- The Euler vector differentiates in the original coordinate i. Iterating
-- over a word records mixed derivatives, including repeated coordinates.
def eulerOne {k : ℕ} (i : Fin k) (f : (Fin k → ℝ) → ℝ) :
    (Fin k → ℝ) → ℝ :=
  fun v => fderiv ℝ f v (Pi.single i (v i))

def eulerWord {k : ℕ} (w : List (Fin k))
    (f : (Fin k → ℝ) → ℝ) : (Fin k → ℝ) → ℝ :=
  w.foldr eulerOne f

-- The rank index is Fin (kStar+1), so one family contains all k <= kStar.
-- A single C_m and B_m work for EVERY rank and target at derivative order m.
-- Real support makes the integer extension an actual smooth geometric
-- function; it supplies no congruence, primality or modulus-dependent filter.
structure Family (kStar : ℕ) where
  aStar : ℝ
  aStar_pos : 0 < aStar
  lower : ℝ
  lower_pos : 0 < lower
  upper : ℝ
  upper_pos : 0 < upper
  ambient : (T : ℕ) → (k : Fin (kStar+1)) →
    (Fin k.val → ℝ) → ℝ
  smooth : ∀ T k, ContDiff ℝ ∞ (ambient T k)
  support : ∀ T k v, ambient T k v ≠ 0 →
    (∀ i, lower * (T : ℝ)^aStar ≤ v i) ∧
      (∏ i, v i) ≤ upper * (T : ℝ)
  finitePrimeSupport : ∀ T k,
    Set.Finite {u : Fin k.val → ℕ |
      (∀ i, (u i).Prime) ∧ ambient T k (fun i => (u i : ℝ)) ≠ 0}
  mixedEuler : ∀ m : ℕ, ∃ C B : ℕ,
    0 < C ∧ ∀ (T : ℕ) (k : Fin (kStar+1))
      (w : List (Fin k.val)) (v : Fin k.val → ℝ),
      w.length ≤ m →
      |eulerWord w (ambient T k) v| ≤
        (C : ℝ) * (Real.log ((T : ℝ)+2))^B

def originalWeight {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (u : Fin k.val → ℕ) : ℝ :=
  A.ambient T k (fun i => (u i : ℝ))

def integerWeight {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) (u : Fin k.val → ℕ) : ℝ :=
  A.ambient T k (fun i => (u i : ℝ))

theorem finite_original_prime_support {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) :
    Set.Finite {u : Fin k.val → ℕ |
      (∀ i, (u i).Prime) ∧ originalWeight A T k u ≠ 0} :=
  A.finitePrimeSupport T k

-- This licence is constructed, not inserted as an unverified W_N premise.
def licence {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar+1)) : Licence k.val (originalWeight A T k) where
  ambient := A.ambient T k
  smooth := A.smooth T k
  agrees_on_primes := by
    intro u hu
    rfl

theorem rank_le {kStar : ℕ} (A : Family kStar)
    (k : Fin (kStar+1)) : k.val ≤ kStar := by
  have h := k.isLt
  omega

theorem original_support {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (u : Fin k.val → ℕ)
    (hu : originalWeight A T k u ≠ 0) :
    (∀ i, A.lower * (T : ℝ)^A.aStar ≤ (u i : ℝ)) ∧
      ((∏ i, u i : ℕ) : ℝ) ≤ A.upper * (T : ℝ) := by
  have h := A.support T k (fun i => (u i : ℝ)) hu
  simpa only [Nat.cast_prod] using h

theorem integer_weight_eq_original {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (u : Fin k.val → ℕ) :
    integerWeight A T k u = originalWeight A T k u := rfl

theorem smooth_profile {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (chi eta : ℝ → ℝ)
    (hchi : ContDiff ℝ ∞ chi) (heta : ContDiff ℝ ∞ eta)
    (kappa0 : ℝ) (Rs : Fin k.val → ℝ) :
    ContDiff ℝ ∞
      (chartAmbient (licence A T k) chi eta (T : ℝ) kappa0 Rs) :=
  chartAmbient_smooth (licence A T k) chi eta hchi heta (T : ℝ) kappa0 Rs

theorem smooth_hb_pullback {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (chi eta : ℝ → ℝ)
    (hchi : ContDiff ℝ ∞ chi) (heta : ContDiff ℝ ∞ eta)
    (kappa0 : ℝ) (Rs : Fin k.val → ℝ) {m : ℕ}
    (slots : Fin k.val → Finset (Fin m)) :
    ContDiff ℝ ∞ (fun v : Fin m → ℝ =>
      chartAmbient (licence A T k) chi eta (T : ℝ) kappa0 Rs
        (groupedProducts slots v)) :=
  HB_chart_pullback_smooth (licence A T k) chi eta hchi heta
    (T : ℝ) kappa0 Rs slots

-- For each original chart, every HB factor tuple is sent back to its
-- ORIGINAL independent test word u. The per-group y_i=(2R_i)^(1/3),
-- eta of the COMPLETE product, and all psi factors are retained by the
-- imported exact atlas, for an arbitrary coordinate-dependent test F.
theorem per_chart_all_rank_atlas {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (chi eta : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    {z : ℝ} (hz : 0 ≤ z) (kappa0 : ℝ)
    (cjs ns : List ℕ) (hcjs : cjs.length = k.val)
    (hns : ns.length = k.val) (F : List ℕ → ℂ) :
    atlasEval chi z cjs ns (fun rows =>
      (listExtension (licence A T k) (originalProducts rows) : ℂ) *
        (eta (((originalProducts rows).prod : ℝ)/(T : ℝ)^(1-kappa0)) : ℂ) *
          F (originalProducts rows)) =
      sourceTuple chi z cjs ns *
        ((listExtension (licence A T k) ns : ℂ) *
          (eta ((ns.prod : ℝ)/(T : ℝ)^(1-kappa0)) : ℂ) * F ns) :=
  licensed_profile_atlas_identity (licence A T k) chi eta hone hzero hz
    (T : ℝ) kappa0 cjs ns F

-- On original prime coordinates the atlas's integer extension is exactly
-- the family weight; no prime condition is inserted into the HB bulk.
theorem list_prime_weight {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (u : Fin k.val → ℕ)
    (hu : ∀ i, (u i).Prime) :
    listExtension (licence A T k) (List.ofFn u) = originalWeight A T k u := by
  rw [listExtension_ofFn,integerExtension_eq_on_primes (licence A T k) u hu]

-- The medium/no-medium split is exact before estimates, for any row test.
theorem branch_partition_all_rank {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar+1)) (chi : ℝ → ℝ) (z lo hi : ℝ)
    (cjs ns : List ℕ) (F : List Row → ℂ) :
    atlasEval chi z cjs ns F =
      atlasEval chi z cjs ns (mediumValue lo hi F) +
        atlasEval chi z cjs ns (typeIValue lo hi F) :=
  atlas_exact_branch_partition chi z lo hi cjs ns F

end
end ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
