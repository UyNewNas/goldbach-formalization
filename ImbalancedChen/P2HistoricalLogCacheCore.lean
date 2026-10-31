import ImbalancedChen.P2HistoricLogComputeCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup

def applyCache (cache : List (ℚ × I80)) (fallback : ℚ → I80) : ℚ → I80 :=
  cache.foldr (fun p f q => if q = p.1 then p.2 else f q) fallback

/-- A cache is globally equal to the original function, including outside its keys. -/
theorem applyCache_eq (fallback : ℚ → I80) :
    ∀ cache : List (ℚ × I80),
      (∀ p ∈ cache, p.2 = fallback p.1) → applyCache cache fallback = fallback := by
  intro cache
  induction cache with
  | nil =>
      intro h
      rfl
  | cons p ps ih =>
      intro h
      have hp : p.2 = fallback p.1 := h p (by simp)
      have ht : ∀ z ∈ ps, z.2 = fallback z.1 := by
        intro z hz
        exact h z (by simp [hz])
      funext q
      change (if q = p.1 then p.2 else applyCache ps fallback q) = fallback q
      rw [ih ht]
      split_ifs with he
      · exact hp.trans (congrArg fallback he.symm)
      · rfl

end ImbalancedChen.P2HistoricalLogCache
