import ImbalancedChen.CurrentChenP5OriginalU5CausalFinite

/-! Exact original U5 root modulus, shared without small-partner payment imports. -/
namespace ImbalancedChen.P2OriginalU5SmallPartnerRootPayment
noncomputable section
open P5OriginalU5CausalFinite (coordinates)

def rootQ (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  (N : ℝ)^Part5OriginalUpsilon5CausalDictionary.level (coordinates N t 0) (coordinates N t 1)

end
end ImbalancedChen.P2OriginalU5SmallPartnerRootPayment
