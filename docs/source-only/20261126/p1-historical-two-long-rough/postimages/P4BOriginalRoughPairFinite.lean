import ImbalancedChen.P4BOriginalTwiceMeanPayment
import ImbalancedChen.P5ActualHBRoughBrunFinite
import ImbalancedChen.Part3TwoLongBrunComplexGap
import ImbalancedChen.P1HistoricalTwoLongFiniteRoughData

/-! SOURCE ONLY / UNCOMPILED. Actual finite E3, before any q-sum.
The complex source is majorized inside the positive count+mean sum,
THEN split into a signed gap discrepancy and TWICE the exact mean. -/
namespace ImbalancedChen.P4BOriginalRoughPairFinite
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open PrimeProducts
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.TwoLongLiteralBrunSubstitution (brunPolynomial brunPolynomial_eq_literal)
open Part3.TwoLongActualLowerBrunMoment (brunSupport)
open OriginalOneLongLiteralBrunDictionary (upperCoefficient gapCoefficient actual_B1)
open OriginalOneLongFiniteBrun (polynomial divisorMask actualRough)
open Part3.TwoLongDivisorAxisClosure (chartDivisor)
open Part3.RoughSlotCharacterLift20261026b (smallPrimes smallPrimes_prime)
open Part3.TwoLongTransitionMellinN2
open P4BOriginalPositiveLongEnvelope
open P4BOriginalTwiceMeanPayment (gapPairMean)

end
end ImbalancedChen.P4BOriginalRoughPairFinite
