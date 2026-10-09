import ImbalancedChen.ChenPrimeHarmonicAdapter
import ImbalancedChen.ChenQuotientMovingPrimeAdapter
import ImbalancedChen.ChenPairHarmonicLimit
import ImbalancedChen.ChenVariablePairHarmonicLimit
import ImbalancedChen.ChenVariableTriangleLimits
import Lean.Util.CollectAxioms

/- Owned audit instrumentation. No mathematical declaration is added.
Every exact proof origin, including private/generated declarations, is audited.
The five added origins also emit one axiom report per actual declaration. -/

#print axioms MathlibNt.SieveTheory.MertensTheorem.tendsto_weightedPrimeReciprocalLogSum
#print axioms ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeHarmonicSum
#print axioms ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeTotientLogSum
#print axioms ImbalancedChen.ChenQuotientMovingPrimeAdapter.exists_eventually_bounded_chenSinglePrimeTotientMass
#print axioms ImbalancedChen.ChenQuotientMovingPrimeAdapter.tendsto_chenSinglePrime_moving_sieveFactor
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_sumTest
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_diagonal
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_log_totient_sum
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_log_totient_sum
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_manuscript_log_totient_sum
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_manuscript_log_totient_sum
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.exists_separated_near_continuousOn
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenPrimeTensor_continuous
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.chenY6_kernel_totient_sum_eq_tensor
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.chenY5_kernel_totient_sum_eq_half_square_sub_diagonal
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenPrimeTensor_continuous_diagonal
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY6_kernel_totient_sum
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY5_kernel_totient_sum
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY6_manuscript_kernel_totient_sum
#print axioms ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY5_manuscript_kernel_totient_sum
#print axioms ImbalancedChen.ChenVariablePairKernel.a
#print axioms ImbalancedChen.ChenVariablePairKernel.h
#print axioms ImbalancedChen.ChenVariablePairKernel.d
#print axioms ImbalancedChen.ChenVariablePairKernel.vLevel
#print axioms ImbalancedChen.ChenVariablePairKernel.argument
#print axioms ImbalancedChen.ChenVariablePairKernel.kernel
#print axioms ImbalancedChen.ChenVariablePairKernel.weightedKernel
#print axioms ImbalancedChen.ChenVariablePairKernel.R5
#print axioms ImbalancedChen.ChenVariablePairKernel.R6
#print axioms ImbalancedChen.ChenVariablePairKernel.a_pos
#print axioms ImbalancedChen.ChenVariablePairKernel.a_lt_h
#print axioms ImbalancedChen.ChenVariablePairKernel.h_pos
#print axioms ImbalancedChen.ChenVariablePairKernel.h_lt_d
#print axioms ImbalancedChen.ChenVariablePairKernel.d_le_one
#print axioms ImbalancedChen.ChenVariablePairKernel.h_le_one
#print axioms ImbalancedChen.ChenVariablePairKernel.d_eq_half_sub_three_a
#print axioms ImbalancedChen.ChenVariablePairKernel.vLevel_sub_antitone
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_eq_max_min
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_antitone
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_symm
#print axioms ImbalancedChen.ChenVariablePairKernel.kernel_symm
#print axioms ImbalancedChen.ChenVariablePairKernel.weightedKernel_symm
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_of_le
#print axioms ImbalancedChen.ChenVariablePairKernel.kernel_of_le
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_h_h
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_a_a
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_h_d
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_a_h
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_mem_R5_range
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_mem_R6_range
#print axioms ImbalancedChen.ChenVariablePairKernel.R5_argument_range_subset
#print axioms ImbalancedChen.ChenVariablePairKernel.R6_argument_range_subset
#print axioms ImbalancedChen.ChenVariablePairKernel.argument_h_d_lt_two
#print axioms ImbalancedChen.ChenVariablePairKernel.continuous_vLevel
#print axioms ImbalancedChen.ChenVariablePairKernel.continuous_argument
#print axioms ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R5_of_range
#print axioms ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R6_of_range
#print axioms ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R5
#print axioms ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R6
#print axioms ImbalancedChen.ChenVariablePairKernel.continuousOn_weightedKernel_R5
#print axioms ImbalancedChen.ChenVariablePairKernel.continuousOn_weightedKernel_R6
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.logCoordinate
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.y5HarmonicSum
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.y6HarmonicSum
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.orderedY5HarmonicSum
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.orderedY6HarmonicSum
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.y5HarmonicSum_eq_ordered
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.y6HarmonicSum_eq_ordered
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_y5HarmonicSum
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_y6HarmonicSum
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_orderedY5HarmonicSum
#print axioms ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_orderedY6HarmonicSum
#print axioms ImbalancedChen.SymmetricTriangleIntegral.rectangle_integral_swap
#print axioms ImbalancedChen.SymmetricTriangleIntegral.half_square_eq_triangle_of_integrable
#print axioms ImbalancedChen.SymmetricTriangleIntegral.half_square_eq_triangle
#print axioms ImbalancedChen.ChenVariableTriangleLimits.weightedKernel_ordered
#print axioms ImbalancedChen.ChenVariableTriangleLimits.half_square_eq_y5_triangle
#print axioms ImbalancedChen.ChenVariableTriangleLimits.rectangle_eq_y6_manuscript
#print axioms ImbalancedChen.ChenVariableTriangleLimits.tendsto_y5HarmonicSum_triangle
#print axioms ImbalancedChen.ChenVariableTriangleLimits.tendsto_y6HarmonicSum_manuscript
#print axioms ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY5HarmonicSum_triangle
#print axioms ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY6HarmonicSum_manuscript
#print axioms ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY5HarmonicSum_explicit
#print axioms ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY6HarmonicSum_explicit

set_option pp.all true in
#check @ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeHarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeTotientLogSum

set_option pp.all true in
#check @ImbalancedChen.ChenQuotientMovingPrimeAdapter.exists_eventually_bounded_chenSinglePrimeTotientMass

set_option pp.all true in
#check @ImbalancedChen.ChenQuotientMovingPrimeAdapter.tendsto_chenSinglePrime_moving_sieveFactor

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_sumTest

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_diagonal

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_manuscript_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_manuscript_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.exists_separated_near_continuousOn

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenPrimeTensor_continuous

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.chenY6_kernel_totient_sum_eq_tensor

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.chenY5_kernel_totient_sum_eq_half_square_sub_diagonal

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenPrimeTensor_continuous_diagonal

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY6_kernel_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY5_kernel_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY6_manuscript_kernel_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenContinuousRectangleTransport.tendsto_chenY5_manuscript_kernel_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.a

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.h

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.d

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.vLevel

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.kernel

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.weightedKernel

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.R5

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.R6

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.a_pos

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.a_lt_h

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.h_pos

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.h_lt_d

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.d_le_one

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.h_le_one

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.d_eq_half_sub_three_a

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.vLevel_sub_antitone

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_eq_max_min

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_antitone

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_symm

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.kernel_symm

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.weightedKernel_symm

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_of_le

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.kernel_of_le

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_h_h

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_a_a

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_h_d

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_a_h

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_mem_R5_range

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_mem_R6_range

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.R5_argument_range_subset

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.R6_argument_range_subset

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.argument_h_d_lt_two

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuous_vLevel

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuous_argument

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R5_of_range

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R6_of_range

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R5

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuousOn_kernel_R6

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuousOn_weightedKernel_R5

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairKernel.continuousOn_weightedKernel_R6

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.logCoordinate

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.y5HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.y6HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.orderedY5HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.orderedY6HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.y5HarmonicSum_eq_ordered

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.y6HarmonicSum_eq_ordered

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_y5HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_y6HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_orderedY5HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenVariablePairHarmonicLimit.tendsto_orderedY6HarmonicSum

set_option pp.all true in
#check @ImbalancedChen.SymmetricTriangleIntegral.rectangle_integral_swap

set_option pp.all true in
#check @ImbalancedChen.SymmetricTriangleIntegral.half_square_eq_triangle_of_integrable

set_option pp.all true in
#check @ImbalancedChen.SymmetricTriangleIntegral.half_square_eq_triangle

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.weightedKernel_ordered

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.half_square_eq_y5_triangle

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.rectangle_eq_y6_manuscript

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.tendsto_y5HarmonicSum_triangle

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.tendsto_y6HarmonicSum_manuscript

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY5HarmonicSum_triangle

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY6HarmonicSum_manuscript

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY5HarmonicSum_explicit

set_option pp.all true in
#check @ImbalancedChen.ChenVariableTriangleLimits.tendsto_orderedY6HarmonicSum_explicit

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let auditedModules : List Name := [
    `ImbalancedChen.QuotientChenFourPrime,
    `ImbalancedChen.QuotientChenFourCounts,
    `ImbalancedChen.QuotientChenInitialCounts,
    `ImbalancedChen.QuotientChenSwitchGeometry,
    `ImbalancedChen.QuotientChenNinthSwitch,
    `ImbalancedChen.Counting,
    `ImbalancedChen.Multiplicity,
    `ImbalancedChen.QuotientChenWeightCases,
    `ImbalancedChen.QuotientChenPositiveBound,
    `ImbalancedChen.RoughSquareException,
    `ImbalancedChen.QuotientChenSummedBridge,
    `ImbalancedChen.QuotientChenElevenSum,
    `ImbalancedChen.RationalPowers,
    `ImbalancedChen.OrderedBad,
    `ImbalancedChen.HalfProductGeometry,
    `ImbalancedChen.BadSourceLocalization,
    `ImbalancedChen.HalfProductSource,
    `ImbalancedChen.SieveSourceCoprimality,
    `ImbalancedChen.FiniteSieveModel,
    `ImbalancedChen.CurvedRegionDiscrepancy,
    `ImbalancedChen.CoprimeRecentering,
    `ImbalancedChen.ChenInitialPrimeSource,
    `ImbalancedChen.ChenQuotientPrimeSource,
    `ImbalancedChen.TotientReciprocalBudget,
    `ImbalancedChen.BoundaryGridBudget,
    `ImbalancedChen.BoundaryCellContainment,
    `ImbalancedChen.MultiplicativeGridPartition,
    `ImbalancedChen.BoundaryGlobalCaps,
    `ImbalancedChen.ActualGridEnvelopes,
    `ImbalancedChen.RectangleDiscrepancyAssembly,
    `ImbalancedChen.NormalizationGrowth,
    `ImbalancedChen.SingularSeries,
    `ImbalancedChen.PowerErrorBudget,
    `ImbalancedChen.BoundaryLogMesh,
    `ImbalancedChen.LogCutoffError,
    `ImbalancedChen.CurvedDiscrepancyReduction,
    `ImbalancedChen.LogMeshGridCount,
    `ImbalancedChen.BoundaryArbitraryLog,
    `ImbalancedChen.ChenInitialCorrectionBudget,
    `ImbalancedChen.ChenPrimeHarmonicFinite,
    `AnalyticNumberTheory.LargeSieve.Additive,
    `AnalyticNumberTheory.LargeSieve.GeomSum,
    `AnalyticNumberTheory.LargeSieve.Duality,
    `AnalyticNumberTheory.LargeSieve.WellSpaced,
    `AnalyticNumberTheory.LargeSieve.Multiplicative,
    `AnalyticNumberTheory.Sieve.BombieriVinogradov,
    `AnalyticNumberTheory.Sieve.WeightedPan,
    `AnalyticNumberTheory.Sieve.VaughanIdentity,
    `AnalyticNumberTheory.LargeSieve.CharacterIndicators,
    `AnalyticNumberTheory.Sieve.PanMeanValueBody,
    `AnalyticNumberTheory.LargeSieve.BombieriDavenport,
    `AnalyticNumberTheory.Mertens.Basic,
    `Architect.Basic,
    `Architect.Command,
    `Architect.Content,
    `Architect.Attribute,
    `Architect.CollectUsed,
    `Architect.Tactic,
    `Architect.Output,
    `Architect.Load,
    `Architect,
    `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic,
    `PrimeNumberTheoremAnd.Sobolev,
    `PrimeNumberTheoremAnd.Fourier,
    `PrimeNumberTheoremAnd.Defs,
    `PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics,
    `PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.Support,
    `PrimeNumberTheoremAnd.SmoothExistence,
    `PrimeNumberTheoremAnd.Wiener,
    `PrimeNumberTheoremAnd.Consequences,
    `PrimeNumberTheoremAnd.Auxiliary,
    `PrimeNumberTheoremAnd.MellinCalculus,
    `PrimeNumberTheoremAnd.Rectangle,
    `PrimeNumberTheoremAnd.Tactic.AdditiveCombination,
    `PrimeNumberTheoremAnd.ResidueCalcOnRectangles,
    `PrimeNumberTheoremAnd.EulerMaclaurin,
    `PrimeNumberTheoremAnd.ZetaBounds,
    `PrimeNumberTheoremAnd.ZetaConj,
    `PrimeNumberTheoremAnd.MediumPNT,
    `AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem,
    `AnalyticNumberTheory.PrimeDistribution.ChebyshevTheta,
    `AnalyticNumberTheory.Mertens.PartialSummation,
    `AnalyticNumberTheory.Sieve.GoldbachDensity,
    `AnalyticNumberTheory.Sieve.PanMainTerm,
    `AnalyticNumberTheory.LargeSieve.PanTypeIAssembly,
    `AnalyticNumberTheory.LargeSieve.PanTypeIIAssembly,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds,
    `AnalyticNumberTheory.Sieve.PanV1SquareMean,
    `AnalyticNumberTheory.LargeSieve.NonCoprimeDensity,
    `AnalyticNumberTheory.Mertens.Product,
    `AnalyticNumberTheory.Mertens.MangoldtBridge,
    `AnalyticNumberTheory.Mertens.Abelian,
    `AnalyticNumberTheory.Mertens.GammaKernel,
    `AnalyticNumberTheory.Mertens.PrimeAbel,
    `AnalyticNumberTheory.Mertens.LogChange,
    `AnalyticNumberTheory.Mertens.AbelianRemainder,
    `AnalyticNumberTheory.Mertens.ConstantIdentity,
    `AnalyticNumberTheory.Mertens.FinitePart,
    `AnalyticNumberTheory.Mertens.Theorems,
    `AnalyticNumberTheory.Sieve.SelbergIdentities,
    `AnalyticNumberTheory.Sieve.Distribution,
    `AnalyticNumberTheory.Sieve.LinearSieve,
    `AnalyticNumberTheory.Sieve.SelbergUpperBound,
    `AnalyticNumberTheory.Sieve.SingularSeries,
    `AnalyticNumberTheory.Sieve.PanV3SquareMean,
    `AnalyticNumberTheory.Sieve.SumTwoPowWeighted,
    `AnalyticNumberTheory.Sieve.PanAssembly,
    `AnalyticNumberTheory.Sieve.PanVaughanPointwise,
    `AnalyticNumberTheory.Sieve.W1LemmaB,
    `AnalyticNumberTheory.Sieve.W2Transfer,
    `AnalyticNumberTheory.Sieve.W1Assembly,
    `AnalyticNumberTheory,
    `MathlibNt.SieveTheory.Arithmetic.SingularSeries,
    `MathlibNt.SieveTheory.Arithmetic.MertensTheorem,
    `ImbalancedChen.ChenPrimeHarmonicAdapter,
    `ImbalancedChen.MovingWeightTransport,
    `ImbalancedChen.ChenLogLevelGeometry,
    `ImbalancedChen.ChenQuotientSieveRemainders,
    `ImbalancedChen.ChenQuotientLevelGeometry,
    `ImbalancedChen.ChenQuotientMovingWeight,
    `ImbalancedChen.ChenQuotientMovingPrimeAdapter,
    `ImbalancedChen.ChenPairHarmonicFinite,
    `ImbalancedChen.ChenPairHarmonicLimit,
    `ImbalancedChen.ChenVariablePairKernel,
    `ImbalancedChen.ChenContinuousRectangleTransport,
    `ImbalancedChen.ChenVariablePairHarmonicLimit,
    `ImbalancedChen.SymmetricTriangleIntegral,
    `ImbalancedChen.ChenVariableTriangleLimits ]
  let newModules : List Name := [
    `ImbalancedChen.ChenContinuousRectangleTransport,
    `ImbalancedChen.ChenVariablePairKernel,
    `ImbalancedChen.ChenVariablePairHarmonicLimit,
    `ImbalancedChen.SymmetricTriangleIntegral,
    `ImbalancedChen.ChenVariableTriangleLimits ]
  let emptyModules : List Name := [`Architect, `AnalyticNumberTheory]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut counts : Std.HashMap Name Nat := {}
  let mut declarations : Nat := 0
  for moduleName in env.header.moduleNames do
    logInfo m!"HARMONIC_IMPORTED_MODULE {moduleName}"
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index]!
      if auditedModules.contains moduleName then
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "Forbidden transitive axiom {axiomName} for {name} in {moduleName}"
        if newModules.contains moduleName then
          let mut axiomNames : List String := []
          for axiomName in axioms do
            axiomNames := axiomNames ++ [toString axiomName]
          let axiomReport := String.intercalate "," axiomNames
          logInfo m!"HARMONIC_NEW_DECL_AUDIT {name} module={moduleName} axioms=[{axiomReport}]"
        counts := counts.insert moduleName (counts.getD moduleName 0 + 1)
        declarations := declarations + 1
  for moduleName in auditedModules do
    unless env.header.moduleNames.contains moduleName do
      throwError "Audited module missing from environment: {moduleName}"
    if emptyModules.contains moduleName then
      unless counts.getD moduleName 0 == 0 do
        throwError "Unexpected declaration in pinned import-only module {moduleName}"
    else
      unless counts.getD moduleName 0 > 0 do
        throwError "Missing declaration coverage for custom module {moduleName}"
    logInfo m!"HARMONIC_MODULE_AUDIT {moduleName} declarations={counts.getD moduleName 0}"
  unless declarations > 0 do
    throwError "Empty custom declaration audit"
  logInfo m!"HARMONIC_AXIOM_AUDIT_PASS declarations={declarations} modules={auditedModules.length}"
