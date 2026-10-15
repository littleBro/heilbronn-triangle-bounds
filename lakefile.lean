import Lake
open Lake DSL

package heilbronn

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "20c73142afa995ac9c8fb80a9bb585a55ca38308"

@[default_target]
lean_lib Heilbronn where
  srcDir := "lean"
  roots := #[`NormExpansion, `NormDescent, `NormAlgebra, `NormPolynomials,
    `NormVandermonde, `BilinearDescent, `BilinearNorm, `ExactLayerData,
    `ExactLayer, `FrobeniusOrbits, `FrobeniusNorm, `FrobeniusDescent,
    `FrobeniusPolynomials, `FrobeniusPacking, `RankFiveExpansion, `RankFiveOrbits,
    `RankFiveNorm, `RankFivePolynomials, `MixedSphere, `MixedLayerData,
    `MixedLayerCounting, `MixedLayerRows0, `MixedLayerRows1, `MixedLayerRows2,
    `MixedLayer, `RankFivePacking, `PairedExpansion, `PairedNorm, `PairedPolynomials,
    `PairedLayerData, `PairedLayerCounting, `PairedLayerRows0, `PairedLayerRows1,
    `PairedLayer, `PairedPacking, `EighteenExpansion, `EighteenNorm, `EighteenPolynomials,
    `EighteenLayerData, `EighteenLayer, `EighteenPacking, `IntervalCounting,
    `TrimmedLayerData, `TrimmedLayer, `TrimmedPacking, `NormCompression, `Slab, `Tuned, `Sphere,
    `SevenDescent, `SevenNorm, `SevenPolynomials, `SevenLayerData, `SevenLayer, `SevenPacking,
    `RowDigits, `FiveDescent, `FiveNorm, `FivePolynomials, `FiveCollision,
    `FiveLayerData, `FiveLayer, `FivePacking, `FiveScales,
    `FiveProbability, `FiveDigits, `FiveJointTail, `FiveTags, `FiveMoment, `FiveCarry, `FiveCoefficientBounds, `FiveLabels, `FiveTagged, `FiveReindex, `FiveFiniteTheorem]
