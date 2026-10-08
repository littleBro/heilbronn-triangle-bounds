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
    `ExactLayer, `NormCompression, `Slab, `Tuned, `Sphere]
