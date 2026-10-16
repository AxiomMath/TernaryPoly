module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RadicalTrivialZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.Embedding

@[expose] public section


/-!
# `binaryHomogeneousEmbedding` is a linear equivalence at degree `0`

`binaryHomogeneousEmbedding degree` (renaming `Fin 2 → Fin 3` via `Fin.succ`) is always injective
(`binaryHomogeneousEmbedding_injective`, already in the library, fully degree-generic). At degree
`0` it is also surjective: both `HomogeneousPoly 0` and `Binary.HomogeneousPoly 0` are exactly the
constant polynomials (`homogeneousPoly_zero_eq_C`), and renaming a constant polynomial fixes it
(`MvPolynomial.rename_C`), so every ternary constant is hit by the corresponding binary constant.
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **`binaryHomogeneousEmbedding 0` is surjective.** Every ternary constant `C c` is the image of
the binary constant `C c`, since `binaryPolynomialEmbedding = rename Fin.succ` fixes constants. -/
theorem binaryHomogeneousEmbeddingZero_surjective :
    Function.Surjective (binaryHomogeneousEmbedding 0) := by
  intro g
  refine ⟨⟨C (g.val.coeff 0), isHomogeneous_C (Fin 2) _⟩, ?_⟩
  apply Subtype.ext
  simp only [binaryHomogeneousEmbedding, binaryPolynomialEmbedding, LinearMap.coe_mk,
    AddHom.coe_mk, rename_C]
  exact (homogeneousPoly_zero_eq_C g).symm

/-- **`binaryHomogeneousEmbedding` at degree `0` is a linear equivalence.** -/
def binaryHomogeneousEmbeddingZeroEquiv :
    Binary.HomogeneousPoly 0 ≃ₗ[ℂ] HomogeneousPoly 0 :=
  LinearEquiv.ofBijective (binaryHomogeneousEmbedding 0)
    ⟨binaryHomogeneousEmbedding_injective 0, binaryHomogeneousEmbeddingZero_surjective⟩

end TernaryPeriodPolynomials.Argument.FacePairing
