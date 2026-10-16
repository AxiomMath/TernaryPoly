module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.HalfDimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar

@[expose] public section


/-!
# Half-dimension: the interface for the general Eisenstein graph

The concrete duality data: the level-preserving involution `g ↦ a (g⁻¹)ᵀ a⁻¹`
(`a = diag(1, 1, 3)`), its flag map from lines to planes, and the invariant nondegenerate
apolar pairing of the coefficient system with its twist by the involution. With these,
`HalfDimension D p` follows from the Eisenstein classes, `H⁴(Γ, ℂ) = 0`, and boundary duality
on the associate pair.
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.Duality

open TernaryPeriodPolynomials.GraphPieces
open TernaryPeriodPolynomials.EisensteinGraph

/-- Boundary duality on the associate pair for the concrete involution, flag map and apolar
pairing: every nonzero line summand class has non-exact boundary cup product with some plane
summand class. -/
def AssociatePairDuality {n : ℕ} (D : InducingData n) : Prop :=
  AssociateDuality D dualInvolution dualFlag (dualPairing n)

/-- No global class projects to `(0, b)` with `b ≠ 0`, for a projector of the away-three Hecke
algebra onto the associate pair, given the Eisenstein classes of the standard graph,
exactness of the twisted cup products of global two-cocycles (a consequence of `H⁴(Γ, ℂ) = 0`), and boundary duality on the associate pair. -/
theorem halfDimension {n : ℕ} (D : InducingData n)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (membership : projection ∈ awayThreeHeckeAlgebra D (Reduction.canonicalStratumHecke n D.chi))
    (range : LinearMap.range projection ≤ associatePair D)
    (existsIntegral : ∀ plane : StandardConstruction.SourceSpace.sourceCocycles D .plane,
      ∃ line, StandardConstruction.StandardRelation.Related D plane line)
    (eisenstein : GraphReduction.HasEisensteinClasses D projection)
    (top : CupProductExactness D dualInvolution (dualPairing n))
    (duality : AssociatePairDuality D) :
    GraphReduction.HalfDimension D projection :=
  halfDimension_of_eisensteinClasses D dualInvolution
    (fun _ membership => dualInvolution_mem_rationalLevel membership) (dualPairing n)
    (fun g _ v w => dualPairing_invariant n D.chi g v w) dualFlag projection membership range
    existsIntegral eisenstein top duality

/-- Variant with the full vanishing `H⁴(Γ, ℂ) = 0` as input. -/
theorem halfDimension_of_globalTopVanishing {n : ℕ} (D : InducingData n)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (membership : projection ∈ awayThreeHeckeAlgebra D (Reduction.canonicalStratumHecke n D.chi))
    (range : LinearMap.range projection ≤ associatePair D)
    (existsIntegral : ∀ plane : StandardConstruction.SourceSpace.sourceCocycles D .plane,
      ∃ line, StandardConstruction.StandardRelation.Related D plane line)
    (eisenstein : GraphReduction.HasEisensteinClasses D projection)
    (top : GlobalTopVanishing) (duality : AssociatePairDuality D) :
    GraphReduction.HalfDimension D projection :=
  halfDimension D projection membership range existsIntegral eisenstein
    (cupProductExactness_of_globalTopVanishing D dualInvolution
      (fun _ membership => dualInvolution_mem_rationalLevel membership) (dualPairing n)
      (fun g _ v w => dualPairing_invariant n D.chi g v w) top) duality

end TernaryPeriodPolynomials.Duality
