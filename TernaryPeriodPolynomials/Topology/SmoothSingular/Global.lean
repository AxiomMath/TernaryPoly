module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormResolution
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.LocalCoefficients

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits
open SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- The actual common-coefficient augmentation span between the genuine smooth and singular sheaf
complexes. Its global descent and quasi-isomorphism properties require separate proofs. -/
def augmentedSheafSpan : WalkingSpan ⥤
    CochainComplex ((TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ)) ℕ :=
  span (formSheafAugmentation ρ) (singularSheafAugmentation ρ)

end TernaryPoly.SmoothSingularGlobal
