module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.Orientation
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldAtlas
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.ContractibleInterior
public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationHomeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeFundamental
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SymmetricSpaceCovering SymmetricSpaceBordifiedContractible SymmetricSpaceCharts

instance bordifiedHausdorff : T2Space BordifiedOrbit :=
  SymmetricSpaceCompactBordification.quotient_hausdorff principalSix

instance bordifiedCompact : CompactSpace BordifiedOrbit :=
  SymmetricSpaceCompactBordification.quotient_compact principalSix

/-- The literal complement of the boundary is the actual open arithmetic interior. -/
theorem boundary_compl_eq_range : (boundary principalSix)ᶜ = Set.range arithmeticEmbedding := by
  change (Set.range (interiorEmbedding principalSix))ᶜᶜ = _
  rw [compl_compl]
  exact arithmeticInterior_eq.symm

/-- The actual complement of the boundary identifies with the constructed
arithmetic manifold by its literal open embedding. -/
def interiorHomeomorph : ↥(boundary principalSix)ᶜ ≃ₜ OrbitSpace :=
  (Homeomorph.setCongr boundary_compl_eq_range).trans
    arithmeticEmbedding_isOpenEmbedding.isEmbedding.toHomeomorph.symm

/-- Transport the actual five-dimensional arithmetic atlas to its literal interior subtype. -/
instance interiorChartedSpace : ChartedSpace Coordinates ↥(boundary principalSix)ᶜ :=
  interiorHomeomorph.symm.chartedSpace

/-- The five matrix-coordinate entries give the required Euclidean model homeomorphism. -/
def interiorEuclidean : Coordinates ≃ₜ EuclideanSpace ℝ (Fin 5) :=
  (EuclideanSpace.equiv (Fin 5) ℝ).toHomeomorph.symm

/-- The actual arithmetic quotient orientation, transported by the literal interior homeomorphism. -/
def interiorOrientation : RationalLocalOrientation.Orientation 5 ↥(boundary principalSix)ᶜ :=
  RationalLocalOrientation.Orientation.pullback interiorHomeomorph 5
    SymmetricSpaceQuotientOrientation.quotientOrientation

end TernaryPoly.SymmetricSpaceRelativeFundamental
