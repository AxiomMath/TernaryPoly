module

public import TernaryPeriodPolynomials.SymmetricSpace.CoveringTopology
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientManifold
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Manifold ContDiff

/-- The actual global five-coordinate chart defines the manifold atlas of positive forms. -/
instance spaceChartedSpace : ChartedSpace Coordinates Space :=
  coordinateChart.singletonChartedSpace coordinateChart_source

@[simp] theorem space_chartAt (S : Space) : chartAt Coordinates S=coordinateChart := rfl

/-- The positive trace-one model is an actual smooth manifold of dimension five. -/
instance spaceIsManifold : IsManifold 𝓘(ℝ,Coordinates) ∞ Space :=
  coordinateChart.isManifold_singleton coordinateChart_source

instance spaceSecondCountable : SecondCountableTopology Space :=
  coordinateEmbedding.isEmbedding.secondCountableTopology

/-- The model vector space has exactly the five independent real matrix entries. -/
theorem model_finrank : Module.finrank ℝ Coordinates=5 := finrank_coordinates

end TernaryPoly.SymmetricSpaceQuotientManifold
