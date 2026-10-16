module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.MatrixComparison
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Scalar

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory SymmetricSpaceCovering SingularLocalCoefficient SingularLocalSupport
open CompactInteriorRelativeBoundary

local instance originalCoverFact : Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

variable (A : Rep.{0} ℚ DeckGroup)

/-- The proved literal bridge from the original rational local-system model to actual
real covering singular cohomology in every degree. -/
def originalRationalRealOrdinary (n : ℕ) :
    (localCochains singularCoveringProjection quotientProjection_quotientCovering A).homology n ⟶
      forgetReal.obj ((coveringCochains (realRep A).ρ Set.univ).homology n) :=
  matrixRealCohomologyInclusion A n

/-- Actual real ordinary cohomology detects the original rational classes. -/
theorem originalRationalRealOrdinary_injective (n : ℕ) :
    Function.Injective (originalRationalRealOrdinary A n) :=
  matrixRealCohomologyInclusion_injective A n

/-- The actual compact-support bridge uses the support kernels and their directed colimit. -/
def originalRationalRealCompact (n : ℕ) :
    compactCohomology singularCoveringProjection A n ⟶
      forgetReal.obj (realCoverCompactCohomology A n) :=
  matrixRealCompactInclusion A n

/-- The rational compact-to-ordinary map and the actual real covering map commute with
these specific proved comparison maps, in every degree and for arbitrary coefficient representations. -/
theorem originalRationalReal_compact_square (n : ℕ) :
    compactForget singularCoveringProjection A n ≫ originalRationalRealOrdinary A n =
      originalRationalRealCompact A n ≫ forgetReal.map (realCoverCompactForget A n) :=
  matrixReal_compact_square A n

end TernaryPoly.SmoothSingularGlobal
