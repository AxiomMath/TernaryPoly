module

public import TernaryPeriodPolynomials.Building.Proper.SpanKernel
public import TernaryPeriodPolynomials.Building.Good.RelativePresentation

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodOrbitCompleteness

/-- The actual relative and incidence orbit maps have exactly the same kernel. -/
theorem orbit_kernels_eq :
    LinearMap.ker GoodOrbitRelations.orbitMap = LinearMap.ker GoodRelativeChains.orbitMap :=
  SpanComparisonExactness.orbit_kernels_eq ProperSpanKernel.proper_kernel_filling_actual

/-- All relations among actual Good incidence apartment cycles follow from norm, cyclic and swap. -/
theorem orbitMap_ker : LinearMap.ker GoodOrbitRelations.orbitMap = GoodOrbitRelations.relations :=
  orbit_kernels_eq.trans GoodRelativePresentation.orbitMap_ker

/-- The precise completeness inclusion required by cycle lifting, without premises. -/
theorem complete : LinearMap.ker GoodOrbitRelations.orbitMap ≤ GoodOrbitRelations.relations :=
  orbitMap_ker.le

end TernaryPoly.GoodOrbitCompleteness
