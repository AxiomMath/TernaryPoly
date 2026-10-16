module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryBasic

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientBoundary
open Topology SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- Descend one actual half-space chart through a local section of the principal-six covering. -/
def quotientChart (x : Glued) : OpenPartialHomeomorph BordifiedOrbit (EuclideanHalfSpace 5) :=
  (localLift x).trans (chartAt (EuclideanHalfSpace 5) x)

@[simp] theorem quotientChart_apply (x : Glued) (q : BordifiedOrbit) :
    quotientChart x q=chartAt (EuclideanHalfSpace 5) x (localLift x q) := rfl

@[simp] theorem quotientChart_self (x : Glued) :
    quotientChart x (projection principalSix x)=chartAt (EuclideanHalfSpace 5) x x := by
  rw [quotientChart_apply,localLift_self]

theorem self_mem_quotientChart (x : Glued) :
    projection principalSix x∈(quotientChart x).source := by
  change projection principalSix x∈(localLift x).source ∧
    localLift x (projection principalSix x)∈(chartAt (EuclideanHalfSpace 5) x).source
  rw [localLift_self]
  exact ⟨self_mem_localLift_source x,mem_chart_source _ x⟩

/-- The inverse quotient chart is literally the original half-space parametrization followed by
projection to arithmetic orbits. The formula is valid on the whole model. -/
@[simp] theorem quotientChart_symm_apply (x : Glued) (u : EuclideanHalfSpace 5) :
    (quotientChart x).symm u=
      projection principalSix ((chartAt (EuclideanHalfSpace 5) x).symm u) := by
  change (localLift x).symm ((chartAt (EuclideanHalfSpace 5) x).symm u)=_
  rw [localLift_symm]

/-- The original half-space inverse is the actual rational parametrization. -/
theorem gluedChart_symm_apply (x : Glued) (u : EuclideanHalfSpace 5) :
    (chartAt (EuclideanHalfSpace 5) x).symm u=
      SymmetricSpaceBoundaryCharts.halfSpaceParam (SymmetricSpaceBoundaryCharts.selectedFrame x) u := by
  rw [SymmetricSpaceBoundaryCharts.chartAt_eq,SymmetricSpaceBoundaryCharts.halfSpaceChart_symm_apply]

/-- These literal covering charts cover the actual principal-six orbit quotient. -/
instance chartedSpace : ChartedSpace (EuclideanHalfSpace 5) BordifiedOrbit where
  atlas := Set.range quotientChart
  chartAt q := quotientChart q.out
  mem_chart_source q := by
    have h := self_mem_quotientChart q.out
    simpa only [projection,Quotient.out_eq] using h
  chart_mem_atlas q := ⟨q.out,rfl⟩

@[simp] theorem quotient_chartAt (q : BordifiedOrbit) :
    chartAt (EuclideanHalfSpace 5) q=quotientChart q.out := rfl

@[simp] theorem quotient_chartAt_self (q : BordifiedOrbit) :
    chartAt (EuclideanHalfSpace 5) q q=chartAt (EuclideanHalfSpace 5) q.out q.out := by
  have h := quotientChart_self q.out
  simpa only [projection,Quotient.out_eq,quotient_chartAt] using h

theorem quotientChart_mem_atlas (x : Glued) :
    quotientChart x∈atlas (EuclideanHalfSpace 5) BordifiedOrbit := ⟨x,rfl⟩

end TernaryPoly.SymmetricSpaceQuotientBoundary
