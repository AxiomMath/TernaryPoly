module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.ScalarSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.ConstantTerm

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointStandardInduction

theorem integral_induced {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    IsInduced data .line cohomologicalPoint
      (fun argument => ∫ coordinates, standardIntegrand extension cohomologicalPoint argument coordinates
        ∂radicalMeasure) :=
  HilbertScalarSmooth.standard_induced data extension flat cohomologicalPoint
    (HilbertCohomological.point_in_halfPlane degree large)

theorem eisensteinValue_constantTerm_induced {degree : ℕ} (data : InducingData degree)
    (large : 4 ≤ degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (extension : EisensteinValue.flatFamilies data) :
    IsInduced data .line cohomologicalPoint
      (fun argument => ∫ coordinates in additiveDomain ×ˢ additiveDomain,
        EisensteinValue.eisensteinValue data holomorphic extension
          (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) := by
  have equality : (fun argument => ∫ coordinates in additiveDomain ×ˢ additiveDomain,
      EisensteinValue.eisensteinValue data holomorphic extension
        (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) =
      (fun argument => ∫ coordinates, standardIntegrand extension.val cohomologicalPoint argument coordinates
        ∂radicalMeasure) := by
    funext argument
    exact EndpointConstantTerm.eisensteinValue_constantTerm data holomorphic extension large argument
  rw [equality]
  exact integral_induced data large extension.val extension.property

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointStandardInduction
