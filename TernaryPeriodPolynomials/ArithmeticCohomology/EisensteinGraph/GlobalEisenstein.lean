module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.EisensteinCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.HolomorphicStandardValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.FullBoundaryMaps

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.GlobalEisenstein

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open StandardConstruction

theorem global_eisenstein_cocycle_exists {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceCochain degree) (closed : IsSourceCocycle data .plane source) :
    ∃ representative : cocycles rationalLevel (rationalCoefficientComponent degree data.chi),
      ∀ vertices : Fin 3 → RationalGL3, representative.val.val vertices =
        PolynomialEisenstein.polynomialValue data holomorphic
          (PolynomialEisenstein.sourceSection data ⟨source, closed⟩
            (GlobalEisensteinCocycle.realVertices vertices)) 1 := by
  refine ⟨EndpointEisensteinCocycle.globalCocycle data holomorphic large ⟨source, closed⟩, ?_⟩
  intro vertices
  rw [EndpointEisensteinCocycle.globalCocycle_realizes,
    GlobalEisensteinCocycle.evaluatedSourceValue_eq_anchor data holomorphic ⟨source, closed⟩ vertices 1,
    inv_one, map_one]

theorem global_eisenstein_full_restriction {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceSpace.sourceCocycles data .plane) :
    FullBoundaryMaps.fullRestriction degree data.chi
      (EndpointEisensteinCocycle.globalClass data holomorphic large source) =
      fullBoundaryClass degree data.chi
        (globalBoundaryCocycle degree data.chi
          (EndpointEisensteinCocycle.globalCocycle data holomorphic large source)) :=
  FullBoundaryMaps.fullRestriction_realizes degree data.chi _

theorem global_eisenstein_boundary_coordinates {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceSpace.sourceCocycles data .plane) :
    FullBoundaryMaps.restriction degree data.chi
      (EndpointEisensteinCocycle.globalClass data holomorphic large source) =
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        (restrictionCocycle degree data.chi .plane
          (EndpointEisensteinCocycle.globalCocycle data holomorphic large source)),
       classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
        (restrictionCocycle degree data.chi .line
          (EndpointEisensteinCocycle.globalCocycle data holomorphic large source))) :=
  FullBoundaryMaps.restriction_realizes degree data.chi _

end TernaryPeriodPolynomials.EisensteinGraph.GlobalEisenstein
