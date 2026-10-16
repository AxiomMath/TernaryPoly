module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorAnalyticMaps
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V W index targetIndex : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [Fintype index] [Fintype targetIndex]

def cuspidalTensorHilbertMap (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ V) (targetBasis : Module.Basis targetIndex ℂ W)
    (linear : V →ₗ[ℂ] W) : (index → cusp.H) →L[ℂ] (targetIndex → cusp.H) :=
  ContinuousLinearMap.pi (fun position => basisHilbertFunctional cusp basis ((targetBasis.coord position).comp linear))

omit [Fintype targetIndex] in
theorem cuspidalTensorHilbertMap_embedding (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ V) (targetBasis : Module.Basis targetIndex ℂ W)
    (linear : V →ₗ[ℂ] W) (values : cuspidalTensorValues cusp V) :
    cuspidalTensorHilbertMap cusp basis targetBasis linear
        (cuspidalTensorHilbertEmbedding cusp basis values) =
      cuspidalTensorHilbertEmbedding cusp targetBasis (cuspidalTensorMap cusp linear values) := by
  funext position
  change basisHilbertFunctional cusp basis ((targetBasis.coord position).comp linear)
      (cuspidalTensorHilbertEmbedding cusp basis values) =
    (cuspidalTensorFunctional cusp (targetBasis.coord position) (cuspidalTensorMap cusp linear values)).val
  rw [cuspidalTensorFunctional_map, basisHilbertFunctional_embedding]

theorem cuspidalTensorMap_integral {X : Type} [MeasurableSpace X]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (targetBasis : Module.Basis targetIndex ℂ W) (linear : V →ₗ[ℂ] W)
    (measure : Measure X) (values : X → cuspidalTensorValues cusp V)
    (integrable : Integrable (fun point => cuspidalTensorHilbertEmbedding cusp basis (values point)) measure)
    (result : cuspidalTensorValues cusp V)
    (equality : cuspidalTensorHilbertEmbedding cusp basis result =
      ∫ point, cuspidalTensorHilbertEmbedding cusp basis (values point) ∂measure) :
    cuspidalTensorHilbertEmbedding cusp targetBasis (cuspidalTensorMap cusp linear result) =
      ∫ point, cuspidalTensorHilbertEmbedding cusp targetBasis (cuspidalTensorMap cusp linear (values point)) ∂measure := by
  rw [← cuspidalTensorHilbertMap_embedding cusp basis targetBasis linear result, equality,
    ← (cuspidalTensorHilbertMap cusp basis targetBasis linear).integral_comp_comm integrable]
  apply integral_congr_ae
  filter_upwards [] with point
  exact cuspidalTensorHilbertMap_embedding cusp basis targetBasis linear (values point)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
