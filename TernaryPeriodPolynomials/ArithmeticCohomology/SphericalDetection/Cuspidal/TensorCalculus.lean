module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorSmoothCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.AnalyticIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

theorem cuspidalTensorIntervalIntegral_exists (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (values : ℝ → cuspidalTensorValues cusp V)
    (continuous : Continuous (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter)))
    (fixed : ∀ parameter, values parameter ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : ∀ center : ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center)) (left right : ℝ) :
    ∃ result : cuspidalTensorValues cusp V,
      cuspidalTensorHilbertEmbedding cusp basis result =
        ∫ parameter in left..right, cuspidalTensorHilbertEmbedding cusp basis (values parameter) ∧
      result ∈ cuspidalTensorFiniteLevel cusp V := by
  let vector : index → cusp.H := ∫ parameter in left..right, cuspidalTensorHilbertEmbedding cusp basis (values parameter)
  have integrable : IntervalIntegrable (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter))
      volume left right := continuous.intervalIntegrable left right
  have coordinate (position : index) : vector position =
      ∫ parameter in left..right, cuspidalTensorHilbertEmbedding cusp basis (values parameter) position :=
    ((ContinuousLinearMap.proj position : (index → cusp.H) →L[ℂ] cusp.H).intervalIntegral_comp_comm integrable).symm
  have coordinate_continuous (position : index) :
      Continuous (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter) position) :=
    (continuous_apply position).comp continuous
  have coordinate_fixed (position : index) (parameter : ℝ) :
      cuspidalTensorHilbertEmbedding cusp basis (values parameter) position ∈ cuspSphericalValues cusp :=
    (cuspidalTensorFiniteLevel_iff_hilbert cusp basis (values parameter)).mp (fixed parameter) position
  have coordinate_analytic (position : index) (center : ℝ) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => cusp.π (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2) position)) (1, center) := by
    let projection : (index → cusp.H) →L[ℝ] cusp.H :=
      (ContinuousLinearMap.proj position : (index → cusp.H) →L[ℂ] cusp.H).restrictScalars ℝ
    exact (projection.analyticAt _).comp (analytic center)
  have smooth (position : index) : vector position ∈ cusp.smooth := by
    rw [coordinate]
    exact cuspSpherical_intervalIntegral_smooth cusp _ (coordinate_continuous position) (coordinate_fixed position)
      (coordinate_analytic position) left right
  obtain ⟨result, equality⟩ := (cuspidalTensorHilbertEmbedding_mem_range cusp basis vector).mpr smooth
  refine ⟨result, equality, (cuspidalTensorFiniteLevel_iff_hilbert cusp basis result).mpr ?_⟩
  intro position
  rw [equality, coordinate]
  exact cuspSpherical_intervalIntegral_mem cusp _ (coordinate_continuous position) (coordinate_fixed position) left right

theorem cuspidalTensorDeriv_exists (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (values : ℝ → cuspidalTensorValues cusp V) (center : ℝ)
    (regular : DifferentiableAt ℝ (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter)) center)
    (fixed : ∀ parameter, values parameter ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center)) :
    ∃ result : cuspidalTensorValues cusp V,
      cuspidalTensorHilbertEmbedding cusp basis result =
        deriv (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter)) center ∧
      result ∈ cuspidalTensorFiniteLevel cusp V := by
  let vector := deriv (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter)) center
  have coordinate (position : index) : vector position =
      deriv (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter) position) center := by
    let projection : (index → cusp.H) →L[ℝ] cusp.H :=
      (ContinuousLinearMap.proj position : (index → cusp.H) →L[ℂ] cusp.H).restrictScalars ℝ
    exact (projection.hasFDerivAt.comp_hasDerivAt center regular.hasDerivAt).deriv.symm
  have coordinate_regular (position : index) : DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (values parameter) position) center :=
    ((ContinuousLinearMap.proj position : (index → cusp.H) →L[ℂ] cusp.H).restrictScalars ℝ).differentiableAt.comp center regular
  have coordinate_fixed (position : index) (parameter : ℝ) :
      cuspidalTensorHilbertEmbedding cusp basis (values parameter) position ∈ cuspSphericalValues cusp :=
    (cuspidalTensorFiniteLevel_iff_hilbert cusp basis (values parameter)).mp (fixed parameter) position
  have coordinate_analytic (position : index) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => cusp.π (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2) position)) (1, center) := by
    let projection : (index → cusp.H) →L[ℝ] cusp.H :=
      (ContinuousLinearMap.proj position : (index → cusp.H) →L[ℂ] cusp.H).restrictScalars ℝ
    exact (projection.analyticAt _).comp analytic
  have smooth (position : index) : vector position ∈ cusp.smooth := by
    rw [coordinate]
    exact cuspSpherical_deriv_smooth cusp _ center (coordinate_regular position) (coordinate_fixed position)
      (coordinate_analytic position)
  obtain ⟨result, equality⟩ := (cuspidalTensorHilbertEmbedding_mem_range cusp basis vector).mpr smooth
  refine ⟨result, equality, (cuspidalTensorFiniteLevel_iff_hilbert cusp basis result).mpr ?_⟩
  intro position
  rw [equality, coordinate]
  exact cuspSpherical_deriv_mem cusp _ center (coordinate_regular position) (coordinate_fixed position)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
