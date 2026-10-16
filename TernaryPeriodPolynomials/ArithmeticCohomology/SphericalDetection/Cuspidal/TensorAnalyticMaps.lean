module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.HilbertFunctionals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspidalTensorFunctional_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (cusp : CuspidalRepresentation) (linear : V →ₗ[ℂ] W) (functional : W →ₗ[ℂ] ℂ)
    (values : cuspidalTensorValues cusp V) :
    cuspidalTensorFunctional cusp functional (cuspidalTensorMap cusp linear values) =
      cuspidalTensorFunctional cusp (functional.comp linear) values := by
  apply cusp.injective
  funext argument
  rw [cuspidalTensorFunctional_realize, cuspidalTensorFunctional_realize]
  rfl

theorem cuspidalTensorMap_hilbert_analyticAt {V W index targetIndex P : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype index] [Fintype targetIndex]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V) (targetBasis : Module.Basis targetIndex ℂ W)
    (linear : V →ₗ[ℂ] W) (values : P → cuspidalTensorValues cusp V) (center : P)
    (analytic : AnalyticAt ℝ (fun point => cuspidalTensorHilbertEmbedding cusp basis (values point)) center) :
    AnalyticAt ℝ (fun point => cuspidalTensorHilbertEmbedding cusp targetBasis (cuspidalTensorMap cusp linear (values point))) center := by
  have regular : ContDiffAt ℝ ⊤
      (fun point => cuspidalTensorHilbertEmbedding cusp targetBasis (cuspidalTensorMap cusp linear (values point))) center := by
    apply contDiffAt_pi.mpr
    intro position
    have composed := ((basisHilbertFunctional cusp basis ((targetBasis.coord position).comp linear)).restrictScalars ℝ).contDiff.contDiffAt.comp
      center (analytic.contDiffAt (n := ⊤))
    convert composed using 1
    funext point
    change (cuspidalTensorFunctional cusp (targetBasis.coord position) (cuspidalTensorMap cusp linear (values point))).val = _
    rw [cuspidalTensorFunctional_map, ← basisHilbertFunctional_embedding cusp basis]
    rfl
  exact regular.analyticAt

theorem binaryHilbertEmbedding_tensor {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1))) :
    binaryHilbertEmbedding cusp basis
      ⟨values.val, (cuspidalTensorValues_binary_iff cusp degree values.val).mp values.property⟩ =
      cuspidalTensorHilbertEmbedding cusp basis values := by
  funext position
  change (binarySmoothCoordinate cusp (basis.coord position) _).val = (cuspidalTensorFunctional cusp (basis.coord position) values).val
  apply congrArg Subtype.val
  apply cusp.injective
  funext argument
  rw [binarySmoothCoordinate_realize, cuspidalTensorFunctional_realize]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
