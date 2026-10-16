module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.TernaryCoefficientRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneHilbertAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneLeviCoefficient_functional_analyticAt_one {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    AnalyticAt ℝ (fun matrix : BinaryRealMatrix => functional
      (realCoefficientComponent degree trivialCharacter (planeLevi (invertibleMatrix matrix) 1) polynomial)) 1 := by
  have regular := realPlaneLeviCoefficient_functional_contDiffOn (fun matrix : BinaryRealMatrix => matrix)
    (fun row column => by fun_prop) (domain := {matrix : BinaryRealMatrix | matrix.det ≠ 0})
    (fun _ member => member) polynomial functional (order := ⊤)
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  exact (regular.contDiffAt (domain_open.mem_nhds (show (1 : BinaryRealMatrix).det ≠ 0 by simp))).analyticAt

theorem realPlaneLeviAction_orbital_analyticAt {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (values : P → cuspidalTensorValues cusp (HomogeneousPoly degree)) (center : P)
    (analytic : AnalyticAt ℝ (fun point : BinaryRealMatrix × P =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center)) :
    AnalyticAt ℝ (fun point : BinaryRealMatrix × P => cuspidalTensorHilbertEmbedding cusp basis
      ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inr (invertibleMatrix point.1))
        (values point.2))) (1, center) := by
  have vector_regular := analytic.contDiffAt (n := ⊤)
  have coefficient_regular : ContDiffAt ℝ ⊤ (fun point : BinaryRealMatrix × P =>
      basisHilbertCoefficient cusp basis
        (realCoefficientComponent degree trivialCharacter (planeLevi (invertibleMatrix point.1) 1))
        (binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (values point.2)))) (1, center) := by
    apply contDiffAt_pi.mpr
    intro position
    simp only [basisHilbertCoefficient_apply]
    apply ContDiffAt.sum
    intro source _
    have scalar := (realPlaneLeviCoefficient_functional_analyticAt_one (basis source) (basis.coord position)).comp
      (f := fun point : BinaryRealMatrix × P => point.1) (x := (1, center)) analyticAt_fst
    exact scalar.contDiffAt.smul (contDiffAt_pi.mp vector_regular source)
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  have scalar_on := binary_normalizingFactor_contDiffOn (fun matrix : BinaryRealMatrix => matrix)
    (fun row column => by fun_prop) (domain := {matrix : BinaryRealMatrix | matrix.det ≠ 0}) (fun _ member => member)
    (((degree : ℂ) + 3) / 2) (order := ⊤)
  have scalar := (scalar_on.contDiffAt (domain_open.mem_nhds (show (1 : BinaryRealMatrix).det ≠ 0 by simp))).comp
    (f := fun point : BinaryRealMatrix × P => point.1) (1, center) contDiffAt_fst
  have combined := (scalar.smul coefficient_regular).analyticAt
  convert combined using 1
  funext point
  refine (realPlaneHilbertOperator_intertwines degree cusp trivialCharacter basis
    (SemidirectProduct.inr (invertibleMatrix point.1)) (values point.2)).trans ?_
  change realPlaneCuspidalTwist degree (SemidirectProduct.inr (invertibleMatrix point.1)) •
    basisHilbertCoefficient cusp basis
      (realCoefficientComponent degree trivialCharacter (realPlaneMatrix (SemidirectProduct.inr (invertibleMatrix point.1))))
      (binaryHilbertTranslation cusp (realPlaneBinaryInput (SemidirectProduct.inr (invertibleMatrix point.1)))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) = _
  rw [realPlaneMatrix_inr]
  rfl

theorem realPlaneLeviAction_orbital_analyticAt_of_trivial {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (values : P → cuspidalTensorValues cusp (HomogeneousPoly degree)) (center : P)
    (analytic : AnalyticAt ℝ (fun point : BinaryRealMatrix × P =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center)) :
    AnalyticAt ℝ (fun point : BinaryRealMatrix × P => cuspidalTensorHilbertEmbedding cusp basis
      ((realPlaneCuspidalRep degree cusp character).ρ (SemidirectProduct.inr (invertibleMatrix point.1))
        (values point.2))) (1, center) := by
  subst character
  exact realPlaneLeviAction_orbital_analyticAt degree cusp basis values center analytic

end TernaryPeriodPolynomials.SphericalDetection.Helpers
