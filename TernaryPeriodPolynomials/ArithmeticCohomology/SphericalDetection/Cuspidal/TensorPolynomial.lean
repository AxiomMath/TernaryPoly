module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorSmoothCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AlgebraicNilpotentPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {index : Type} [Fintype index]

theorem cuspidalTensorMap_finiteLevel (cusp : CuspidalRepresentation) (linear : V →ₗ[ℂ] W)
    (values : cuspidalTensorValues cusp V) (fixed : values ∈ cuspidalTensorFiniteLevel cusp V) :
    cuspidalTensorMap cusp linear values ∈ cuspidalTensorFiniteLevel cusp W := by
  intro matrix argument
  change linear (values.val _) = linear (values.val _)
  rw [fixed]

theorem cuspidalTensorOrbit_analyticAt_one (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (values : cuspidalTensorValues cusp V) : AnalyticAt ℝ
      (fun matrix : BinaryRealMatrix => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix matrix))
        (cuspidalTensorHilbertEmbedding cusp basis values)) 1 := by
  apply analyticAt_pi_iff.mpr
  intro position
  have regular := smooth_one_contDiffOn
    (function := fun matrix : BinaryRealGL => cusp.π (atInfinity matrix)
      (cuspidalTensorHilbertEmbedding cusp basis values position))
    ((cusp.smooth_exact (cuspidalTensorHilbertEmbedding cusp basis values position)).mp
      (cuspidalTensorFunctional cusp (basis.coord position) values).property).1
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  exact (regular.contDiffAt (domain_open.mem_nhds (by simp))).analyticAt

theorem cuspidalTensorPolynomial_analytic (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (vectors : ℕ → cuspidalTensorValues cusp V) (coefficients : ℕ → ℝ → ℂ) (cutoff : ℕ) (center : ℝ)
    (regular : ∀ power, AnalyticAt ℝ (coefficients power) center) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ => binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (∑ power ∈ Finset.range cutoff, coefficients power point.2 • vectors power)))
      (1, center) := by
  simp only [map_sum, map_smul]
  apply Finset.analyticAt_fun_sum
  intro power _
  exact ((regular power).comp (f := fun point : BinaryRealMatrix × ℝ => point.2) (x := (1, center)) analyticAt_snd).smul
    ((cuspidalTensorOrbit_analyticAt_one cusp basis (vectors power)).comp
      (f := fun point : BinaryRealMatrix × ℝ => point.1) (x := (1, center)) analyticAt_fst)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
