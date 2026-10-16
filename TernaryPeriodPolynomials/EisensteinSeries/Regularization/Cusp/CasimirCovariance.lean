module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CasimirInvariance
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DerivedCovariance
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CasimirOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

attribute [local instance] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

theorem cuspCasimir_real_covariance (cusp : CuspidalRepresentation)
    (matrix : BinaryRealGL) (vector : cusp.smooth) :
    cuspCasimirOperator cusp (cuspSmoothAction cusp (atInfinity matrix) vector) =
      cuspSmoothAction cusp (atInfinity matrix) (cuspCasimirOperator cusp vector) := by
  have invariant := congrArg (fun action : Module.End ℂ cusp.smooth => action vector)
    (binary_casimir_conjugation_invariant (cuspDerivedAction cusp).toLinearMap matrix)
  simp only [cuspCasimirOperator, cuspSplitOperator, cuspSymmetricOperator, cuspRotationOperator,
    LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    cuspDerivedAction_real_covariance, map_sub, map_add]
  simpa only [LieHom.coe_toLinearMap, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.mul_apply, map_sub, map_add]
    using congrArg (cuspSmoothAction cusp (atInfinity matrix)) invariant

theorem cuspCasimir_finite_covariance (cusp : CuspidalRepresentation)
    (matrix : BinaryFiniteGL) (vector : cusp.smooth) :
    cuspCasimirOperator cusp (cuspSmoothAction cusp (atFinite matrix) vector) =
      cuspSmoothAction cusp (atFinite matrix) (cuspCasimirOperator cusp vector) := by
  simp only [cuspCasimirOperator, cuspSplitOperator, cuspSymmetricOperator, cuspRotationOperator,
    LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    cuspDerivedAction_finite_covariance, map_sub, map_add]

theorem binaryAdelic_real_finite (matrix : BinaryAdelicGL) :
    matrix = atInfinity (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) matrix) *
      atFinite (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) matrix) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, atFinite, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem cuspCasimir_covariance (cusp : CuspidalRepresentation)
    (matrix : BinaryAdelicGL) (vector : cusp.smooth) :
    cuspCasimirOperator cusp (cuspSmoothAction cusp matrix vector) =
      cuspSmoothAction cusp matrix (cuspCasimirOperator cusp vector) := by
  rw [binaryAdelic_real_finite matrix, map_mul]
  simp only [Module.End.mul_apply, cuspCasimir_real_covariance, cuspCasimir_finite_covariance]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
