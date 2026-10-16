module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.LowestCuspForm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.IntegralRepresentatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_atFinite_mul (first second : BinaryFiniteGL) :
    atFinite (first * second) = atFinite first * atFinite second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atFinite, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem cuspFiniteFixed_integral_translate (cusp : CuspidalRepresentation)
    (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) :
    cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix)) vector.val ∈
      cuspFiniteFixedSubmodule cusp binaryPrincipalLevel := by
  intro element
  let translated : binaryPrincipalLevel := ⟨_, binaryPrincipalLevel_integral_conjugate_mem matrix element⟩
  change cusp.π (atFinite element.val)
    (cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding matrix)) vector.val.val) = _
  have identity : element.val * GeneralLinearGroup.map integralEmbedding matrix =
      GeneralLinearGroup.map integralEmbedding matrix * translated.val := by
    dsimp only [translated]
    group
  rw [← Module.End.mul_apply, ← map_mul, ← binary_atFinite_mul, identity,
    binary_atFinite_mul, map_mul, Module.End.mul_apply, vector.property translated]
  rfl

theorem cuspPrincipalLowest_integral_translate (cusp : CuspidalRepresentation) (weight : ℕ)
    (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (vector : cuspPrincipalLowestSubmodule cusp weight) :
    cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix)) vector.val ∈
      cuspPrincipalLowestSubmodule cusp weight := by
  refine ⟨cuspFiniteFixed_integral_translate cusp matrix ⟨vector.val, vector.property.1⟩, ?_, ?_⟩
  · change cuspDerivedAction cusp binaryRotationDirection _ = _
    rw [cuspDerivedAction_finite_covariance]
    change cuspSmoothAction cusp _ (cuspRotationOperator cusp vector.val) = _
    rw [vector.property.2.1, map_smul]
  · have commute : cuspLoweringOperator cusp
        (cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix)) vector.val) =
      cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map integralEmbedding matrix))
        (cuspLoweringOperator cusp vector.val) := by
      simp only [cuspLoweringOperator, cuspSplitOperator, cuspSymmetricOperator,
        LinearMap.sub_apply, LinearMap.smul_apply, cuspDerivedAction_finite_covariance, map_sub, map_smul]
    rw [commute, vector.property.2.2, map_zero]

noncomputable def cuspPrincipalLowestIntegralAction (cusp : CuspidalRepresentation) (weight : ℕ)
    (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    Module.End ℂ (cuspPrincipalLowestSubmodule cusp weight) where
  toFun vector := ⟨_, cuspPrincipalLowest_integral_translate cusp weight matrix vector⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem cuspPrincipalLowestIntegralAction_same_reduction (cusp : CuspidalRepresentation) (weight : ℕ)
    (first second : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (same : GeneralLinearGroup.map integralReduction first = GeneralLinearGroup.map integralReduction second)
    (vector : cuspPrincipalLowestSubmodule cusp weight) :
    cuspPrincipalLowestIntegralAction cusp weight first vector =
      cuspPrincipalLowestIntegralAction cusp weight second vector := by
  let quotient : binaryPrincipalLevel :=
    ⟨_, binaryIntegral_same_reduction_quotient_mem first second same⟩
  have fixed : cuspSmoothAction cusp (atFinite quotient.val) vector.val = vector.val :=
    Subtype.ext (vector.property.1 quotient)
  apply Subtype.ext
  change cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map integralEmbedding first)) vector.val =
    cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map integralEmbedding second)) vector.val
  have identity : GeneralLinearGroup.map integralEmbedding second =
      GeneralLinearGroup.map integralEmbedding first * quotient.val := by
    dsimp only [quotient]
    rw [map_mul, map_inv]
    group
  rw [identity, binary_atFinite_mul, map_mul, Module.End.mul_apply, fixed]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
