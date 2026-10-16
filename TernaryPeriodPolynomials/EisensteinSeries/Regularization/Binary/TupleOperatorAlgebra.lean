module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.PolynomialBrackets
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalDerivedOperator

@[expose] public section


open GeneralEisenstein MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryCuspTupleOperator (cusp : CuspidalRepresentation) (degree : ℕ) :
    Module.End ℂ cusp.smooth →ₐ[ℂ] Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) where
  toFun operator := LinearMap.pi (fun monomial => operator.comp (LinearMap.proj monomial))
  map_one' := by ext vectors monomial; rfl
  map_mul' _ _ := by ext vectors monomial; rfl
  map_zero' := by ext vectors monomial; rfl
  map_add' _ _ := by ext vectors monomial; rfl
  commutes' _ := by ext vectors monomial; rfl

theorem binaryCuspCoefficientAction_one (cusp : CuspidalRepresentation) (degree : ℕ) :
    binaryCuspCoefficientAction cusp degree 1 = 1 := by
  apply LinearMap.ext
  intro vectors
  apply binaryCuspRealize_injective cusp degree
  funext argument
  rw [binaryCuspCoefficientAction_realize]
  rfl

theorem binaryCuspCoefficientAction_mul (cusp : CuspidalRepresentation) (degree : ℕ)
    (first second : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryCuspCoefficientAction cusp degree (first * second) =
      binaryCuspCoefficientAction cusp degree first * binaryCuspCoefficientAction cusp degree second := by
  apply LinearMap.ext
  intro vectors
  apply binaryCuspRealize_injective cusp degree
  funext argument
  simp only [Module.End.mul_apply, binaryCuspCoefficientAction_realize]

noncomputable def binaryCuspCoefficientHom (cusp : CuspidalRepresentation) (degree : ℕ) :
    Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) →ₐ[ℂ]
      Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) where
  toFun := binaryCuspCoefficientAction cusp degree
  map_one' := binaryCuspCoefficientAction_one cusp degree
  map_mul' := binaryCuspCoefficientAction_mul cusp degree
  map_zero' := by
    apply LinearMap.ext
    intro vectors
    funext monomial
    simp [binaryCuspCoefficientAction]
  map_add' first second := by
    apply LinearMap.ext
    intro vectors
    funext monomial
    simp [binaryCuspCoefficientAction, add_smul, Finset.sum_add_distrib]
  commutes' scalar := by
    apply LinearMap.ext
    intro vectors
    apply binaryCuspRealize_injective cusp degree
    funext argument
    rw [binaryCuspCoefficientAction_realize]
    change scalar • binaryCuspRealize cusp degree vectors argument =
      binaryCuspRealize cusp degree (scalar • vectors) argument
    simp only [map_smul, Pi.smul_apply]

theorem binaryCuspTuple_coefficient_commute (cusp : CuspidalRepresentation) (degree : ℕ)
    (operator : Module.End ℂ cusp.smooth)
    (coefficient : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) :
    Commute (binaryCuspTupleOperator cusp degree operator) (binaryCuspCoefficientHom cusp degree coefficient) := by
  apply LinearMap.ext
  intro vectors
  funext monomial
  change operator (∑ other : BinaryDegreeMonomial (degree + 1),
      (coefficient (binaryHomogeneousMonomial other)).val.coeff monomial.val • vectors other) =
    ∑ other, (coefficient (binaryHomogeneousMonomial other)).val.coeff monomial.val • operator (vectors other)
  simp only [map_sum, map_smul]

theorem binaryCohomologicalDerivedOperator_eq_sum (cusp : CuspidalRepresentation) (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCohomologicalDerivedOperator cusp degree direction =
      binaryCuspTupleOperator cusp degree (cuspDerivedAction cusp direction) +
        binaryCuspCoefficientHom cusp degree (binaryCoefficientDerivedOperator degree direction) := rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
