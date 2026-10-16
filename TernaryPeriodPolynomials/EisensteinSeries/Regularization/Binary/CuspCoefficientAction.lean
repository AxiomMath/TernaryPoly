module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CuspCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped BigOperators

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def binaryCuspCoefficientAction (cusp : CuspidalRepresentation) (degree : ℕ)
    (operator : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) :
    Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) where
  toFun vectors monomial := ∑ other,
    (operator (binaryHomogeneousMonomial other)).val.coeff monomial.val • vectors other
  map_add' first second := by
    funext monomial
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar vectors := by
    funext monomial
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro other _
    exact smul_comm _ _ _

theorem binaryCuspCoefficientAction_realize (cusp : CuspidalRepresentation) (degree : ℕ)
    (operator : Module.End ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth) (argument : BinaryAdelicGL) :
    binaryCuspRealize cusp degree (binaryCuspCoefficientAction cusp degree operator vectors) argument =
      operator (binaryCuspRealize cusp degree vectors argument) := by
  apply binaryHomogeneousCoordinates_injective (degree + 1)
  funext monomial
  change (_ : MvPolynomial (Fin 2) ℂ).coeff monomial.val = (_ : MvPolynomial (Fin 2) ℂ).coeff monomial.val
  rw [binaryCuspRealize_coefficient]
  change cusp.realize (∑ other : BinaryDegreeMonomial (degree + 1),
      (operator (binaryHomogeneousMonomial other)).val.coeff monomial.val • vectors other) argument =
    (operator (∑ other, cusp.realize (vectors other) argument • binaryHomogeneousMonomial other)).val.coeff monomial.val
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro other _
  exact mul_comm _ _

theorem binaryCuspCoefficientAction_translate (cusp : CuspidalRepresentation) (degree : ℕ)
    (operator : Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) (matrix : BinaryAdelicGL)
    (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth) :
    binaryCuspCoefficientAction cusp degree operator
        (fun monomial => cuspSmoothAction cusp matrix (vectors monomial)) =
      fun monomial => cuspSmoothAction cusp matrix (binaryCuspCoefficientAction cusp degree operator vectors monomial) := by
  funext monomial
  simp only [binaryCuspCoefficientAction, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
