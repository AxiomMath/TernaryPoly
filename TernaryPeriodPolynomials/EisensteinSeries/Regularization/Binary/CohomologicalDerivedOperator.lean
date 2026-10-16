module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.PathDerivative
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalHilbertAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryCohomologicalDerivedOperator (cusp : CuspidalRepresentation) (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) :=
  LinearMap.pi (fun monomial => (cuspDerivedAction cusp direction).comp (LinearMap.proj monomial)) +
    binaryCuspCoefficientAction cusp degree (binaryCoefficientDerivedOperator degree direction)

theorem binaryCohomologicalDerivedOperator_val (cusp : CuspidalRepresentation) (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth)
    (monomial : BinaryDegreeMonomial (degree + 1)) :
    (binaryCohomologicalDerivedOperator cusp degree direction vectors monomial).val =
      (cuspDerivedAction cusp direction (vectors monomial)).val +
        ∑ other, (binaryCoefficientDerivedOperator degree direction (binaryHomogeneousMonomial other)).val.coeff monomial.val •
            (vectors other).val := by
  change (cuspDerivedAction cusp direction (vectors monomial) +
    ∑ other, (binaryCoefficientDerivedOperator degree direction (binaryHomogeneousMonomial other)).val.coeff monomial.val •
        vectors other).val = _
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]

theorem binaryCohomologicalRepresentation_path_hasDerivAt
    (cusp : CuspidalRepresentation) (degree : ℕ)
    (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth)
    (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (traceless : Matrix.trace tangent = 0) (monomial : BinaryDegreeMonomial (degree + 1)) :
    HasDerivAt (fun t => (binaryCohomologicalRepresentation cusp degree (path t) vectors monomial).val)
      (binaryCohomologicalDerivedOperator cusp degree tangent vectors monomial).val point := by
  classical
  have term (other : BinaryDegreeMonomial (degree + 1)) :=
    (binary_twistedCoefficient_derived_hasDerivAt degree path tangent point identity derivative traceless
      (binaryHomogeneousMonomial other) monomial.val).smul
        (cuspSmoothAction_path_hasDerivAt cusp (vectors other) path tangent point identity derivative)
  have computed := HasDerivAt.sum (fun other (_ : other ∈ Finset.univ) => term other)
  convert! computed using 1
  · ext t
    change (∑ other : BinaryDegreeMonomial (degree + 1),
      ((normPower (GeneralLinearGroup.det (atInfinity (path t))) (((degree : ℂ) + 3) / 2) •
          binaryCoefficient degree (path t)) (binaryHomogeneousMonomial other)).val.coeff monomial.val •
        cuspSmoothAction cusp (atInfinity (path t)) (vectors other)).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply]
    rfl
  · rw [binaryCohomologicalDerivedOperator_val]
    have equal (other : BinaryDegreeMonomial (degree + 1)) :
        other.val = monomial.val ↔ other = monomial := ⟨Subtype.ext, congrArg Subtype.val⟩
    simp [identity, binary_atInfinity_one, normPower_one, binaryCoefficient,
      binaryHomogeneousMonomial, coeff_monomial, equal, Finset.sum_add_distrib]

theorem binaryCohomologicalHilbertAction_path_hasDerivAt
    (cusp : CuspidalRepresentation) (degree : ℕ)
    (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth)
    (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (traceless : Matrix.trace tangent = 0) :
    HasDerivAt (fun t => binaryCohomologicalHilbertAction cusp degree (path t)
      (fun monomial => (vectors monomial).val))
      (fun monomial => (binaryCohomologicalDerivedOperator cusp degree tangent vectors monomial).val) point := by
  simp only [binaryCohomologicalHilbertAction_smooth]
  exact hasDerivAt_pi.mpr
    (binaryCohomologicalRepresentation_path_hasDerivAt cusp degree vectors path tangent point identity derivative traceless)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
