module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalRepresentation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped BigOperators

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def binaryCohomologicalHilbertAction (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryRealGL) :
    (BinaryDegreeMonomial (degree + 1) → cusp.H) →L[ℂ] (BinaryDegreeMonomial (degree + 1) → cusp.H) :=
  ContinuousLinearMap.pi (fun monomial => ∑ other : BinaryDegreeMonomial (degree + 1),
    ((normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
        binaryCoefficient degree matrix) (binaryHomogeneousMonomial other)).val.coeff monomial.val •
      ((cuspUnitaryAction cusp (atInfinity matrix)).toContinuousLinearMap.comp (ContinuousLinearMap.proj other)))

theorem binaryCohomologicalHilbertAction_smooth (cusp : CuspidalRepresentation) (degree : ℕ)
    (matrix : BinaryRealGL) (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth) :
    binaryCohomologicalHilbertAction cusp degree matrix (fun monomial => (vectors monomial).val) =
      fun monomial => (binaryCohomologicalRepresentation cusp degree matrix vectors monomial).val := by
  funext monomial
  change (∑ other : BinaryDegreeMonomial (degree + 1), _ •
      ((cuspUnitaryAction cusp (atInfinity matrix)).toContinuousLinearMap.comp (ContinuousLinearMap.proj other)))
      (fun monomial => (vectors monomial).val) =
    (∑ other : BinaryDegreeMonomial (degree + 1),
      ((normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
          binaryCoefficient degree matrix) (binaryHomogeneousMonomial other)).val.coeff monomial.val •
        cuspSmoothAction cusp (atInfinity matrix) (vectors other)).val
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Submodule.coe_sum, Submodule.coe_smul, cuspSmoothAction_apply_val]
  rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
