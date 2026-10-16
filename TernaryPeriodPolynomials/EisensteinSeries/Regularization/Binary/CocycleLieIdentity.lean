module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CocycleSecondDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryCocycleInfinitesimal_lie_identity
    (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (identity : ∀ first second, cocycle (first * second) = cocycle first +
      binaryCohomologicalRepresentation cusp degree first (cocycle second))
    (first second : Matrix (Fin 2) (Fin 2) ℝ)
    (first_traceless : Matrix.trace first = 0) (second_traceless : Matrix.trace second = 0) :
    binaryCocycleInfinitesimal cusp degree cocycle smooth finite (first * second - second * first) =
      binaryCohomologicalDerivedOperator cusp degree first
        (binaryCocycleInfinitesimal cusp degree cocycle smooth finite second) -
      binaryCohomologicalDerivedOperator cusp degree second
        (binaryCocycleInfinitesimal cusp degree cocycle smooth finite first) := by
  have forward := binaryCocycleInfinitesimal_composition cusp degree cocycle smooth finite identity first second first_traceless
  have backward := binaryCocycleInfinitesimal_composition cusp degree cocycle smooth finite identity second first second_traceless
  have symmetric := (binaryCocycleHilbertFamily_contDiffAt cusp degree cocycle smooth 1).isSymmSndFDerivAt_of_omega.eq first second
  simp only [Units.val_one] at symmetric
  funext monomial
  apply Subtype.ext
  rw [← congrFun (binaryCocycleHilbertFamily_identity_derivative cusp degree cocycle smooth finite
    (first * second - second * first)) monomial]
  change _ =
    (binaryCohomologicalDerivedOperator cusp degree first
      (binaryCocycleInfinitesimal cusp degree cocycle smooth finite second) monomial).val -
    (binaryCohomologicalDerivedOperator cusp degree second
      (binaryCocycleInfinitesimal cusp degree cocycle smooth finite first) monomial).val
  rw [congrFun forward monomial, congrFun backward monomial, map_sub, symmetric]
  simp only [Pi.add_apply, Pi.sub_apply]
  abel

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
