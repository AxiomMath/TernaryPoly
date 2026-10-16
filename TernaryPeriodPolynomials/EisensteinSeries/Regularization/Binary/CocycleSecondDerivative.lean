module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.IdentityLine
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalDerivedOperator
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CocycleDifferentialEquation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryCocycleInfinitesimal_composition
    (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (identity : ∀ first second, cocycle (first * second) = cocycle first +
      binaryCohomologicalRepresentation cusp degree first (cocycle second))
    (first second : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace first = 0) :
    (fun monomial => (binaryCohomologicalDerivedOperator cusp degree first
      (binaryCocycleInfinitesimal cusp degree cocycle smooth finite second) monomial).val) =
      fderiv ℝ (binaryCocycleHilbertFamily cusp degree cocycle) 1 (first * second) +
        fderiv ℝ (fderiv ℝ (binaryCocycleHilbertFamily cusp degree cocycle)) 1 first second := by
  let family := binaryCocycleHilbertFamily cusp degree cocycle
  have action_derivative := binaryCohomologicalHilbertAction_path_hasDerivAt cusp degree
    (binaryCocycleInfinitesimal cusp degree cocycle smooth finite second)
    (binaryIdentityLine first) first 0 (binaryIdentityLine_zero first)
    (binaryIdentityLine_entry_hasDerivAt first) traceless
  rw [← binaryCocycleHilbertFamily_identity_derivative cusp degree cocycle smooth finite second] at action_derivative
  have line : HasDerivAt (fun parameter : ℝ => 1 + parameter • first) first 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const first).const_add (1 : Matrix (Fin 2) (Fin 2) ℝ) using 1
    simp
  have family_smooth := binaryCocycleHilbertFamily_contDiffAt cusp degree cocycle smooth 1
  have derivative_smooth : ContDiffAt ℝ ⊤ (fderiv ℝ family) 1 := family_smooth.fderiv_right le_top
  have second_derivative := (derivative_smooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 line (by simp)
  let right : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ second)
  have right_derivative := right.hasFDerivAt.comp_hasDerivAt 0 line
  have computed := second_derivative.clm_apply right_derivative
  have near :
      (fun parameter : ℝ =>
        fderiv ℝ family (1 + parameter • first) ((1 + parameter • first) * second)) =ᶠ[nhds 0]
      (fun parameter => binaryCohomologicalHilbertAction cusp degree (binaryIdentityLine first parameter)
        (fderiv ℝ family 1 second)) := by
    filter_upwards [binaryIdentityLine_val_eventuallyEq first] with parameter value
    rw [← value]
    exact binaryCocycle_left_differential_equation cusp degree cocycle smooth identity
      (binaryIdentityLine first parameter) second
  have computed' : HasDerivAt
      (fun parameter : ℝ =>
        fderiv ℝ family (1 + parameter • first) ((1 + parameter • first) * second))
      (fderiv ℝ family 1 (first * second) + fderiv ℝ (fderiv ℝ family) 1 first second) 0 := by
    convert! computed using 1
    simp only [Function.comp_def, zero_smul, add_zero]
    change _ = fderiv ℝ (fderiv ℝ family) 1 first (1 * second) + fderiv ℝ family 1 (first * second)
    rw [one_mul]
    exact add_comm _ _
  exact action_derivative.unique (computed'.congr_of_eventuallyEq near.symm)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
