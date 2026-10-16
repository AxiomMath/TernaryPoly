module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Conjugation

@[expose] public section

/-! Actual deck transport of the coefficient metric connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open SymmetricSpaceArithmeticProper
open scoped ContDiff Matrix.Norms.Elementwise

/-- The genuine determinant-normalized form transforms by literal arithmetic congruence. -/
theorem coordinateForm_deck (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    coordinateForm (coordinateAction (deckMatrix g) x) = conjugate (deckMatrix g) (coordinateForm x) := by
  rw [coordinateForm, reconstruct_coordinateAction (deckMatrix g) x hx]
  change determinantNormalize ((conjugate (deckMatrix g) (reconstruct x)).trace⁻¹ •
    conjugate (deckMatrix g) (reconstruct x)) = _
  rw [determinantNormalize_smul _ (inv_pos.mpr (conjugate_positive (deckMatrix g) _ hx).trace_pos)
    _ (conjugate_positive (deckMatrix g) _ hx)]
  exact determinantNormalize_integral_conjugate (deckInclusion g) (reconstruct x)

/-- Differentiating the actual deck transformation gives the transformed normalized tangent. -/
theorem formDerivative_deck (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) :
    formDerivative (coordinateAction (deckMatrix g) x) (fderiv ℝ (coordinateAction (deckMatrix g)) x v) =
      conjugate (deckMatrix g) (formDerivative x v) := by
  have hF := (((contDiffOn_coordinateAction (deckMatrix g) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hQ := coordinateForm_differentiable (coordinateAction (deckMatrix g) x)
    (coordinateAction_mem (deckMatrix g) x hx)
  have hl := hQ.hasFDerivAt.comp x hF.hasFDerivAt
  have hr := (congruenceCLM (deckMatrix g)).hasFDerivAt.comp x (coordinateForm_differentiable x hx).hasFDerivAt
  have hL : HasFDerivAt (fun y => conjugate (deckMatrix g) (coordinateForm y))
      ((fderiv ℝ coordinateForm (coordinateAction (deckMatrix g) x)).comp
        (fderiv ℝ (coordinateAction (deckMatrix g)) x)) x := by
    apply hl.congr_of_eventuallyEq
    filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
    exact (coordinateForm_deck g y hy).symm
  have he := congrArg (fun L => L v) (hL.unique hr)
  convert! he using 1

/-- Right logarithmic differentials transform by similarity, using actual unit inverses. -/
theorem right_inverse_congruence_tangent (g S : Matˣ) (U : Mat) :
    ((g : Mat) * U * star (g : Mat)) * (↑(g * S * star g) : Mat)⁻¹ =
      (g : Mat) * (U * (↑S⁻¹ : Mat)) * (↑g⁻¹ : Mat) := by
  rw [← Matrix.coe_units_inv (g * S * star g)]
  simp [-Matrix.coe_units_inv, mul_assoc]
  have hs : star (g : Mat) * star (↑g⁻¹ : Mat) = 1 := by
    rw [← star_mul]
    simp
  rw [← mul_assoc (star (g : Mat)) (star (↑g⁻¹ : Mat)), hs, one_mul]

theorem logarithmicForm_deck (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) :
    logarithmicForm (coordinateAction (deckMatrix g) x) (fderiv ℝ (coordinateAction (deckMatrix g)) x v) =
      (deckMatrix g).val * logarithmicForm x v * (deckMatrix g).val⁻¹ := by
  rw [logarithmicForm, formDerivative_deck g x hx v, coordinateForm_deck g x hx]
  obtain ⟨S, hS⟩ := (coordinateForm_positive x hx).isUnit
  have h := right_inverse_congruence_tangent (deckMatrix g) S (formDerivative x v)
  simpa only [conjugate, Units.val_mul, Units.coe_star, Matrix.coe_units_inv, logarithmicForm, ← hS] using h

/-- The deck representation is the same actual inverse substitution used above. -/
theorem deckRepresentation_eq_substitution (n : ℕ) (g : DeckGroup) (p : Coefficients n) :
    deckRepresentation n g p = coefficientSubstitution n (deckMatrix g).val⁻¹ p := by
  apply Subtype.ext
  simp only [deckRepresentation_apply, coefficientSubstitution_apply, GeneralLinearGroup.coe_inv]

/-- Actual equivariance of the symmetric coefficient connection under deck transport. -/
theorem symmetricPart_deck (n : ℕ) (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (p : Coefficients n) :
    symmetricPart n (coordinateAction (deckMatrix g) x)
      (fderiv ℝ (coordinateAction (deckMatrix g)) x v) (deckRepresentation n g p) =
      deckRepresentation n g (symmetricPart n x v p) := by
  simp only [symmetricPart, _root_.smul_apply, infinitesimalCLM_apply, map_smul]
  rw [logarithmicForm_deck g x hx v, deckRepresentation_eq_substitution,
    coefficientInfinitesimal_conjugation n (deckMatrix g).val (logarithmicForm x v) (deckMatrix g).isUnit,
    deckRepresentation_eq_substitution]

/-- Consequently the metric connection matrix itself has the exact deck covariance law. -/
theorem connectionMatrix_deck (n : ℕ) (g : DeckGroup) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (p : Coefficients n) :
    connectionMatrix n (coordinateAction (deckMatrix g) x)
      (fderiv ℝ (coordinateAction (deckMatrix g)) x v) (deckRepresentation n g p) =
      deckRepresentation n g (connectionMatrix n x v p) := by
  simp only [connectionMatrix, _root_.neg_apply, map_neg, symmetricPart_deck n g x hx v p]

end TernaryPoly.PolynomialFormConnection
