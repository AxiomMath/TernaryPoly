module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Cancellation

@[expose] public section



/-! Degree-6 triviality. `Coordinates` is 5-dimensional, so any alternating map on six
`Coordinates`-arguments vanishes (`AlternatingMap.map_linearDependent`, since six vectors in a
5-dimensional space are never linearly independent). This forces `FormValue n 6`, and hence
`Form`/`EquivariantForm`/`Core` at level 6, to be the trivial module. Consequently, for
`a : Core n 5`, `compactDifferential ... 5 a : Core n 6` is identically `0`: the `‖Da‖²`
summand of Proposition C.1's degree-5 clause vanishes with no basepoint/transport argument
needed, reducing that clause to the one-sided bound `c‖a‖² ≤ ‖D*a‖²`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Six vectors in the 5-dimensional `Coordinates` are never linearly independent. -/
theorem not_linearIndependent_six (v : Fin 6 → Coordinates) : ¬ LinearIndependent ℝ v := by
  intro hli
  have hcard := hli.fintype_card_le_finrank
  rw [finrank_coordinates, Fintype.card_fin] at hcard
  omega

/-- `FormValue n 6` is the trivial module: any alternating 6-form on the 5-dimensional
`Coordinates` vanishes identically. -/
theorem formValue_six_eq_zero (n : ℕ) (f : FormValue n 6) : f = 0 :=
  ContinuousAlternatingMap.ext fun v =>
    AlternatingMap.map_linearDependent f.toAlternatingMap v (not_linearIndependent_six v)

/-- Any `Form`-level 6-form, on any domain `s`, is the zero form. -/
theorem form_six_eq_zero (n : ℕ) {s : Set Coordinates} (w : Form (F := Coefficients n) s 6) :
    w = 0 :=
  Form.ext fun x _ => formValue_six_eq_zero n (w.val x)

/-- Any equivariant degree-6 form is zero. -/
theorem equivariantForm_six_eq_zero (n : ℕ) (a : EquivariantForm (deckRepresentation n) univ 6) :
    a = 0 :=
  Subtype.ext (form_six_eq_zero n a.val)

/-- `Core n 6` is the trivial module. -/
theorem core_six_eq_zero (n : ℕ) (b : Core n 6) : b = 0 :=
  Subtype.ext (equivariantForm_six_eq_zero n b.val)

/-- The degree-5 differential of any compactly-supported degree-5 core form is identically
zero. -/
theorem compactDifferential_five_eq_zero (n : ℕ) (a : Core n 5) :
    compactDifferential (deckRepresentation n) isOpen_univ 5 a = 0 :=
  core_six_eq_zero n _

/-- Consequently the `‖Da‖` summand of the degree-5 clause vanishes identically. -/
theorem norm_compactDifferential_five_eq_zero (n : ℕ) (a : Core n 5) :
    ‖inclusion n 6 (compactDifferential (deckRepresentation n) isOpen_univ 5 a)‖ = 0 := by
  have h1 : inclusion n 6 (compactDifferential (deckRepresentation n) isOpen_univ 5 a) = 0 :=
    (congrArg (inclusion n 6) (compactDifferential_five_eq_zero n a)).trans (inclusion n 6).map_zero
  rw [h1, norm_zero]

end TernaryPeriodPolynomials.Argument.Coercivity
