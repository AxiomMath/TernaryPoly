module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.MaurerCartan

@[expose] public section


/-! Actual curvature of the coefficient metric connection, evaluated on a coefficient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- Evaluation of the actual polynomial infinitesimal action is linear in its matrix. -/
def infinitesimalAt (n : ℕ) (p : Coefficients n) : Mat →ₗ[ℝ] Coefficients n where
  toFun A := coefficientInfinitesimal n A p
  map_add' A B := coefficientInfinitesimal_add n A B p
  map_smul' c A := coefficientInfinitesimal_smul n c A p

theorem coefficientInfinitesimal_sub (n : ℕ) (A B : Mat) (p : Coefficients n) :
    coefficientInfinitesimal n (A - B) p = coefficientInfinitesimal n A p - coefficientInfinitesimal n B p :=
  map_sub (infinitesimalAt n p) A B

theorem hasDerivAt_symmetricPart_apply_line (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) :
    HasDerivAt (fun t : ℝ => symmetricPart n (x + t • u) v p)
      ((1/2 : ℝ) • coefficientInfinitesimal n (logarithmicDerivative x u v) p) 0 := by
  have hd := (((contDiffOn_logarithmicForm v x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hl := hasDerivAt_matrixField_line _ x u hd
  have hi := (infinitesimalAt n p).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hl
  have hs := hi.const_smul (1/2 : ℝ)
  convert! hs using 1

theorem symmetricPartDerivative_apply (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) :
    fderiv ℝ (fun y => symmetricPart n y v p) x u =
      (1/2 : ℝ) • coefficientInfinitesimal n (logarithmicDerivative x u v) p := by
  have hd := ((((contDiffOn_symmetricPart n v).clm_apply (contDiffOn_const (c := p)) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  exact (hasDerivAt_section_line n _ x u hd).unique (hasDerivAt_symmetricPart_apply_line n x hx u v p)

theorem connectionMatrixDerivative_apply (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) :
    fderiv ℝ (fun y => connectionMatrix n y v p) x u =
      (-1/2 : ℝ) • coefficientInfinitesimal n (logarithmicDerivative x u v) p := by
  have hd := ((((contDiffOn_connectionMatrix n v).clm_apply (contDiffOn_const (c := p)) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hs := (hasDerivAt_symmetricPart_apply_line n x hx u v p).neg
  have hs' : HasDerivAt (fun t : ℝ => connectionMatrix n (x + t • u) v p)
      ((-1/2 : ℝ) • coefficientInfinitesimal n (logarithmicDerivative x u v) p) 0 := by
    convert! hs using 1
    simp only [neg_div, neg_smul]
  exact (hasDerivAt_section_line n _ x u hd).unique hs'

/-- Literal exterior derivative plus connection commutator, evaluated on a constant coefficient. -/
def coefficientCurvature (n : ℕ) (x u v : Coordinates) (p : Coefficients n) : Coefficients n :=
  fderiv ℝ (fun y => connectionMatrix n y v p) x u -
    fderiv ℝ (fun y => connectionMatrix n y u p) x v +
    connectionMatrix n x u (connectionMatrix n x v p) - connectionMatrix n x v (connectionMatrix n x u p)

theorem connectionExteriorDerivative_apply (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) :
    fderiv ℝ (fun y => connectionMatrix n y v p) x u -
      fderiv ℝ (fun y => connectionMatrix n y u p) x v =
      (-1/2 : ℝ) • coefficientInfinitesimal n
        (logarithmicForm x u * logarithmicForm x v - logarithmicForm x v * logarithmicForm x u) p := by
  rw [connectionMatrixDerivative_apply n x hx u v p, connectionMatrixDerivative_apply n x hx v u p,
    ← smul_sub, ← coefficientInfinitesimal_sub, logarithmic_maurerCartan x hx u v]

theorem connectionMatrix_commutator_apply (n : ℕ) (x u v : Coordinates) (p : Coefficients n) :
    connectionMatrix n x u (connectionMatrix n x v p) - connectionMatrix n x v (connectionMatrix n x u p) =
      (1/4 : ℝ) • coefficientInfinitesimal n
        (logarithmicForm x u * logarithmicForm x v - logarithmicForm x v * logarithmicForm x u) p := by
  rw [coefficientInfinitesimal_commutator]
  simp only [connectionMatrix, symmetricPart, _root_.neg_apply, _root_.smul_apply,
    infinitesimalCLM_apply, map_neg, map_smul]
  module

/-- Actual curvature with the exact one-quarter normalization. -/
theorem coefficientCurvature_formula (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) :
    coefficientCurvature n x u v p = (-1/4 : ℝ) • coefficientInfinitesimal n
      (logarithmicForm x u * logarithmicForm x v - logarithmicForm x v * logarithmicForm x u) p := by
  rw [coefficientCurvature, add_sub_assoc, connectionExteriorDerivative_apply n x hx u v p,
    connectionMatrix_commutator_apply]
  module

/-- The genuine symmetric connection terms square to minus the coefficient curvature. -/
theorem coefficientCurvature_eq_neg_symmetric_commutator (n : ℕ) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (u v : Coordinates) (p : Coefficients n) :
    coefficientCurvature n x u v p =
      -(symmetricPart n x u (symmetricPart n x v p) - symmetricPart n x v (symmetricPart n x u p)) := by
  rw [coefficientCurvature_formula n x hx u v p]
  have h := connectionMatrix_commutator_apply n x u v p
  simp only [connectionMatrix, _root_.neg_apply, map_neg, neg_neg] at h
  rw [h]
  simp only [neg_div, neg_smul]

end TernaryPoly.PolynomialFormConnection
