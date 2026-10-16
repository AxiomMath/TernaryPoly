module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tangent.Sections
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Symbol

@[expose] public section



/-! Genuine exterior multiplication by the symmetric coefficient connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open SmoothCoveringDeRham ContinuousAlternatingMap
open scoped ContDiff Matrix.Norms.Elementwise

/-- Apply the actual symmetric connection to a genuine coefficient form, retaining a tangent slot. -/
def symmetricFormDerivative (n k : ℕ) (x : Coordinates) (a : FormValue n k) : Coordinates →L[ℝ] FormValue n k :=
  (show Coordinates →ₗ[ℝ] FormValue n k from
    { toFun v := (symmetricPart n x v).compContinuousAlternatingMap a
      map_add' u v := by
        apply ContinuousAlternatingMap.ext
        intro z
        change symmetricPart n x (u + v) (a z) = symmetricPart n x u (a z) + symmetricPart n x v (a z)
        rw [symmetricPart_add]
        rfl
      map_smul' c v := by
        apply ContinuousAlternatingMap.ext
        intro z
        change symmetricPart n x (c • v) (a z) = c • symmetricPart n x v (a z)
        rw [symmetricPart_smul]
        rfl }).toContinuousLinearMap

@[simp] theorem symmetricFormDerivative_apply (n k : ℕ) (x v : Coordinates) (a : FormValue n k)
    (z : Fin k → Coordinates) : symmetricFormDerivative n k x a v z = symmetricPart n x v (a z) := rfl

/-- Exterior multiplication by Ψ, using exactly Mathlib's exterior-derivative alternation. -/
def symmetricExterior (n k : ℕ) (x : Coordinates) (a : FormValue n k) : FormValue n (k + 1) :=
  alternatizeUncurryFin (symmetricFormDerivative n k x a)

theorem symmetricExterior_apply (n k : ℕ) (x : Coordinates) (a : FormValue n k)
    (v : Fin (k + 1) → Coordinates) :
    symmetricExterior n k x a v = ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) •
      symmetricPart n x (v i) (a (Fin.removeNth i v)) := by
  exact alternatizeUncurryFin_apply (symmetricFormDerivative n k x a) v

/-- The actual symmetric exterior term in the same coordinate symbols as the flat differential. -/
theorem symmetricExterior_symbol (n k : ℕ) (x : Coordinates) (a : FormValue n k) :
    symmetricExterior n k x a = ∑ d : Fin 5, PolynomialFormCoordinates.symbol n k d
      (coefficientFormMap (symmetricPart n x (Pi.single d 1)) k a) := by
  change (alternatizeUncurryFinCLM ℝ Coordinates (Coefficients n) (n := k)) (symmetricFormDerivative n k x a) = _
  rw [PolynomialFormCoordinates.derivative_decomposition n k (symmetricFormDerivative n k x a),
    PolynomialFormCoordinates.clm_map_sum]
  rfl

/-- The genuine exterior covariant derivative on coefficient forms in the flat trivialization. -/
def covariantExterior (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) : FormValue n (k + 1) :=
  extDeriv w x - symmetricExterior n k x (w x)

theorem flatExterior_eq_covariant_add_symmetric (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) :
    extDeriv w x = covariantExterior n k w x + symmetricExterior n k x (w x) := by
  simp [covariantExterior]

/-- The exterior covariant derivative is literally the alternation of d plus the Γ. -/
theorem covariantExterior_symbol (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) :
    covariantExterior n k w x = ∑ d : Fin 5, PolynomialFormCoordinates.symbol n k d
      (fderiv ℝ w x (Pi.single d 1) + coefficientFormMap (connectionMatrix n x (Pi.single d 1)) k (w x)) := by
  rw [covariantExterior, PolynomialFormCoordinates.extDeriv_symbol, symmetricExterior_symbol,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← PolynomialFormCoordinates.clm_map_sub]
  congr 1
  apply ContinuousAlternatingMap.ext
  intro v
  show (fderiv ℝ w x (Pi.single d 1)) v -
      (PolynomialFormConnection.symmetricPart n x (Pi.single d 1)) (w x v) =
    (fderiv ℝ w x (Pi.single d 1)) v +
      (-(PolynomialFormConnection.symmetricPart n x (Pi.single d 1))) (w x v)
  rw [_root_.neg_apply, sub_eq_add_neg]

theorem symmetricExterior_one_apply (n : ℕ) (x : Coordinates) (a : FormValue n 1) (u v : Coordinates) :
    symmetricExterior n 1 x a ![u, v] = symmetricPart n x u (a ![v]) - symmetricPart n x v (a ![u]) := by
  have h : Fin.removeNth (1 : Fin 2) ![u, v] = ![u] := by
    ext j; fin_cases j; rfl
  simp [symmetricExterior_apply, Fin.sum_univ_two, h, sub_eq_add_neg]

theorem symmetricExterior_two_apply (n : ℕ) (x : Coordinates) (a : FormValue n 2) (u v w : Coordinates) :
    symmetricExterior n 2 x a ![u, v, w] =
      symmetricPart n x u (a ![v, w]) - symmetricPart n x v (a ![u, w]) + symmetricPart n x w (a ![u, v]) := by
  have h1 : Fin.removeNth (1 : Fin 3) ![u, v, w] = ![u, w] := by
    ext j; fin_cases j <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u, v, w] = ![u, v] := by
    ext j; fin_cases j <;> rfl
  simp [symmetricExterior_apply, Fin.sum_univ_succ, h1, h2, sub_eq_add_neg, add_assoc]

/-- No basepoint scale is suppressed in degree one. -/
theorem symmetricExterior_one_basepoint (n : ℕ) (a : FormValue n 1) (i j : Fin 5) :
    (symmetricExterior n 1 (coordinateChart basepoint) a ![baseFrame i, baseFrame j]).val =
      (1/2 : ℝ) • exteriorOne (fun r => (a ![baseFrame r]).val) i j := by
  rw [symmetricExterior_one_apply, symmetricPart_baseFrame, symmetricPart_baseFrame]
  simp only [_root_.smul_apply, infinitesimalCLM_apply, Submodule.coe_sub, Submodule.coe_smul,
    coefficientInfinitesimal_apply, exteriorOne]
  module

/-- The same exact one-half factor applies to the actual degree-two exterior term. -/
theorem symmetricExterior_two_basepoint (n : ℕ) (a : FormValue n 2) (i j l : Fin 5) :
    (symmetricExterior n 2 (coordinateChart basepoint) a ![baseFrame i, baseFrame j, baseFrame l]).val =
      (1/2 : ℝ) • exteriorTwo (baseTwoCoordinates a) i j l := by
  rw [symmetricExterior_two_apply, symmetricPart_baseFrame, symmetricPart_baseFrame, symmetricPart_baseFrame]
  simp only [_root_.smul_apply, infinitesimalCLM_apply, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    coefficientInfinitesimal_apply, exteriorTwo, baseTwoCoordinates]
  module

end TernaryPoly.PolynomialFormGeometricEnergy
