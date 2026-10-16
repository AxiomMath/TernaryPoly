module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricSections
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Regularity

@[expose] public section


/-! Exact interaction of the genuine tensor connection with coefficient maps and insertion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy
open SymmetricSpaceCharts SmoothCoveringDeRham ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

theorem tangentFormAction_add (n k : ℕ) (x u : Coordinates) (a b : FormValue n k) :
    tangentFormAction n k x u (a + b) = tangentFormAction n k x u a + tangentFormAction n k x u b := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [tangentFormAction_apply, ContinuousAlternatingMap.add_apply, Finset.sum_add_distrib]

theorem tangentFormAction_smul (n k : ℕ) (x u : Coordinates) (c : ℝ) (a : FormValue n k) :
    tangentFormAction n k x u (c • a) = c • tangentFormAction n k x u a := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [tangentFormAction_apply, ContinuousAlternatingMap.smul_apply, Finset.smul_sum]

theorem tangentFormAction_coefficientFormMap (n k : ℕ) (x u : Coordinates)
    (L : Coefficients n →L[ℝ] Coefficients n) (a : FormValue n k) :
    tangentFormAction n k x u (coefficientFormMap L k a) =
      coefficientFormMap L k (tangentFormAction n k x u a) := by
  apply ContinuousAlternatingMap.ext
  intro v
  change tangentFormAction n k x u (coefficientFormMap L k a) v = L (tangentFormAction n k x u a v)
  rw [tangentFormAction_apply, tangentFormAction_apply, _root_.map_sum]
  rfl

theorem coefficientFormMap_insertion (n k : ℕ) (L : Coefficients n →L[ℝ] Coefficients n)
    (a : FormValue n (k + 1)) (v : Coordinates) :
    coefficientFormMap L k (insertion n k v a) = insertion n k v (coefficientFormMap L (k + 1) a) := by
  apply ContinuousAlternatingMap.ext
  intro w
  rfl

/-- Differentiating tangent slots separates the inserted slot from all remaining slots. -/
theorem tangentFormAction_insertion (n k : ℕ) (x u v : Coordinates) (a : FormValue n (k + 1)) :
    insertion n k v (tangentFormAction n (k + 1) x u a) =
      insertion n k (tangentConnection x u v) a + tangentFormAction n k x u (insertion n k v a) := by
  apply ContinuousAlternatingMap.ext
  intro w
  change tangentFormAction n (k + 1) x u a (Fin.cons v w) =
    a (Fin.cons (tangentConnection x u v) w) + tangentFormAction n k x u (insertion n k v a) w
  rw [tangentFormAction_apply, tangentFormAction_apply, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
  rfl

end TernaryPoly.PolynomialFormConnection
