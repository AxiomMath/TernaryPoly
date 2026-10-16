module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LowCurrent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Coordinates

@[expose] public section


/-! The genuine low-degree exterior current equations are the ordinary weak gradient equations. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts
open SmoothLocalDeRham
open scoped Distributions

/-- The actual exterior current derivative of a zero-form is its coefficient-valued weak gradient. -/
theorem formWeakExterior_zero (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (T : ValuedWeak (V := Coefficients n) Ω) :
    formWeakOneValue n Ω (formWeakExterior n 0 Ω (zeroFormWeak n Ω T)) =
      valuedWeakGradient Ω T := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro φ
  change oneEquiv.symm (formWeakExterior n 0 Ω (zeroFormWeak n Ω T) φ) v =
    valuedWeakDerivative Ω v T φ
  rw [valuedWeakDerivative_coordinates 5]
  simp only [formWeakExterior_apply, zeroFormWeak_apply, ← map_neg zeroEquiv, map_sum,
    _root_.sum_apply, symbol_zero_value, LinearMap.sum_apply,
    LinearMap.smul_apply, valuedWeakDerivative_apply]

/-- Evaluating the actual degree-one exterior derivative gives the literal antisymmetric weak
first derivatives of the coefficient-valued one-form. -/
theorem formWeakExterior_one_apply (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n 1 Ω) (φ : 𝓓(Ω, ℝ)) (u v : Coordinates) :
    formWeakExterior n 1 Ω W φ ![u,v] =
      valuedWeakDerivative Ω u (formWeakOneValue n Ω W v) φ -
      valuedWeakDerivative Ω v (formWeakOneValue n Ω W u) φ := by
  rw [valuedWeakDerivative_coordinates 5, valuedWeakDerivative_coordinates 5]
  simp only [formWeakExterior_apply, ContinuousAlternatingMap.sum_apply, symbol_one_value]
  simp only [map_neg, _root_.neg_apply, Finset.sum_sub_distrib,
    LinearMap.sum_apply, LinearMap.smul_apply, valuedWeakDerivative_apply,
    formWeakOneValue_apply]

/-- Closedness of an actual one-form current is exactly the actual valued weak closedness
condition used by the compact-test Poincare theorem. -/
theorem formWeakExterior_one_eq_zero_iff (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n 1 Ω) : formWeakExterior n 1 Ω W = 0 ↔
      ∀ u v, valuedWeakDerivative Ω u (formWeakOneValue n Ω W v) =
        valuedWeakDerivative Ω v (formWeakOneValue n Ω W u) := by
  constructor
  · intro h u v
    apply LinearMap.ext
    intro φ
    apply sub_eq_zero.mp
    exact (formWeakExterior_one_apply n Ω W φ u v).symm.trans
      (congrArg (fun Z : FormWeak n 2 Ω => Z φ ![u,v]) h)
  · intro h
    apply LinearMap.ext
    intro φ
    apply ContinuousAlternatingMap.ext
    intro v
    have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, formWeakExterior_one_apply, h]
    exact sub_self _

end TernaryPoly.PolynomialFormWeakSmooth
