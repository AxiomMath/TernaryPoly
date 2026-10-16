module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowDegreeCoercivity

@[expose] public section


/-! Strictly positive finite-dimensional coefficient coercivity for every positive degree. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

/-- The actual algebraic degree-two Hodge operator for positive polynomial coefficients
has a positive lower bound, uniform over all forms of each fixed degree. -/
theorem homogeneousHodgeTwo_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : homogeneousTwoForms n,
      c * twoPairing a.val a.val ≤ twoPairing (homogeneousHodgeTwo n a).val a.val := by
  by_cases h4 : 4 ≤ n
  · exact homogeneousHodgeTwo_coercive_high_degree h4
  have hs : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hs with rfl | rfl | rfl
  · exact homogeneousHodgeTwo_coercive_degree1
  · exact homogeneousHodgeTwo_coercive_degree2
  · exact homogeneousHodgeTwo_coercive_degree3

end TernaryPoly.SL3PolynomialCoercivity
