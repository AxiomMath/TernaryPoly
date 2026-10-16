module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ComplexExactness
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section


/-! Energy estimates in the usual squared-norm form imply actual exactness. -/
namespace TernaryPoly.HilbertClosedOperator

open scoped InnerProductSpace LinearPMap
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [NormedSpace ℝ G]
variable [CompleteSpace E] [CompleteSpace F]

/-- The standard positive energy lower bound gives unreduced exactness. -/
theorem exact_of_energy (S : E →ₗ.[ℝ] F) (T : F →ₗ.[ℝ] G)
    (hS : S.IsClosed) (hdS : Dense (S.domain : Set E)) (hT : T.IsClosed)
    (hcomplex : ∀ u : S.domain, S u ∈ kernel T)
    (c : ℝ) (hc : 0 < c)
    (henergy : ∀ x : T.domain, ∀ hx : (x : F) ∈ S†.domain,
      c * ‖(x : F)‖ ^ 2 ≤ ‖T x‖ ^ 2 + ‖S† ⟨(x : F), hx⟩‖ ^ 2) :
    (kernel T : Set F) = Set.range S := by
  apply exact_of_coercive S T hS hdS hT hcomplex (1 / Real.sqrt c)
  intro x hx
  have h := henergy x hx
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hs2 := Real.sq_sqrt hc.le
  have hnorm : Real.sqrt c * ‖(x : F)‖ ≤ ‖T x‖ + ‖S† ⟨(x : F), hx⟩‖ := by
    apply (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _))
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, hs2]
    nlinarith [mul_nonneg (norm_nonneg (T x)) (norm_nonneg (S† ⟨(x : F), hx⟩))]
  calc ‖(x : F)‖ = (1 / Real.sqrt c) * (Real.sqrt c * ‖(x : F)‖) := by
         field_simp
       _ ≤ (1 / Real.sqrt c) * (‖T x‖ + ‖S† ⟨(x : F), hx⟩‖) :=
         mul_le_mul_of_nonneg_left hnorm (by positivity)

end TernaryPoly.HilbertClosedOperator
