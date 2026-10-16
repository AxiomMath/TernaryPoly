module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Current
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Derivative

@[expose] public section

/-! The actual exterior-symbol differential of genuine form-valued compact-test currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts
open scoped Distributions

/-- The literal exterior differential of a form-valued current, using the genuine constant symbols. -/
def formWeakExterior (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates) (W : FormWeak n k Ω) :
    FormWeak n (k+1) Ω :=
  ∑ d : Fin 5, (symbol n k d).toLinearMap.comp (valuedWeakDerivative Ω (Pi.single d 1) W)

@[simp] theorem formWeakExterior_apply (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n k Ω) (φ : 𝓓(Ω, ℝ)) :
    formWeakExterior n k Ω W φ =
      ∑ d : Fin 5, symbol n k d (-W (TestFunction.lineDerivCLM ℝ (Pi.single d 1) φ)) := by
  simp only [formWeakExterior, LinearMap.sum_apply, LinearMap.comp_apply, valuedWeakDerivative_apply]
  rfl

/-- Actual symbol coordinates are exactly their true finite matrix expansion. -/
theorem formWeakSymbol_coordinate (n k : ℕ) (d : Fin 5) (a : FormValue n k) (j : Index n (k+1)) :
    coordinates n (k+1) (symbol n k d a) j =
      ∑ i : Index n k, symbolMatrix n k d j i * coordinates n k a i :=
  congrFun (symbolMatrix_apply n k d a).symm j

/-- The actual form-valued differential has exactly the proved scalar-current
exterior-symbol coordinate formula. -/
theorem formWeakCoordinates_exterior (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n k Ω) (j : Index n (k+1)) :
    formWeakCoordinates n (k+1) Ω (formWeakExterior n k Ω W) j =
      ∑ i : Index n k, ∑ d : Fin 5, symbolMatrix n k d j i •
        scalarWeakDerivative Ω (Pi.single d 1) (formWeakCoordinates n k Ω W i) := by
  apply LinearMap.ext
  intro φ
  simp only [formWeakCoordinates_apply, formWeakExterior_apply, map_sum, Finset.sum_apply,
    formWeakSymbol_coordinate, map_neg, Pi.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    scalarWeakDerivative_apply, smul_eq_mul]
  simp only [← Finset.sum_neg_distrib, mul_neg]
  exact Finset.sum_comm (f := fun (d : Fin 5) (i : Index n k) =>
    -(symbolMatrix n k d j i * (coordinates n k (W (TestFunction.lineDerivCLM ℝ (Pi.single d 1) φ))) i))

end TernaryPoly.PolynomialFormWeakSmooth
