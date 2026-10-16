module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Tensor
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Basic
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Density

@[expose] public section


/-! Evaluation of genuine continuous alternating maps in the fixed tangent coordinates. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open SymmetricSpaceCharts PolynomialCoefficientMetric
open scoped ContDiff

/-- The exact coefficient-valued form fiber already used by the smooth de Rham complex. -/
abbrev FormValue (n k : ℕ) := Coordinates [⋀^Fin k]→L[ℝ] Coefficients n

/-- The topology of the form values is the one of their operator norm. -/
theorem formValue_isNormableSpace (n k : ℕ) :
    ∃ p : Seminorm ℝ (FormValue n k), WithSeminorms (𝕜 := ℝ) (E := FormValue n k) (fun _ : Unit => p) :=
  ⟨normSeminorm ℝ (FormValue n k), norm_withSeminorms ℝ (FormValue n k)⟩

/-- Values on all ordered tuples of the actual coordinate basis. -/
def formCoordinates {n k : ℕ} (a : FormValue n k) (I : Fin k → Fin 5) : Coefficients n :=
  a (fun r => Pi.single (I r) 1)

theorem form_expansion {n k : ℕ} (a : FormValue n k) (v : Fin k → Coordinates) :
    a v = ∑ I : Fin k → Fin 5, (∏ r, v r (I r)) • formCoordinates a I := by
  have hv (r : Fin k) : v r = ∑ i : Fin 5, v r i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  calc
    a v = a (fun r => ∑ i : Fin 5, v r i • Pi.single i 1) := congrArg a (funext hv)
    _ = _ := by
      change a.toContinuousMultilinearMap.toMultilinearMap (fun r => ∑ i : Fin 5, v r i • Pi.single i 1) = _
      rw [a.toContinuousMultilinearMap.toMultilinearMap.map_sum]
      apply Finset.sum_congr rfl
      intro I _
      exact a.toContinuousMultilinearMap.toMultilinearMap.map_smul_univ _ _

theorem formCoordinates_injective (n k : ℕ) :
    Function.Injective (formCoordinates : FormValue n k → (Fin k → Fin 5) → Coefficients n) := by
  intro a b h
  ext v
  rw [form_expansion a, form_expansion b, h]

@[simp] theorem formCoordinates_zero (n k : ℕ) : formCoordinates (0 : FormValue n k) = 0 := by
  rfl

/-- Pullback by a linear map acts on ordered values through its tensor matrix. -/
theorem formCoordinates_comp {n k : ℕ} (a : FormValue n k) (L : Coordinates →L[ℝ] Coordinates) :
    formCoordinates (a.compContinuousLinearMap L) =
      matrixAction (tensorMatrix k (LinearMap.toMatrix' L.toLinearMap).transpose)
        (formCoordinates a) := by
  funext I
  change a (fun r => L (Pi.single (I r) 1)) = _
  rw [form_expansion]
  rfl

end TernaryPoly.PolynomialFormMetric
