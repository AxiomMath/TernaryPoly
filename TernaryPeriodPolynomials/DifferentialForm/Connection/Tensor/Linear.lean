module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.Algebra

@[expose] public section


/-! The actual tensor connection is a linear zero-order term, with genuine sum and product rules. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

def tangentFormActionCLM (n k : ℕ) (x u : Coordinates) : FormValue n k →L[ℝ] FormValue n k :=
  (show FormValue n k →ₗ[ℝ] FormValue n k from
    { toFun := tangentFormAction n k x u
      map_add' := tangentFormAction_add n k x u
      map_smul' := fun c a => tangentFormAction_smul n k x u c a }).toContinuousLinearMap

@[simp] theorem tangentFormActionCLM_apply (n k : ℕ) (x u : Coordinates) (a : FormValue n k) :
    tangentFormActionCLM n k x u a = tangentFormAction n k x u a := rfl

/-- The actual induced tensor connection coefficient, on the genuine form fiber. -/
def tensorConnectionEndomorphism (n k : ℕ) (x u : Coordinates) : FormValue n k →L[ℝ] FormValue n k :=
  coefficientFormMap (connectionMatrix n x u) k - tangentFormActionCLM n k x u

theorem covariantFormDerivative_eq (n k : ℕ) (w : Coordinates → FormValue n k) (x u : Coordinates) :
    covariantFormDerivative n k w x u = fderiv ℝ w x u + tensorConnectionEndomorphism n k x u (w x) := by
  change fderiv ℝ w x u + coefficientFormMap (connectionMatrix n x u) k (w x) -
    tangentFormAction n k x u (w x) =
    fderiv ℝ w x u + (coefficientFormMap (connectionMatrix n x u) k (w x) -
      tangentFormAction n k x u (w x))
  abel

theorem covariantFormDerivative_sum {ι : Type*} [Fintype ι] (n k : ℕ)
    (w : ι → Coordinates → FormValue n k) (x u : Coordinates) (hw : ∀ i, DifferentiableAt ℝ (w i) x) :
    covariantFormDerivative n k (fun y => ∑ i, w i y) x u = ∑ i, covariantFormDerivative n k (w i) x u := by
  have hd : fderiv ℝ (fun y => ∑ i, w i y) x = ∑ i, fderiv ℝ (w i) x := by
    convert! fderiv_fun_sum (𝕜 := ℝ) (A := w) (x := x)
      (u := Finset.univ) (fun i _ => by convert! hw i using 1) using 1
  simp only [covariantFormDerivative_eq, hd, _root_.sum_apply,
    map_sum, Finset.sum_add_distrib]

theorem covariantFormDerivative_smul (n k : ℕ) (f : Coordinates → ℝ) (w : Coordinates → FormValue n k)
    (x u : Coordinates) (hf : DifferentiableAt ℝ f x) (hw : DifferentiableAt ℝ w x) :
    covariantFormDerivative n k (fun y => f y • w y) x u =
      fderiv ℝ f x u • w x + f x • covariantFormDerivative n k w x u := by
  let : IsBoundedSMul ℝ (FormValue n k) := by
    convert! (NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := FormValue n k)) using 1
  have hd : fderiv ℝ (fun y => f y • w y) x =
      f x • fderiv ℝ w x + (fderiv ℝ f x).smulRight (w x) := by
    convert! fderiv_fun_smul (𝕜 := ℝ) (F := FormValue n k) (c := f) (f := w) (x := x)
      (by convert! hf using 1) (by convert! hw using 1) using 1
  rw [covariantFormDerivative_eq, covariantFormDerivative_eq, hd]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply, map_smul]
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_add]
  abel

end TernaryPoly.PolynomialFormConnection
