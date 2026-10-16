module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Mixed.Operator

@[expose] public section



/-! Degree-0 adjointness: `symmetricExterior n 0` and `symmetricContraction n 0` are mutually
adjoint, first at the basepoint (via the orthogonal `tangentFrame` basis and the symmetric-operator
adjointness of `infinitesimal`), then transported to every point by the project's generic
real-frame transport machinery. No alternating-tensor-specific machinery (as used by the degree-1/2
basepoint adjoints) is needed at degree 0, since a degree-0 form carries no alternating structure. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SmoothCoveringDeRham
open ContinuousAlternatingMap

/-- Basepoint adjointness between the degree-0 symmetric exterior derivative and the degree-0
symmetric contraction, via the orthogonal `tangentFrame` basis and `infinitesimal`'s
self-adjointness on symmetric directions (the same fact `CasimirBound.lean` already uses). -/
theorem symmetricExterior_zero_basepoint_adjoint (n : ℕ) (a : FormValue n 0) (b : FormValue n 1) :
    formPairing n 1 (coordinateChart basepoint) (symmetricExterior n 0 (coordinateChart basepoint) a) b =
      formPairing n 0 (coordinateChart basepoint) a (symmetricContraction n 0 (coordinateChart basepoint) b) := by
  have hR : (symmetricContraction n 0 (coordinateChart basepoint) b ![]).val =
      ∑ i : Fin 5, tangentWeight i •
        ((1 / 2 : ℝ) • infinitesimal (tangentFrame i) (b ![baseFrame i]).val) := by
    rw [symmetricContraction_basepoint_frame]
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    apply Finset.sum_congr rfl
    intro i _
    have hcf : coefficientFormMap (symmetricPart n (coordinateChart basepoint) (baseFrame i)) 0
        (b.curryLeft (baseFrame i)) ![] =
        symmetricPart n (coordinateChart basepoint) (baseFrame i) (b ![baseFrame i]) := rfl
    rw [hcf, symmetricPart_baseFrame]
    simp only [_root_.smul_apply, infinitesimalCLM_apply, Submodule.coe_smul, coefficientInfinitesimal_apply]
  rw [formPairing_basepoint_one, formPairing_basepoint_zero, hR, _root_.map_sum]
  simp only [onePairing, baseOneCoordinates, symmetricExterior_zero_basepoint, _root_.map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [infinitesimal_symmetric_adjoint (tangentFrame i) (tangentFrame_mem i).1]

/-- Transport of the degree-0 adjointness from the basepoint to every point of the positive cone,
mirroring `symmetricExterior_one_adjoint`'s proof via the generic real-frame transport machinery. -/
theorem symmetricExterior_zero_adjoint (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n 0) (b : FormValue n 1) :
    formPairing n 1 x (symmetricExterior n 0 x a) b =
      formPairing n 0 x a (symmetricContraction n 0 x b) := by
  obtain ⟨g,hg,he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let c := realFormPullback n 0 g y a
  let d := realFormPullback n 1 g y b
  have hc := realFormPullback_spec n 0 g y a
  have hd := realFormPullback_spec n 1 g y b
  calc
    formPairing n 1 (coordinateAction g y) (symmetricExterior n 0 (coordinateAction g y) a) b =
        formPairing n 1 y (symmetricExterior n 0 y c) d :=
      formPairing_real n 1 g hg y hy _ _ _ _ (symmetricExterior_real n 0 g hg y hy a c hc) hd
    _ = formPairing n 0 y c (symmetricContraction n 0 y d) :=
      symmetricExterior_zero_basepoint_adjoint n c d
    _ = formPairing n 0 (coordinateAction g y) a (symmetricContraction n 0 (coordinateAction g y) b) :=
      (formPairing_real n 0 g hg y hy _ _ _ _ hc (symmetricContraction_real n 0 g hg y hy b d hd)).symm

end TernaryPeriodPolynomials.Argument.Coercivity
