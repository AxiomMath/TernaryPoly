module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MatrixStabilizerDomain
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IdeleSlice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixStabilizerDomain
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryStrongApproximation

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularStabilizer

def determinant (matrix : Rectangular ℚ) : stabilizer matrix →* ℚˣ :=
  GeneralLinearGroup.det.comp (stabilizer matrix).subtype

def unipotents (matrix : Rectangular ℚ) : Subgroup (stabilizer matrix) := (determinant matrix).ker

theorem exists_nonzero_second (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0)
    (zeroFirst : ∀ row, matrix row 0 = 0) : ∃ row, matrix row 1 ≠ 0 := by
  by_contra vanishing
  push Not at vanishing
  apply nonzero
  ext row column
  fin_cases column
  · exact zeroFirst row
  · exact vanishing row

theorem mem_stabilizer_iff (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0)
    (zeroFirst : ∀ row, matrix row 0 = 0) (element : BinaryRationalGL) :
    element ∈ stabilizer matrix ↔ element.val 1 0 = 0 ∧ element.val 1 1 = 1 := by
  obtain ⟨row, rowNonzero⟩ := exists_nonzero_second matrix nonzero zeroFirst
  constructor
  · intro membership
    have first := congrArg (fun value : Rectangular ℚ => value row 0) membership
    have second := congrArg (fun value : Rectangular ℚ => value row 1) membership
    simp only [Matrix.mul_apply, Fin.sum_univ_two, zeroFirst, zero_mul, zero_add] at first second
    exact ⟨(mul_eq_zero.mp first).resolve_left rowNonzero, (mul_eq_left₀ rowNonzero).mp second⟩
  · intro entries
    change matrix * element.val = matrix
    ext row column
    fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zeroFirst, entries.1, entries.2]

theorem unipotent_of_det_one (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0)
    (zeroFirst : ∀ row, matrix row 0 = 0) (element : BinaryRationalGL)
    (membership : element ∈ stabilizer matrix) (detOne : GeneralLinearGroup.det element = 1) :
    element = binaryUnipotent (element.val 0 1) := by
  obtain ⟨lowerLeft, lowerRight⟩ := (mem_stabilizer_iff matrix nonzero zeroFirst element).mp membership
  have upperLeft : element.val 0 0 = 1 := by
    have equation := congrArg Units.val detOne
    simpa only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, lowerLeft, lowerRight,
      mul_one, mul_zero, sub_zero, Units.val_one] using equation
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUnipotent, upperLeft, lowerLeft, lowerRight]

theorem conjugate_mem (matrix : Rectangular ℚ) (basis element : BinaryRationalGL) :
    element ∈ stabilizer (matrix * basis.val) ↔ basis * element * basis⁻¹ ∈ stabilizer matrix := by
  have inverse : basis.val * basis⁻¹.val = 1 := basis.val_inv
  have inverse' : basis⁻¹.val * basis.val = 1 := basis.inv_val
  constructor
  · intro membership
    change matrix * ((basis.val * element.val) * basis⁻¹.val) = matrix
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, membership, Matrix.mul_assoc, inverse, Matrix.mul_one]
  · intro membership
    have equality := congrArg (fun value : Rectangular ℚ => value * basis.val) membership
    change (matrix * ((basis.val * element.val) * basis⁻¹.val)) * basis.val = matrix * basis.val at equality
    change (matrix * basis.val) * element.val = matrix * basis.val
    simpa only [Matrix.mul_assoc, inverse', Matrix.mul_one] using equality

theorem conjugate_det {ring : Type*} [CommRing ring] (basis element : GeneralLinearGroup (Fin 2) ring) :
    GeneralLinearGroup.det (basis * element * basis⁻¹) = GeneralLinearGroup.det element := by
  simp only [map_mul, map_inv]
  rw [mul_comm (GeneralLinearGroup.det basis), mul_assoc, mul_inv_cancel, mul_one]

theorem conjugate_nonzero (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) (basis : BinaryRationalGL) :
    matrix * basis.val ≠ 0 := by
  intro zero
  have inverse : basis.val * basis⁻¹.val = 1 := basis.val_inv
  apply nonzero
  have equality := congrArg (fun value : Rectangular ℚ => value * basis⁻¹.val) zero
  simpa only [Matrix.mul_assoc, inverse, Matrix.mul_one, Matrix.zero_mul] using equality

theorem kernel_conjugate_unipotent (matrix : Rectangular ℚ) (nonzero : matrix ≠ 0) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (element : unipotents matrix) :
    ∃ parameter : ℚ, element.val.val = basis * binaryUnipotent parameter * basis⁻¹ := by
  have membership : basis⁻¹ * element.val.val * basis ∈ stabilizer (matrix * basis.val) := by
    apply (conjugate_mem matrix basis _).mpr
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using element.val.property
  have detOne : GeneralLinearGroup.det (basis⁻¹ * element.val.val * basis) = 1 := by
    simpa only [inv_inv] using (conjugate_det basis⁻¹ element.val.val).trans element.property
  have equality := unipotent_of_det_one (matrix * basis.val) (conjugate_nonzero matrix nonzero basis)
    zeroFirst _ membership detOne
  refine ⟨(basis⁻¹ * element.val.val * basis).val 0 1, ?_⟩
  rw [← equality]
  group

def scalingElement (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (scalar : ℚˣ) : stabilizer matrix :=
  ⟨basis * diagonal scalar 1 * basis⁻¹, by
    apply (conjugate_mem matrix basis _).mp
    change (matrix * basis.val) * (diagonal scalar 1).val = matrix * basis.val
    generalize matrix * basis.val = transformed at zeroFirst ⊢
    ext row column
    fin_cases column <;> simp [BinaryStrongApproximation.diagonal, Matrix.mul_apply, Fin.sum_univ_two, zeroFirst]⟩

theorem scalingElement_det (matrix : Rectangular ℚ) (basis : BinaryRationalGL)
    (zeroFirst : ∀ row, (matrix * basis.val) row 0 = 0) (scalar : ℚˣ) :
    determinant matrix (scalingElement matrix basis zeroFirst scalar) = scalar := by
  change GeneralLinearGroup.det (basis * diagonal scalar 1 * basis⁻¹) = scalar
  rw [conjugate_det, IdeleSlice.diagonal_det, mul_one]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SingularStabilizer
