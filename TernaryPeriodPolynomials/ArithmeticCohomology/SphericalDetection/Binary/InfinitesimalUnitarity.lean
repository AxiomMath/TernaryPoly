module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeCocycle
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspUnitary_inner (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (first second : cusp.H) :
    inner ℂ (cusp.π matrix first) (cusp.π matrix second) = inner ℂ first second :=
  (cuspUnitaryIsometryEquiv cusp matrix).inner_map_map first second

theorem cuspUnitary_derivative_skew (cusp : CuspidalRepresentation)
    (path : ℝ → BinaryAdelicGL) (at_zero : path 0 = 1)
    (first second first_derivative second_derivative : cusp.H)
    (first_regular : HasDerivAt (fun parameter => cusp.π (path parameter) first) first_derivative 0)
    (second_regular : HasDerivAt (fun parameter => cusp.π (path parameter) second) second_derivative 0) :
    inner ℂ first second_derivative + inner ℂ first_derivative second = 0 := by
  have derivative := first_regular.inner ℂ second_regular
  have constant : (fun parameter => inner ℂ (cusp.π (path parameter) first)
      (cusp.π (path parameter) second)) = fun _ => inner ℂ first second := by
    funext parameter
    exact cuspUnitary_inner cusp (path parameter) first second
  rw [constant] at derivative
  have equality := derivative.unique (hasDerivAt_const (0 : ℝ) (inner ℂ first second))
  simpa only [at_zero, map_one, Module.End.one_apply] using equality

def cuspAffineOrbitVector (cusp : CuspidalRepresentation) (vector : cusp.H) (point : ℂ) : cusp.H :=
  cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point))) vector

theorem binaryUpperSectionMatrix_I : binaryUpperSectionMatrix Complex.I = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUpperSectionMatrix]

theorem binaryAffineSection_I : invertibleMatrix (binaryUpperSectionMatrix Complex.I) = 1 := by
  rw [binaryUpperSectionMatrix_I]
  exact invertibleMatrix_coe (1 : BinaryRealGL)

theorem cuspAffineOrbitVector_I (cusp : CuspidalRepresentation) (vector : cusp.H) :
    cuspAffineOrbitVector cusp vector Complex.I = vector := by
  rw [cuspAffineOrbitVector, binaryAffineSection_I, atInfinity_one, map_one]
  rfl

theorem cuspAffineOrbitVector_derivative_skew (cusp : CuspidalRepresentation)
    (first second : cusp.H)
    (first_regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp first) Complex.I)
    (second_regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp second) Complex.I)
    (direction : ℂ) :
    inner ℂ first (fderiv ℝ (cuspAffineOrbitVector cusp second) Complex.I direction) +
      inner ℂ (fderiv ℝ (cuspAffineOrbitVector cusp first) Complex.I direction) second = 0 := by
  have line_derivative : HasDerivAt (fun parameter : ℝ => Complex.I + parameter • direction) direction 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add Complex.I using 1
    · rfl
    · exact (one_smul ℝ direction).symm
  have first_derivative := first_regular.hasFDerivAt.comp_hasDerivAt_of_eq 0 line_derivative (by simp)
  have second_derivative := second_regular.hasFDerivAt.comp_hasDerivAt_of_eq 0 line_derivative (by simp)
  apply cuspUnitary_derivative_skew cusp
    (fun parameter : ℝ => atInfinity (invertibleMatrix
      (binaryUpperSectionMatrix (Complex.I + parameter • direction)))) _ first second _ _
    first_derivative second_derivative
  simp only [zero_smul, add_zero, binaryAffineSection_I, atInfinity_one]

theorem cuspAffineOrbitVector_real_inner_derivative (cusp : CuspidalRepresentation)
    (vector : cusp.H) (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I)
    (direction : ℂ) :
    (inner ℂ vector (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction)).re = 0 := by
  have skew := cuspAffineOrbitVector_derivative_skew cusp vector vector regular regular direction
  have real_skew := congrArg Complex.re skew
  rw [← inner_conj_symm (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction) vector] at real_skew
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at real_skew
  linarith

variable {degree : ℕ} {index : Type} [Fintype index]

theorem cuspAffineOrbitVector_coordinate_contDiffOn (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : index → cusp.H) {order : WithTop ℕ∞}
    (regular : ContDiffOn ℝ order (binaryAffineOrbitVector cusp basis vector) UpperHalfPlane.upperHalfPlaneSet)
    (position : index) :
    ContDiffOn ℝ order (cuspAffineOrbitVector cusp (vector position)) UpperHalfPlane.upperHalfPlaneSet := by
  have entries (row column : Fin 2) :
      ContDiffOn ℝ order (fun point => binaryUpperSectionMatrix point row column) UpperHalfPlane.upperHalfPlaneSet :=
    contDiffOn_pi.mp (contDiffOn_pi.mp binaryUpperSectionMatrix_contDiffOn row) column
  have unitary_regular := binaryHilbertTranslation_contDiffOn_of_operator cusp basis
    binaryUpperSectionMatrix entries binaryUpperSectionMatrix_invertible vector regular
  exact contDiffOn_pi.mp unitary_regular position

end TernaryPeriodPolynomials.SphericalDetection.Helpers
