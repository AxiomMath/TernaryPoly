module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineLieOperators
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SubstitutionDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryUpperSectionInverse (point : ℂ) : BinaryRealMatrix :=
  !![1 / Real.sqrt point.im, -(point.re / Real.sqrt point.im); 0, Real.sqrt point.im]

theorem binaryUpperSectionMatrix_det (point : ℂ) (positive : 0 < point.im) :
    (binaryUpperSectionMatrix point).det = 1 := by
  rw [binaryUpperSectionMatrix_coe (⟨point, positive⟩ : UpperHalfPlane)]
  exact (⟨point, positive⟩ : UpperHalfPlane).toSL2R.property

theorem binaryUpperSectionMatrix_inverse (point : ℂ) (positive : 0 < point.im) :
    (binaryUpperSectionMatrix point)⁻¹ = binaryUpperSectionInverse point := by
  rw [Matrix.inv_def, binaryUpperSectionMatrix_det point positive,
    Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  simp [binaryUpperSectionMatrix, binaryUpperSectionInverse]

def binaryAffineInverseDerivative (direction : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(direction.im : ℂ) / 2, -(direction.re : ℂ); 0, (direction.im : ℂ) / 2]

theorem binaryInfinitesimalSubstitution_horizontal (polynomial : Binary.Poly) :
    binaryInfinitesimalSubstitution (binaryAffineInverseDerivative 1) polynomial =
      -(MvPolynomial.X 1 * MvPolynomial.pderiv 0 polynomial) := by
  simp [binaryInfinitesimalSubstitution, binaryAffineInverseDerivative, Binary.linearForm, Fin.sum_univ_two]

theorem binaryInfinitesimalSubstitution_vertical (polynomial : Binary.Poly) :
    binaryInfinitesimalSubstitution (binaryAffineInverseDerivative Complex.I) polynomial =
      (1 / 2 : ℂ) • (MvPolynomial.X 1 * MvPolynomial.pderiv 1 polynomial -
        MvPolynomial.X 0 * MvPolynomial.pderiv 0 polynomial) := by
  simp [binaryInfinitesimalSubstitution, binaryAffineInverseDerivative, Binary.linearForm,
    Fin.sum_univ_two, Algebra.smul_def, neg_div]
  ring

theorem binaryUpperSectionInverse_hasDerivAt (direction : ℂ) (row column : Fin 2) :
    HasDerivAt
      (fun parameter : ℝ => (binaryUpperSectionInverse (Complex.I + parameter • direction) row column : ℂ))
      (binaryAffineInverseDerivative direction row column) 0 := by
  have real_derivative : HasDerivAt (fun parameter : ℝ => (Complex.I + parameter • direction).re) direction.re 0 := by
    convert (hasDerivAt_id (0 : ℝ)).mul_const direction.re using 1 <;> first
      | simp [Complex.real_smul]
  have imaginary_derivative : HasDerivAt (fun parameter : ℝ => (Complex.I + parameter • direction).im) direction.im 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const direction.im).const_add 1 using 1 <;> first
      | simp [Complex.real_smul]
  have root_derivative : HasDerivAt (fun parameter : ℝ => Real.sqrt (Complex.I + parameter • direction).im)
      (direction.im / 2) 0 := by
    simpa only [zero_smul, add_zero, Complex.I_im, Real.sqrt_one, mul_one] using
      imaginary_derivative.sqrt (by simp)
  have root_nonzero : Real.sqrt (Complex.I + (0 : ℝ) • direction).im ≠ 0 := by simp
  fin_cases row <;> fin_cases column
  · simpa [binaryUpperSectionInverse, binaryAffineInverseDerivative, one_div, neg_div] using
      (root_derivative.inv root_nonzero).ofReal_comp
  · simpa [binaryUpperSectionInverse, binaryAffineInverseDerivative] using
      (real_derivative.div root_derivative root_nonzero).neg.ofReal_comp
  · simpa [binaryUpperSectionInverse, binaryAffineInverseDerivative] using
      (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  · simpa [binaryUpperSectionInverse, binaryAffineInverseDerivative] using root_derivative.ofReal_comp

theorem binaryAffineLine_eventually_positive (direction : ℂ) :
    ∀ᶠ parameter : ℝ in nhds 0, 0 < (Complex.I + parameter • direction).im := by
  have continuous : Continuous (fun parameter : ℝ => (Complex.I + parameter • direction).im) := by fun_prop
  have positive : 0 < (Complex.I + (0 : ℝ) • direction).im := by simp
  exact continuous.continuousAt.eventually (lt_mem_nhds positive)

theorem binaryAffineCoefficient_functional_hasDerivAt {degree : ℕ}
    (direction : ℂ) (polynomial : Binary.HomogeneousPoly (degree + 1))
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    HasDerivAt
      (fun parameter : ℝ => functional (binaryCoefficient degree
        (invertibleMatrix (binaryUpperSectionMatrix (Complex.I + parameter • direction))) polynomial))
      (functional (binaryInfinitesimalCoefficient degree (binaryAffineInverseDerivative direction) polynomial)) 0 := by
  let matrices : ℝ → Binary.GL2 := fun parameter => GeneralLinearGroup.map (algebraMap ℝ ℂ)
    (invertibleMatrix (binaryUpperSectionMatrix (Complex.I + parameter • direction)))
  apply binary_homogeneousAction_functional_hasDerivAt matrices (binaryAffineInverseDerivative direction)
  · simp only [matrices, zero_smul, add_zero, binaryAffineSection_I, map_one]
  · filter_upwards [binaryAffineLine_eventually_positive direction] with parameter positive
    change (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (invertibleMatrix (binaryUpperSectionMatrix (Complex.I + parameter • direction))))).val = 1
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply,
      invertibleMatrix_val _ (binaryUpperSectionMatrix_invertible _ positive)]
    change (Complex.ofRealHom.mapMatrix (binaryUpperSectionMatrix (Complex.I + parameter • direction))).det = 1
    rw [← Complex.ofRealHom.map_det, binaryUpperSectionMatrix_det _ positive, map_one]
  · intro row column
    apply (binaryUpperSectionInverse_hasDerivAt direction row column).congr_of_eventuallyEq
    filter_upwards [binaryAffineLine_eventually_positive direction] with parameter positive
    dsimp only [matrices]
    rw [← map_inv, GeneralLinearGroup.val_map_apply, GeneralLinearGroup.coe_inv,
      invertibleMatrix_val _ (binaryUpperSectionMatrix_invertible _ positive), binaryUpperSectionMatrix_inverse _ positive]
    rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
