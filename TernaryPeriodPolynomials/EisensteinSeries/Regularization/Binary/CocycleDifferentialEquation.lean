module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CocycleInfinitesimal
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalHilbertAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryCocycleHilbertFamily (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (entries : Matrix (Fin 2) (Fin 2) ℝ) (monomial : BinaryDegreeMonomial (degree + 1)) : cusp.H :=
  (cocycle (invertibleMatrix entries) monomial).val

theorem binaryCocycleHilbertFamily_contDiffAt (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (matrix : BinaryRealGL) :
    ContDiffAt ℝ ⊤ (binaryCocycleHilbertFamily cusp degree cocycle) matrix.val := by
  apply ContDiffOn.contDiffAt (s := {entries : Matrix (Fin 2) (Fin 2) ℝ | entries.det ≠ 0})
  · exact contDiffOn_pi.mpr (binaryCocycle_parameter_smooth cusp degree cocycle smooth)
  · exact (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds matrix.det_ne_zero

theorem binaryCocycleHilbertFamily_identity_derivative (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (binaryCocycleHilbertFamily cusp degree cocycle) 1 direction =
      fun monomial => (binaryCocycleInfinitesimal cusp degree cocycle smooth finite direction monomial).val := by
  have coordinate_differentiable (monomial : BinaryDegreeMonomial (degree + 1)) :
      DifferentiableAt ℝ (fun entries : Matrix (Fin 2) (Fin 2) ℝ =>
        (cocycle (invertibleMatrix entries) monomial).val) 1 := by
    exact ((binaryCocycle_parameter_smooth cusp degree cocycle smooth monomial).contDiffAt
      ((isOpen_ne.preimage continuous_id.matrix_det).mem_nhds (by simp))).differentiableAt (by simp)
  change fderiv ℝ (fun entries : Matrix (Fin 2) (Fin 2) ℝ =>
    fun monomial => (cocycle (invertibleMatrix entries) monomial).val) 1 direction = _
  rw [fderiv_pi coordinate_differentiable]
  rfl

theorem binaryCocycle_left_differential_equation (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (identity : ∀ first second, cocycle (first * second) = cocycle first +
      binaryCohomologicalRepresentation cusp degree first (cocycle second))
    (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (binaryCocycleHilbertFamily cusp degree cocycle) matrix.val (matrix.val * direction) =
      binaryCohomologicalHilbertAction cusp degree matrix
        (fderiv ℝ (binaryCocycleHilbertFamily cusp degree cocycle) 1 direction) := by
  let family := binaryCocycleHilbertFamily cusp degree cocycle
  let left : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ matrix.val)
  have at_matrix : DifferentiableAt ℝ family (left 1) := by
    change DifferentiableAt ℝ family (matrix.val * 1)
    rw [mul_one]
    exact (binaryCocycleHilbertFamily_contDiffAt cusp degree cocycle smooth matrix).differentiableAt (by simp)
  have at_one : DifferentiableAt ℝ family (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    (binaryCocycleHilbertFamily_contDiffAt cusp degree cocycle smooth 1).differentiableAt (by simp)
  have left_derivative := at_matrix.hasFDerivAt.comp 1 left.hasFDerivAt
  have right_derivative := (((binaryCohomologicalHilbertAction cusp degree matrix).restrictScalars ℝ).hasFDerivAt.comp
    1 at_one.hasFDerivAt).const_add (fun monomial => (cocycle matrix monomial).val)
  have near : (family ∘ left) =ᶠ[nhds (1 : Matrix (Fin 2) (Fin 2) ℝ)]
      (fun entries => (fun monomial => (cocycle matrix monomial).val) +
        binaryCohomologicalHilbertAction cusp degree matrix (family entries)) := by
    have domain_near : ∀ᶠ entries : Matrix (Fin 2) (Fin 2) ℝ in nhds 1, entries.det ≠ 0 :=
      (isOpen_ne.preimage continuous_id.matrix_det).eventually_mem (by simp)
    filter_upwards [domain_near] with entries invertible
    have value : matrix.val * entries = (matrix * invertibleMatrix entries).val := by
      simp only [Units.val_mul, invertibleMatrix, dite_eq_left invertible, GeneralLinearGroup.val_mkOfDetNeZero]
    change (fun monomial => (cocycle (invertibleMatrix (matrix.val * entries)) monomial).val) = _
    rw [value, invertibleMatrix_val, identity]
    change _ = (fun monomial => (cocycle matrix monomial).val) +
      binaryCohomologicalHilbertAction cusp degree matrix
        (fun monomial => (cocycle (invertibleMatrix entries) monomial).val)
    rw [binaryCohomologicalHilbertAction_smooth]
    rfl
  have equality := left_derivative.unique (right_derivative.congr_of_eventuallyEq near)
  have applied := congrArg (fun linear => linear direction) equality
  change fderiv ℝ family (matrix.val * 1) (matrix.val * direction) =
    binaryCohomologicalHilbertAction cusp degree matrix (fderiv ℝ family 1 direction) at applied
  simpa only [mul_one] using applied

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
