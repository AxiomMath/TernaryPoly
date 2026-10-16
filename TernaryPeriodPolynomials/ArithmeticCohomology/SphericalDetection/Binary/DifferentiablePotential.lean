module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DifferentiableCohomology
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryUpperSectionMatrix (point : ℂ) : BinaryRealMatrix :=
  !![Real.sqrt point.im, point.re / Real.sqrt point.im; 0, 1 / Real.sqrt point.im]

theorem binaryUpperSectionMatrix_coe (point : UpperHalfPlane) :
    binaryUpperSectionMatrix point = (binarySymmetricSection point).val := by
  exact (UpperHalfPlane.coe_toSL2R point).symm

theorem binaryUpperSectionMatrix_invertible (point : ℂ) (positive : 0 < point.im) :
    (binaryUpperSectionMatrix point).det ≠ 0 := by
  rw [binaryUpperSectionMatrix_coe (⟨point, positive⟩ : UpperHalfPlane)]
  exact (binarySymmetricSection (⟨point, positive⟩ : UpperHalfPlane)).det_ne_zero

theorem binaryUpperSectionMatrix_contDiffOn {order : WithTop ℕ∞} :
    ContDiffOn ℝ order binaryUpperSectionMatrix UpperHalfPlane.upperHalfPlaneSet := by
  have imaginary : ContDiffOn ℝ order Complex.im UpperHalfPlane.upperHalfPlaneSet :=
    Complex.imCLM.contDiff.contDiffOn
  have root := imaginary.sqrt (fun point member => ne_of_gt member)
  have root_nonzero : ∀ point ∈ UpperHalfPlane.upperHalfPlaneSet, Real.sqrt point.im ≠ 0 :=
    fun point member => ne_of_gt (Real.sqrt_pos.mpr member)
  apply contDiffOn_pi.mpr
  intro row
  apply contDiffOn_pi.mpr
  intro column
  fin_cases row <;> fin_cases column
  · exact root
  · exact Complex.reCLM.contDiff.contDiffOn.div root root_nonzero
  · exact contDiffOn_const
  · exact contDiffOn_const.div root root_nonzero

theorem binarySymmetricSection_coe_smul (point argument : UpperHalfPlane) :
    ((binarySymmetricSection point • argument : UpperHalfPlane) : ℂ) =
      (point.re : ℂ) + (point.im : ℂ) * (argument : ℂ) := by
  have positive : 0 < (GeneralLinearGroup.det (binarySymmetricSection point)).val := by
    change 0 < point.toSL2R.val.det
    rw [point.toSL2R.property]
    norm_num
  rw [UpperHalfPlane.coe_smul_of_det_pos positive]
  have root_ne : (Real.sqrt point.im : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr point.im_pos)
  have root_sq : (Real.sqrt point.im : ℂ) ^ 2 = (point.im : ℂ) := by
    exact_mod_cast Real.sq_sqrt point.im_pos.le
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  rw [← binaryUpperSectionMatrix_coe]
  simp only [binaryUpperSectionMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.ofReal_div, Complex.ofReal_zero,
    Complex.ofReal_one, zero_mul, zero_add]
  change ((Real.sqrt point.im : ℂ) * (argument : ℂ) + (point.re : ℂ) / (Real.sqrt point.im : ℂ)) /
    (1 / (Real.sqrt point.im : ℂ)) = (point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)
  field_simp
  linear_combination (argument : ℂ) * root_sq

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryUpperPotential (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (point : ℂ) : index → cusp.H :=
  (cycle (invertibleMatrix (binaryUpperSectionMatrix point)) : binaryHilbertFiniteValues cusp level).val

theorem binaryUpperPotential_coe (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (point : UpperHalfPlane) :
    binaryUpperPotential cusp spherical basis level cycle point =
      (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle point :
        binaryHilbertFiniteValues cusp level).val := by
  simp only [binaryUpperPotential, binaryUpperSectionMatrix_coe, invertibleMatrix_coe,
    binarySymmetricPotential]

theorem binaryUpperPotential_contDiffOn (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    {order : WithTop ℕ∞}
    (regular : ContDiffOn ℝ order (fun matrix : BinaryRealMatrix =>
      (cycle (invertibleMatrix matrix) : binaryHilbertFiniteValues cusp level).val)
      {matrix | matrix.det ≠ 0}) :
    ContDiffOn ℝ order (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet :=
  regular.comp binaryUpperSectionMatrix_contDiffOn binaryUpperSectionMatrix_invertible

theorem binaryUpperPotential_affine (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (point argument : UpperHalfPlane) :
    binaryUpperPotential cusp spherical basis level cycle
      ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
        binaryHilbertOperator cusp basis (binarySymmetricSection point)
          (binaryUpperPotential cusp spherical basis level cycle argument) := by
  rw [← binarySymmetricSection_coe_smul point argument, binaryUpperPotential_coe,
    binaryUpperPotential_coe]
  exact congrArg Subtype.val (binarySymmetricPotential_affine _ cycle stabilizer_zero
    (binarySymmetricSection point) argument)

theorem binaryUpperPotential_exists_fderiv_ne_zero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    ∃ point : UpperHalfPlane,
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ) ≠ 0 := by
  by_contra no_derivative
  have zero_derivative : Set.EqOn
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle)) 0
      UpperHalfPlane.upperHalfPlaneSet := by
    intro point member
    exact not_ne_iff.mp (fun nonzero => no_derivative ⟨⟨point, member⟩, nonzero⟩)
  have convex : Convex ℝ UpperHalfPlane.upperHalfPlaneSet :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  have constant {x y : ℂ} (x_mem : x ∈ UpperHalfPlane.upperHalfPlaneSet)
      (y_mem : y ∈ UpperHalfPlane.upperHalfPlaneSet) :
      binaryUpperPotential cusp spherical basis level cycle x =
        binaryUpperPotential cusp spherical basis level cycle y :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
      convex.isPreconnected regular zero_derivative x_mem y_mem
  have basepoint : binaryUpperPotential cusp spherical basis level cycle (UpperHalfPlane.I : ℂ) = 0 := by
    rw [binaryUpperPotential_coe, binarySymmetricPotential_basepoint _ cycle stabilizer_zero]
    rfl
  have cycle_zero : cycle = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    apply Subtype.ext
    have equal := constant (x := ((matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ))
      (y := (UpperHalfPlane.I : ℂ)) (matrix • UpperHalfPlane.I).im_pos UpperHalfPlane.I.im_pos
    rw [binaryUpperPotential_coe, binarySymmetricPotential_descent _ cycle stabilizer_zero,
      basepoint] at equal
    exact equal
  exact nonzero (by rw [cycle_zero, map_zero])

theorem binaryUpperPotential_fderiv_basepoint_ne_zero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0)
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I ≠ 0 := by
  intro base_zero
  obtain ⟨point, derivative_nonzero⟩ := binaryUpperPotential_exists_fderiv_ne_zero
    cusp spherical basis level cycle nonzero regular stabilizer_zero
  let potential := binaryUpperPotential cusp spherical basis level cycle
  let affine : ℂ → ℂ := fun argument => (point.re : ℂ) + point.im • argument
  have affine_base : affine Complex.I = (point : ℂ) := by
    apply Complex.ext <;> simp [affine]
  have affine_derivative : HasFDerivAt affine (point.im • ContinuousLinearMap.id ℝ ℂ) Complex.I :=
    ((hasFDerivAt_id (𝕜 := ℝ) Complex.I).const_smul point.im).const_add (point.re : ℂ)
  have point_derivative : HasFDerivAt potential (fderiv ℝ potential (point : ℂ)) (point : ℂ) :=
    (regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos)).hasFDerivAt
  have base_derivative : HasFDerivAt (𝕜 := ℝ) potential 0 Complex.I := by
    have differentiable := regular.differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp))
    simpa only [potential, base_zero] using differentiable.hasFDerivAt
  have at_affine : HasFDerivAt potential (fderiv ℝ potential (point : ℂ)) (affine Complex.I) :=
    affine_base.symm ▸ point_derivative
  have left_derivative := at_affine.comp Complex.I affine_derivative
  let action := (binaryHilbertOperator cusp basis (binarySymmetricSection point)).restrictScalars ℝ
  have right_derivative : HasFDerivAt (𝕜 := ℝ)
      (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
        action (potential argument)) 0 Complex.I := by
    have derivative := (action.hasFDerivAt.comp Complex.I base_derivative).const_add
      (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val
    rw [ContinuousLinearMap.comp_zero] at derivative
    exact derivative
  have equality : potential ∘ affine =ᶠ[nhds Complex.I]
      (fun argument => (cycle (binarySymmetricSection point) : binaryHilbertFiniteValues cusp level).val +
        action (potential argument)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp)] with argument member
    exact binaryUpperPotential_affine cusp spherical basis level cycle stabilizer_zero point ⟨argument, member⟩
  have derivative_zero := left_derivative.unique (right_derivative.congr_of_eventuallyEq equality)
  apply derivative_nonzero
  apply ContinuousLinearMap.ext
  intro direction
  have scaled := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction) derivative_zero
  change fderiv ℝ potential (point : ℂ) (point.im • direction) = 0 at scaled
  rw [map_smul] at scaled
  exact (smul_eq_zero.mp scaled).resolve_left (ne_of_gt point.im_pos)

theorem cohomological_exists_nonzero_symmetric_differential (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
        UpperHalfPlane.upperHalfPlaneSet ∧
      (∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) ∧
      ∃ point : UpperHalfPlane,
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ) ≠ 0 := by
  obtain ⟨level, cycle, level_open, level_compact, nonzero, regular, stabilizer_zero⟩ :=
    cohomological_exists_smooth_symmetricSpace_H1 cusp spherical cohomological basis
  have potential_regular := binaryUpperPotential_contDiffOn cusp spherical basis level cycle regular
  exact ⟨level, cycle, level_open, level_compact, nonzero, potential_regular, stabilizer_zero,
    binaryUpperPotential_exists_fderiv_ne_zero cusp spherical basis level cycle nonzero
      (potential_regular.differentiableOn (by simp)) stabilizer_zero⟩

theorem cohomological_exists_symmetric_basepoint_differential (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
        UpperHalfPlane.upperHalfPlaneSet ∧
      (∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) ∧
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I ≠ 0 := by
  obtain ⟨level, cycle, level_open, level_compact, nonzero, regular, stabilizer_zero⟩ :=
    cohomological_exists_smooth_symmetricSpace_H1 cusp spherical cohomological basis
  have potential_regular := binaryUpperPotential_contDiffOn cusp spherical basis level cycle regular
  exact ⟨level, cycle, level_open, level_compact, nonzero, potential_regular, stabilizer_zero,
    binaryUpperPotential_fderiv_basepoint_ne_zero cusp spherical basis level cycle nonzero
      (potential_regular.differentiableOn (by simp)) stabilizer_zero⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
