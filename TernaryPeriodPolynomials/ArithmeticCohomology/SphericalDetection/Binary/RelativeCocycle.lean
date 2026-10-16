module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TangentCohomology
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binarySymmetricSection_smulFDeriv (point : UpperHalfPlane) (direction : ℂ) :
    UpperHalfPlane.smulFDeriv (binarySymmetricSection point) Complex.I direction = point.im • direction := by
  have determinant : (GeneralLinearGroup.det (binarySymmetricSection point)).val = 1 :=
    point.toSL2R.property
  have denominator : UpperHalfPlane.denom (binarySymmetricSection point) Complex.I =
      1 / (Real.sqrt point.im : ℂ) := by
    simp only [UpperHalfPlane.denom]
    rw [← binaryUpperSectionMatrix_coe]
    simp [binaryUpperSectionMatrix]
  have root_sq : (Real.sqrt point.im : ℂ) ^ 2 = (point.im : ℂ) := by
    exact_mod_cast Real.sq_sqrt point.im_pos.le
  simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, determinant, denominator,
    one_div, root_sq, Complex.real_smul, mul_comm]

theorem weightedGradient_relation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℂ → E) (regular : ContDiffAt ℝ 2 function Complex.I) :
    fderiv ℝ (fun point : ℂ => point.im • fderiv ℝ function point 1) Complex.I Complex.I -
      fderiv ℝ (fun point : ℂ => point.im • fderiv ℝ function point Complex.I) Complex.I 1 =
        fderiv ℝ function Complex.I 1 := by
  have second_regular : ContDiffAt ℝ 1 (fderiv ℝ function) Complex.I :=
    regular.fderiv_right (by norm_num)
  have derivative := (second_regular.differentiableAt (by norm_num)).hasFDerivAt
  have weighted_derivative (direction : ℂ) :
      HasFDerivAt (fun point : ℂ => point.im • fderiv ℝ function point direction)
        (Complex.I.im • ((fderiv ℝ function Complex.I).comp (0 : ℂ →L[ℝ] ℂ) +
          (fderiv ℝ (fderiv ℝ function) Complex.I).flip direction) +
          Complex.imCLM.smulRight (fderiv ℝ function Complex.I direction)) Complex.I := by
    exact Complex.imCLM.hasFDerivAt.smul (derivative.clm_apply (hasFDerivAt_const direction Complex.I))
  rw [(weighted_derivative 1).fderiv, (weighted_derivative Complex.I).fderiv]
  simp only [Complex.imCLM_apply, Complex.I_im, one_smul, ContinuousLinearMap.comp_zero,
    zero_add, _root_.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRight_apply, Complex.one_im, zero_smul, add_zero]
  have symmetric := regular.isSymmSndFDerivAt (by norm_num [minSmoothness])
  rw [symmetric.eq Complex.I 1]
  abel

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryAffineOrbitVector (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : index → cusp.H) (point : ℂ) : index → cusp.H :=
  binaryHilbertOperator cusp basis (invertibleMatrix (binaryUpperSectionMatrix point)) vector

theorem binaryAffineOrbitVector_tangent (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (point : UpperHalfPlane) (direction : ℂ) :
    binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) point =
        point.im • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ) direction := by
  have equivariant := binaryUpperPotential_fderiv_equivariant cusp spherical basis level cycle regular
    stabilizer_zero (binarySymmetricSection point) UpperHalfPlane.I
  rw [binarySymmetricSection_smul] at equivariant
  have evaluated := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction) equivariant
  change fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ)
      (UpperHalfPlane.smulFDeriv (binarySymmetricSection point) Complex.I direction) =
    binaryHilbertOperator cusp basis (binarySymmetricSection point)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) at evaluated
  rw [binarySymmetricSection_smulFDeriv, map_smul] at evaluated
  rw [binaryAffineOrbitVector, binaryUpperSectionMatrix_coe, invertibleMatrix_coe]
  exact evaluated.symm

theorem binaryAffineOrbitVector_tangent_contDiffOn (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (direction : ℂ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction))
      UpperHalfPlane.upperHalfPlaneSet := by
  have derivative_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle)) UpperHalfPlane.upperHalfPlaneSet :=
    regular.fderiv_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet
      (WithTop.coe_le_coe.mpr (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))
  have weighted := Complex.imCLM.contDiff.contDiffOn.smul
    (derivative_regular.clm_apply (contDiffOn_const (c := direction)))
  apply weighted.congr
  intro point member
  exact binaryAffineOrbitVector_tangent cusp spherical basis level cycle
    (regular.differentiableOn (by simp)) stabilizer_zero ⟨point, member⟩ direction

theorem binaryTangent_relativeCocycle (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    fderiv ℝ (binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1)) Complex.I Complex.I -
    fderiv ℝ (binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I)) Complex.I 1 =
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 := by
  have equality (direction : ℂ) :
      binaryAffineOrbitVector cusp basis
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) =ᶠ[nhds Complex.I]
      (fun point : ℂ => point.im •
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) point direction) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp)] with point member
    exact binaryAffineOrbitVector_tangent cusp spherical basis level cycle
      (regular.differentiableOn (by simp)) stabilizer_zero ⟨point, member⟩ direction
  rw [(equality 1).fderiv_eq, (equality Complex.I).fderiv_eq]
  apply weightedGradient_relation
  exact (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp))).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
