module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointDifferential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryEndpointDifferential (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (lower : index → cusp.H) (point direction : ℂ) : index → cusp.H :=
  point.im⁻¹ • binaryAffineOrbitVector cusp basis
    ((2 : ℂ)⁻¹ • (direction • lower -
      (starRingEnd ℂ direction) • binaryHilbertOperator cusp basis UpperHalfPlane.J lower)) point

def binaryEndpointPrimitive (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (lower : index → cusp.H) (point : ℂ) : index → cusp.H :=
  ∫ parameter : ℝ in 0..1, binaryEndpointDifferential cusp basis lower
    (Complex.I + parameter • (point - Complex.I)) (point - Complex.I)

theorem upperHalfPlane_straightPath (point : UpperHalfPlane) {parameter : ℝ}
    (member : parameter ∈ Set.Icc 0 1) :
    0 < (Complex.I + parameter • ((point : ℂ) - Complex.I)).im := by
  simp only [Complex.add_im, Complex.I_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_mul, add_zero]
  have positive := point.im_pos
  change 0 < (point : ℂ).im at positive
  by_cases zero : parameter = 0
  · simp [zero]
  · have product := mul_pos (lt_of_le_of_ne member.1 (Ne.symm zero)) positive
    nlinarith [member.2]

/-- Integrating the transported differential reconstructs the supplied relative cycle's potential. -/
theorem binaryUpperPotential_eq_endpointPrimitive (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (point : UpperHalfPlane) :
    binaryUpperPotential cusp spherical basis level cycle point =
      binaryEndpointPrimitive cusp basis
        (binaryHolomorphicTangent cusp spherical basis level cycle) point := by
  let potential := binaryUpperPotential cusp spherical basis level cycle
  let path : ℝ → ℂ := fun parameter => Complex.I + parameter • ((point : ℂ) - Complex.I)
  let direction : ℂ := (point : ℂ) - Complex.I
  have path_continuous : Continuous path := by fun_prop
  have path_mem : Set.MapsTo path (Set.Icc 0 1) UpperHalfPlane.upperHalfPlaneSet :=
    fun _ member => upperHalfPlane_straightPath point member
  have differentiable := regular.differentiableOn (by simp)
  have derivative_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ potential)
      UpperHalfPlane.upperHalfPlaneSet :=
    regular.fderiv_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet
      (WithTop.coe_le_coe.mpr (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))
  have derivative_continuous : ContinuousOn
      (fun parameter => fderiv ℝ potential (path parameter) direction) (Set.Icc 0 1) :=
    (derivative_regular.continuousOn.comp
        path_continuous.continuousOn path_mem).clm_apply continuousOn_const
  have derivative (parameter : ℝ) (member : parameter ∈ Set.uIcc 0 1) :
      HasDerivAt (potential ∘ path) (fderiv ℝ potential (path parameter) direction) parameter := by
    have belongs : parameter ∈ Set.Icc 0 1 := by simpa only [Set.uIcc_of_le zero_le_one] using member
    have at_point := (differentiable.differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (path_mem belongs))).hasFDerivAt
    have path_derivative : HasDerivAt path direction parameter := by
      simpa only [one_smul, id_eq, path, direction] using
        ((hasDerivAt_id parameter).smul_const direction).const_add Complex.I
    exact at_point.comp_hasDerivAt parameter path_derivative
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    (derivative_continuous.intervalIntegrable_of_Icc zero_le_one)
  have basepoint : potential Complex.I = 0 := by
    change binaryUpperPotential cusp spherical basis level cycle (UpperHalfPlane.I : ℂ) = 0
    rw [binaryUpperPotential_coe, binarySymmetricPotential_basepoint _ cycle stabilizer_zero]
    rfl
  have endpoints : (potential ∘ path) 1 - (potential ∘ path) 0 = potential point := by
    simp only [Function.comp_def, path, one_smul, zero_smul, add_zero, add_sub_cancel,
      basepoint, sub_zero]
  rw [endpoints] at integral
  change potential point = _
  rw [← integral]
  apply intervalIntegral.integral_congr
  intro parameter member
  have belongs : parameter ∈ Set.Icc 0 1 := by simpa only [Set.uIcc_of_le zero_le_one] using member
  exact binaryUpperPotential_fderiv_from_lower cusp spherical basis level cycle differentiable
    stabilizer_zero ⟨path parameter, path_mem belongs⟩ direction

theorem binaryRelativeCycle_eq_endpointPrimitive (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical basis level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (matrix : BinaryRealGL) :
    (cycle matrix : binaryHilbertFiniteValues cusp level).val =
      binaryEndpointPrimitive cusp basis
        (binaryHolomorphicTangent cusp spherical basis level cycle)
        ((matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
  rw [← binaryUpperPotential_eq_endpointPrimitive cusp spherical basis level cycle regular stabilizer_zero,
    binaryUpperPotential_coe, binarySymmetricPotential_descent _ cycle stabilizer_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
