module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderAlgebra

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspLoweringVector (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) : cusp.H :=
  fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 -
    Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I +
      (Complex.I * (weight : ℂ) / 2) • vector

theorem cuspRotationWeight_holomorphic_differential (cusp : CuspidalRepresentation)
    (vector : cusp.H) (weight : ℤ)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle))
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 -
          Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) =
      (angle : ℂ) ^ (weight - 2) •
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 -
          Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) +
      ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * ((angle : ℂ).im : ℂ)) • vector := by
  let linear := (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I).toLinearMap
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  have factor : (angle : ℂ) ^ weight * ((angle : ℂ) ^ 2)⁻¹ = (angle : ℂ) ^ (weight - 2) := by
    simp only [zpow_sub₀ nonzero, div_eq_mul_inv]
    rfl
  rw [map_sub, map_smul, cuspRotationWeight_differential cusp vector weight regular rotation,
    cuspRotationWeight_differential cusp vector weight regular rotation, mul_one]
  change (angle : ℂ) ^ weight • linear (((angle : ℂ) ^ 2)⁻¹) +
      ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * binaryRotationPhaseDerivative angle 1) • vector -
      Complex.I • ((angle : ℂ) ^ weight • linear (((angle : ℂ) ^ 2)⁻¹ * Complex.I) +
        ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * binaryRotationPhaseDerivative angle Complex.I) • vector) = _
  calc
    _ = (angle : ℂ) ^ weight •
        (linear (((angle : ℂ) ^ 2)⁻¹) - Complex.I • linear (((angle : ℂ) ^ 2)⁻¹ * Complex.I)) +
        ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) *
          (binaryRotationPhaseDerivative angle 1 - Complex.I * binaryRotationPhaseDerivative angle Complex.I)) • vector := by
      module
    _ = _ := by
      rw [realLinear_holomorphic_coordinates, smul_smul, factor, binaryRotationPhaseDerivative_holomorphic]
      rfl

theorem cuspLoweringVector_rotation (cusp : CuspidalRepresentation)
    (vector : cusp.H) (weight : ℤ)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (cuspLoweringVector cusp weight vector) =
      (angle : ℂ) ^ (weight - 2) • cuspLoweringVector cusp weight vector := by
  rw [cuspLoweringVector, map_add, map_smul,
    cuspRotationWeight_holomorphic_differential cusp vector weight regular rotation, rotation]
  calc
    _ = (angle : ℂ) ^ (weight - 2) •
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 -
          Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) +
        ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * ((angle : ℂ).im : ℂ) +
          (Complex.I * (weight : ℂ) / 2) * (angle : ℂ) ^ weight) • vector := by module
    _ = _ := by
      rw [binaryLowering_scalar]
      simp only [smul_add, smul_smul]

theorem cuspLoweringVector_regular (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp (cuspLoweringVector cusp weight vector))
      UpperHalfPlane.upperHalfPlaneSet := by
  have first := cuspAffineOrbitVector_derivative_contDiffOn cusp vector regular 1
  have second := cuspAffineOrbitVector_derivative_contDiffOn cusp vector regular Complex.I
  apply ((first.sub (second.const_smul Complex.I)).add
    (regular.const_smul (Complex.I * (weight : ℂ) / 2))).congr
  intro point _
  simp only [cuspAffineOrbitVector, cuspLoweringVector, map_add, map_sub, map_smul]

def cuspRaisingVector (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) : cusp.H :=
  fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 +
    Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I +
      (Complex.I * (weight : ℂ) / 2) • vector

theorem cuspRotationWeight_antiholomorphic_differential (cusp : CuspidalRepresentation)
    (vector : cusp.H) (weight : ℤ)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle))
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 +
          Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) =
      (angle : ℂ) ^ (weight + 2) •
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 +
          Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) +
      (-((weight : ℂ) * (angle : ℂ) ^ (weight + 1) * ((angle : ℂ).im : ℂ))) • vector := by
  let linear := (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I).toLinearMap
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  have conjugate_inverse : (starRingEnd ℂ) (((angle : ℂ) ^ 2)⁻¹) = (angle : ℂ) ^ 2 := by
    rw [map_inv₀, map_pow, ← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_pow, inv_inv]
  have factor : (angle : ℂ) ^ weight * (starRingEnd ℂ) (((angle : ℂ) ^ 2)⁻¹) = (angle : ℂ) ^ (weight + 2) := by
    rw [conjugate_inverse, zpow_add₀ nonzero]
    rfl
  have step : (angle : ℂ) ^ (weight - 1) * (angle : ℂ) ^ 2 = (angle : ℂ) ^ (weight + 1) := by
    rw [← zpow_natCast, ← zpow_add₀ nonzero]
    congr 1
    omega
  have phase_factor : (weight : ℂ) * (angle : ℂ) ^ (weight - 1) * (-(angle : ℂ) ^ 2 * ((angle : ℂ).im : ℂ)) =
      -((weight : ℂ) * (angle : ℂ) ^ (weight + 1) * ((angle : ℂ).im : ℂ)) := by
    calc
      _ = -((weight : ℂ) * ((angle : ℂ) ^ (weight - 1) * (angle : ℂ) ^ 2) * ((angle : ℂ).im : ℂ)) := by ring
      _ = _ := by rw [step]
  rw [map_add, map_smul, cuspRotationWeight_differential cusp vector weight regular rotation,
    cuspRotationWeight_differential cusp vector weight regular rotation, mul_one]
  change (angle : ℂ) ^ weight • linear (((angle : ℂ) ^ 2)⁻¹) +
      ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * binaryRotationPhaseDerivative angle 1) • vector +
      Complex.I • ((angle : ℂ) ^ weight • linear (((angle : ℂ) ^ 2)⁻¹ * Complex.I) +
        ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * binaryRotationPhaseDerivative angle Complex.I) • vector) = _
  calc
    _ = (angle : ℂ) ^ weight •
        (linear (((angle : ℂ) ^ 2)⁻¹) + Complex.I • linear (((angle : ℂ) ^ 2)⁻¹ * Complex.I)) +
        ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) *
          (binaryRotationPhaseDerivative angle 1 + Complex.I * binaryRotationPhaseDerivative angle Complex.I)) • vector := by
      module
    _ = _ := by
      rw [realLinear_antiholomorphic_coordinates, smul_smul, factor,
        binaryRotationPhaseDerivative_antiholomorphic, phase_factor]
      rfl

theorem cuspRaisingVector_rotation (cusp : CuspidalRepresentation)
    (vector : cusp.H) (weight : ℤ)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (cuspRaisingVector cusp weight vector) =
      (angle : ℂ) ^ (weight + 2) • cuspRaisingVector cusp weight vector := by
  rw [cuspRaisingVector, map_add, map_smul,
    cuspRotationWeight_antiholomorphic_differential cusp vector weight regular rotation, rotation]
  calc
    _ = (angle : ℂ) ^ (weight + 2) •
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1 +
          Complex.I • fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) +
        (-((weight : ℂ) * (angle : ℂ) ^ (weight + 1) * ((angle : ℂ).im : ℂ)) +
          (Complex.I * (weight : ℂ) / 2) * (angle : ℂ) ^ weight) • vector := by module
    _ = _ := by
      rw [binaryRaising_scalar]
      simp only [smul_add, smul_smul]

theorem cuspRaisingVector_regular (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp (cuspRaisingVector cusp weight vector))
      UpperHalfPlane.upperHalfPlaneSet := by
  have first := cuspAffineOrbitVector_derivative_contDiffOn cusp vector regular 1
  have second := cuspAffineOrbitVector_derivative_contDiffOn cusp vector regular Complex.I
  apply ((first.add (second.const_smul Complex.I)).add
    (regular.const_smul (Complex.I * (weight : ℂ) / 2))).congr
  intro point _
  simp only [cuspAffineOrbitVector, cuspRaisingVector, map_add, map_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
