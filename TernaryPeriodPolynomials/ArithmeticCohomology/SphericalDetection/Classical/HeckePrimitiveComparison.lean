module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.HeckePrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem classicalHeckePrimitive_factors (halfWeight twist : ℤ) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (prime : Nat.Primes) :
    (prime.val : ℂ) ^ (-twist) * (prime.val : ℂ) ^ (degree + 1) =
      (prime.val : ℂ) ^ (-halfWeight - 1 - twist) * (prime.val : ℂ) ^ (-halfWeight) ∧
    (prime.val : ℂ) ^ (-twist) * (prime.val : ℂ)⁻¹ =
      (prime.val : ℂ) ^ (-halfWeight - 1 - twist) * (prime.val : ℂ) ^ halfWeight := by
  have nonzero : (prime.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr prime.property.ne_zero
  constructor
  · rw [← zpow_natCast, ← zpow_add₀ nonzero, ← zpow_add₀ nonzero]
    congr 1
    push_cast
    omega
  · rw [← _root_.zpow_neg_one, ← zpow_add₀ nonzero, ← zpow_add₀ nonzero]
    congr 1
    ring

theorem scalarPrimeHecke_modularHeckePoint (halfWeight : ℤ) (prime : Nat.Primes)
    (function : UpperHalfPlane → ℂ) (point : ℂ) (positive : 0 < point.im) :
    scalarPrimeHecke halfWeight prime function (UpperHalfPlane.ofComplex point) =
      (prime.val : ℂ) ^ (-halfWeight) * function (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) +
        (prime.val : ℂ) ^ halfWeight * ∑ index : Fin prime.val,
          function (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point)) := by
  let upper : UpperHalfPlane := ⟨point, positive⟩
  have upper_eq : UpperHalfPlane.ofComplex point = upper := UpperHalfPlane.ofComplex_apply upper
  have points (index : Option (Fin prime.val)) :
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • upper =
        UpperHalfPlane.ofComplex (modularHeckePoint prime index point) := by
    rw [← modularHeckePoint_upper prime index upper, UpperHalfPlane.ofComplex_apply]
  rw [upper_eq]
  change (prime.val : ℂ) ^ (-halfWeight) * function
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime none) • upper) +
    (prime.val : ℂ) ^ halfWeight * ∑ index : Fin prime.val, function
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime (some index)) • upper) = _
  simp_rw [points]

theorem classicalHeckePrimitive_transformed_derivative (halfWeight : ℤ)
    (form target : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (degree : ℕ) (weight_eq : -2 * halfWeight = (degree : ℤ) + 2)
    (twist : ℤ) (prime : Nat.Primes)
    (transformed : (target : UpperHalfPlane → ℂ) = scalarPrimeHecke halfWeight prime form)
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (point : ℂ) (positive : 0 < point.im) :
    HasDerivAt (fun point => functional (classicalHeckePrimitive form degree twist prime point))
      ((prime.val : ℂ) ^ (-halfWeight - 1 - twist) * functional (classicalBinaryForm target degree point)) point := by
  have result := classicalHeckePrimitive_differential form degree twist prime functional point positive
  obtain ⟨first, second⟩ := classicalHeckePrimitive_factors halfWeight twist degree weight_eq prime
  rw [first, second] at result
  have value : target (UpperHalfPlane.ofComplex point) =
      (prime.val : ℂ) ^ (-halfWeight) * form (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) +
        (prime.val : ℂ) ^ halfWeight * ∑ index : Fin prime.val,
          form (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point)) := by
    rw [transformed]
    exact scalarPrimeHecke_modularHeckePoint halfWeight prime form point positive
  have coefficient :
      ((prime.val : ℂ) ^ (-halfWeight - 1 - twist) * (prime.val : ℂ) ^ (-halfWeight) *
          form (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) +
        (prime.val : ℂ) ^ (-halfWeight - 1 - twist) * (prime.val : ℂ) ^ halfWeight *
          ∑ index : Fin prime.val, form (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point))) *
        functional (binaryPointPower degree point) =
      (prime.val : ℂ) ^ (-halfWeight - 1 - twist) * functional (classicalBinaryForm target degree point) := by
    rw [classicalBinaryForm, map_smul, smul_eq_mul, value]
    ring
  exact coefficient ▸ result

/-- The Hecke trace of the actual primitive, with its exact scalar and basepoint correction. -/
theorem classicalHeckePrimitive_comparison (halfWeight : ℤ)
    (form target : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (degree : ℕ) (weight_eq : -2 * halfWeight = (degree : ℤ) + 2)
    (twist : ℤ) (prime : Nat.Primes)
    (transformed : (target : UpperHalfPlane → ℂ) = scalarPrimeHecke halfWeight prime form)
    (point : ℂ) (positive : 0 < point.im) :
    classicalHeckePrimitive form degree twist prime point - classicalHeckePrimitive form degree twist prime Complex.I =
      (prime.val : ℂ) ^ (-halfWeight - 1 - twist) • classicalBinaryPrimitive target degree point := by
  let scalar : ℂ := (prime.val : ℂ) ^ (-halfWeight - 1 - twist)
  have derivative (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (argument : ℂ)
      (argument_positive : 0 < argument.im) :
      HasDerivAt (fun point => functional
        (classicalHeckePrimitive form degree twist prime point - classicalHeckePrimitive form degree twist prime Complex.I))
        (functional (classicalBinaryForm (scalar • target) degree argument)) argument := by
    have result := (classicalHeckePrimitive_transformed_derivative halfWeight form target degree weight_eq twist prime
      transformed functional argument argument_positive).sub_const
        (functional (classicalHeckePrimitive form degree twist prime Complex.I))
    rw [classicalBinaryForm_smul, map_smul, smul_eq_mul]
    convert result using 1
    all_goals first | (funext point; exact map_sub functional _ _)
  have equal := classicalBinaryPrimitive_unique (scalar • target) degree
    (fun point => classicalHeckePrimitive form degree twist prime point - classicalHeckePrimitive form degree twist prime Complex.I)
    (sub_self _) derivative point positive
  rw [classicalBinaryPrimitive_smul scalar target degree point positive] at equal
  exact equal

end TernaryPeriodPolynomials.SphericalDetection.Helpers
