module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.ParityPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem classicalParityPeriod_hecke_kernel (halfWeight : ℤ)
    (form target : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (degree : ℕ) (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (prime : Nat.Primes)
    (transformed : (target : UpperHalfPlane → ℂ) = scalarPrimeHecke halfWeight prime form)
    (zero : groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity (classicalBinaryCocycle form degree weight_eq twist)) = 0) :
    groupCohomology.H1π (modularBinaryRep degree twist)
      (modularCocycleParity degree twist parity (classicalBinaryCocycle target degree weight_eq twist)) = 0 := by
  obtain ⟨potential, equivariant⟩ :=
    (classicalParityPrimitive_equivariant_iff_H1_zero form degree weight_eq twist parity).mpr zero
  let representation := rationalBinaryRep degree twist
  let function : UpperHalfPlane → representation := fun point => classicalParityPrimitive form degree parity point + potential
  have invariant (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
      function (GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) • point) =
      representation.ρ (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) (function point) := by
    have real_eq : GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) =
          SpecialLinearGroup.mapGL ℝ matrix := by
      apply Units.ext
      ext row column
      simp [SpecialLinearGroup.mapGL, GeneralLinearGroup.map_apply]
    rw [real_eq]
    exact (equivariant matrix point).trans (rationalBinaryRep_integral degree twist
      (SpecialLinearGroup.toGL matrix) (classicalParityPrimitive form degree parity point + potential)).symm
  let traceMap : (UpperHalfPlane → Binary.HomogeneousPoly degree) →ₗ[ℂ]
      (UpperHalfPlane → Binary.HomogeneousPoly degree) := modularHeckeTrace representation prime
  let trace : UpperHalfPlane → Binary.HomogeneousPoly degree := traceMap function
  let scalar : ℂ := (prime.val : ℂ) ^ (-halfWeight - 1 - twist)
  have scalar_nonzero : scalar ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr prime.property.ne_zero)
  let constant : Binary.HomogeneousPoly degree := modularHeckeTrace representation prime (fun _ => potential) UpperHalfPlane.I
  let corrected := classicalHeckeParityPrimitive form degree twist parity prime Complex.I + constant
  have trace_formula (point : UpperHalfPlane) :
      trace point = scalar • classicalParityPrimitive target degree parity point + corrected := by
    have addition : trace point = traceMap
        (fun (point : UpperHalfPlane) => classicalParityPrimitive form degree parity point) point + constant := by
      have relation := congrFun (map_add traceMap
        (fun (point : UpperHalfPlane) => classicalParityPrimitive form degree parity point) (fun _ => potential)) point
      exact relation
    have primitive : traceMap
        (fun (point : UpperHalfPlane) => classicalParityPrimitive form degree parity point) point =
        classicalHeckeParityPrimitive form degree twist parity prime point :=
      (classicalHeckeParityPrimitive_eq_trace form degree twist parity prime point).symm
    have comparison := sub_eq_iff_eq_add.mp
      (classicalHeckeParityPrimitive_comparison halfWeight form target degree weight_eq even twist parity prime transformed
        point point.im_pos)
    change trace point = scalar • classicalParityPrimitive target degree parity point +
      (classicalHeckeParityPrimitive form degree twist parity prime Complex.I + constant)
    rw [addition, primitive, comparison, add_assoc]
  apply (classicalParityPrimitive_equivariant_iff_H1_zero target degree weight_eq twist parity).mp
  refine ⟨scalar⁻¹ • corrected, ?_⟩
  intro matrix point
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) := (modularBinaryRep degree twist).ρ matrix
  have real_eq : GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) =
        SpecialLinearGroup.mapGL ℝ matrix := by
    apply Units.ext
    ext row column
    simp [SpecialLinearGroup.mapGL, GeneralLinearGroup.map_apply]
  have relation := modularHeckeTrace_equivariant representation prime function invariant matrix point
  rw [real_eq] at relation
  have integral : representation.ρ (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix))
      (trace point) = action (trace point) := rationalBinaryRep_integral degree twist _ (trace point)
  change trace (SpecialLinearGroup.mapGL ℝ matrix • point) =
    representation.ρ (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) (trace point) at relation
  have concrete : trace (SpecialLinearGroup.mapGL ℝ matrix • point) = action (trace point) := relation.trans integral
  rw [trace_formula, trace_formula, map_add, map_smul] at concrete
  have scaled := congrArg (fun value : Binary.HomogeneousPoly degree => scalar⁻¹ • value) concrete
  simp only [smul_add, smul_smul, inv_mul_cancel₀ scalar_nonzero, one_smul] at scaled
  change @Eq (Binary.HomogeneousPoly degree)
    (classicalParityPrimitive target degree parity ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) +
      scalar⁻¹ • corrected)
    (action (classicalParityPrimitive target degree parity point + scalar⁻¹ • corrected))
  rw [map_add, map_smul]
  exact scaled

end TernaryPeriodPolynomials.SphericalDetection.Helpers
