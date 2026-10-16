module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ClassicalDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArithmeticModularity
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryStrongApproximation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentPeriodicity

theorem unipotent_zero {ring : Type*} [CommRing ring] : binaryUnipotent (0 : ring) = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUnipotent]

def integerUnipotent (parameter : ℤ) : SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, parameter; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem integerUnipotent_map (parameter : ℤ) :
    SpecialLinearGroup.mapGL ℝ (integerUnipotent parameter) = binaryUnipotent (parameter : ℝ) := by
  apply Units.ext
  ext row column
  change ((integerUnipotent parameter).val row column : ℝ) = (binaryUnipotent (parameter : ℝ)).val row column
  fin_cases row <;> fin_cases column <;> simp [integerUnipotent, binaryUnipotent]

theorem integerUnipotent_three : integerUnipotent 3 ∈ CongruenceSubgroup.Gamma 3 := by
  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [integerUnipotent]
  decide

noncomputable def realFunction (data : CuspidalRepresentation) (vector : data.smooth)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) (parameter : ℝ) : ℂ :=
  data.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding point) *
    atInfinity (binaryUnipotent parameter * realPoint))

theorem realFunction_continuous (data : CuspidalRepresentation) (vector : data.smooth)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) :
    Continuous (realFunction data vector point realPoint) := by
  have continuity := (RotationScalarDerivative.scalarMatrixOrbit_contDiffOn data
    (atFinite (GeneralLinearGroup.map integralEmbedding point)) vector).continuousOn.comp_continuous
      (ZeroCocycleDifferential.upper_curve_differentiable.continuous.mul continuous_const)
      (fun parameter => GeneralLinearGroup.det_ne_zero (binaryUnipotent parameter * realPoint))
  have equality : RotationScalarDerivative.scalarMatrixOrbit data
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) vector ∘
        (fun parameter : ℝ => (binaryUnipotent parameter).val * realPoint.val) =
      realFunction data vector point realPoint := by
    funext parameter
    change data.realize vector (_ * atInfinity (invertibleMatrix (binaryUnipotent parameter * realPoint).val)) = _
    rw [invertibleMatrix_units]
    rfl
  exact continuity.congr (congrFun equality)

theorem realFunction_periodic (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) :
    Function.Periodic (realFunction data vector point realPoint) 3 := by
  intro parameter
  have invariance := realize_arithmetic data vector fixed (integerUnipotent 3) integerUnipotent_three
    point (binaryUnipotent parameter * realPoint)
  rw [integerUnipotent_map] at invariance
  dsimp only [realFunction]
  rw [add_comm parameter 3, unipotent_add, mul_assoc, Height.atInfinity_mul, ← mul_assoc]
  exact invariance

theorem conjugate_unipotent_congruence (point : IntegralBinaryGL) (parameter : IntegralAdeles) :
    point⁻¹ * binaryUnipotent (3 * parameter) * point ∈ integralCongruence := by
  change GeneralLinearGroup.map integralReduction _ = 1
  rw [map_mul, map_mul, map_inv, unipotent_map]
  have reduction : integralReduction (3 * parameter) = 0 := by
    rw [map_mul, show integralReduction (3 : IntegralAdeles) = 0 from
      (map_natCast integralReduction 3).trans (by decide), zero_mul]
  rw [reduction, unipotent_zero, mul_one, inv_mul_cancel]

theorem adelic_unipotent_decomposition (parameter : ℝ) (residue : ℕ) (quotient : IntegralAdeles) :
    binaryUnipotent ((parameter, integralEmbedding ((residue : IntegralAdeles) + 3 * quotient)) : Adeles) =
      GeneralLinearGroup.map rationalAdele (binaryUnipotent (residue : ℚ)) *
        atFinite (GeneralLinearGroup.map integralEmbedding (binaryUnipotent (3 * quotient))) *
        atInfinity (binaryUnipotent (parameter - residue)) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · fin_cases row <;> fin_cases column <;>
      simp [binaryUnipotent, atFinite, atInfinity,
        combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · fin_cases row <;> fin_cases column <;>
      simp [binaryUnipotent, atFinite, atInfinity,
        combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem conjugate_unipotent_factorization (point : IntegralBinaryGL) (realPoint : BinaryRealGL)
    (parameter : IntegralAdeles) :
    (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint) *
        atFinite (GeneralLinearGroup.map integralEmbedding (point⁻¹ * binaryUnipotent (3 * parameter) * point)) =
      atFinite (GeneralLinearGroup.map integralEmbedding (binaryUnipotent (3 * parameter))) *
        atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint := by
  rw [mul_assoc, ← atFinite_atInfinity_commute, ← mul_assoc, ← atFinite_mul, ← map_mul]
  congr 2
  rw [mul_assoc point⁻¹, mul_inv_cancel_left, map_mul, atFinite_mul]

theorem realize_residue (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) (parameter : ℝ)
    (residue : ℕ) (quotient : IntegralAdeles) :
    data.realize vector (binaryUnipotent
        ((parameter, integralEmbedding ((residue : IntegralAdeles) + 3 * quotient)) : Adeles) *
      (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint)) =
      realFunction data vector point realPoint (parameter - residue) := by
  rw [adelic_unipotent_decomposition]
  rw [mul_assoc, mul_assoc, ← mul_assoc (atInfinity (binaryUnipotent (parameter - residue))),
    ← atFinite_atInfinity_commute, mul_assoc, ← Height.atInfinity_mul]
  rw [← mul_assoc (atFinite (GeneralLinearGroup.map integralEmbedding (binaryUnipotent (3 * quotient)))),
    ← conjugate_unipotent_factorization, data.leftRational]
  exact realize_right_fixed data vector fixed _ ⟨_, conjugate_unipotent_congruence point quotient, rfl⟩ _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentPeriodicity
