module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.QuotientIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryProjectedEntries

theorem integral_eq_of_translate (data : CuspidalRepresentation) (vector : data.smooth)
    (coefficient : BinaryFiniteGL → ℂ) (evaluation : BinaryAdelicGL) (first second matrix : BinaryFiniteGL)
    (invariant : ∀ binary, coefficient (matrix * binary) = coefficient binary)
    (product : first * matrix = second) :
    (∫ binary : BinaryFiniteGL, coefficient binary * data.realize vector (evaluation * atFinite first * atFinite binary)
      ∂BinaryProductHaar.finiteMeasure) =
      ∫ binary : BinaryFiniteGL, coefficient binary * data.realize vector (evaluation * atFinite second * atFinite binary)
        ∂BinaryProductHaar.finiteMeasure := by
  rw [← integral_mul_left_eq_self (μ := BinaryProductHaar.finiteMeasure)
    (fun binary => coefficient binary * data.realize vector (evaluation * atFinite first * atFinite binary)) matrix]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro binary
  dsimp only
  rw [invariant]
  have equality : evaluation * atFinite first * atFinite (matrix * binary) =
      evaluation * atFinite second * atFinite binary := by
    rw [atFinite_mul]
    calc
      _ = evaluation * (atFinite first * atFinite matrix) * atFinite binary := by group
      _ = _ := by rw [← atFinite_mul, product]
  rw [equality]

theorem integral_factors {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (parameter : ℂ) (point : IntegralFiniteGL) (key : UniversalFiniteProfiles.Key data)
    (evaluation : BinaryAdelicGL) (first second : finiteCongruence)
    (equality : FiniteQuotientIntegral.finiteMap (RecoveryBinarySymmetry.quotient data) first =
      FiniteQuotientIntegral.finiteMap (RecoveryBinarySymmetry.quotient data) second) :
    FiniteCoefficientEvaluation.integral data vector (UniversalFiniteProfiles.boxes data key)
      parameter (GeneralLinearGroup.map integralEmbedding point) (evaluation * atFinite first.val) =
        FiniteCoefficientEvaluation.integral data vector (UniversalFiniteProfiles.boxes data key)
          parameter (GeneralLinearGroup.map integralEmbedding point) (evaluation * atFinite second.val) := by
  let firstIntegral := FiniteQuotientIntegral.levelEquiv.symm first
  let secondIntegral := FiniteQuotientIntegral.levelEquiv.symm second
  have firstValue : GeneralLinearGroup.map integralEmbedding firstIntegral.val = first.val :=
    congrArg Subtype.val (FiniteQuotientIntegral.levelEquiv.apply_symm_apply first)
  have secondValue : GeneralLinearGroup.map integralEmbedding secondIntegral.val = second.val :=
    congrArg Subtype.val (FiniteQuotientIntegral.levelEquiv.apply_symm_apply second)
  have quotientEquality : RecoveryBinarySymmetry.quotient data firstIntegral.val =
      RecoveryBinarySymmetry.quotient data secondIntegral.val := congrArg Subtype.val equality
  have membership : firstIntegral.val⁻¹ * secondIntegral.val ∈ (RecoveryBinarySymmetry.quotient data).ker := by
    change RecoveryBinarySymmetry.quotient data (firstIntegral.val⁻¹ * secondIntegral.val) = 1
    rw [map_mul, map_inv, quotientEquality, inv_mul_cancel]
  apply integral_eq_of_translate data.cusp vector _ evaluation first.val second.val
    (GeneralLinearGroup.map integralEmbedding (firstIntegral.val⁻¹ * secondIntegral.val))
  · exact RecoveryBinarySymmetry.coefficient_kernel data parameter point key _ membership
  · rw [map_mul, map_inv, firstValue, secondValue, mul_inv_cancel_left]

theorem realize_eq_sum {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
      (RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding point)) key)
      (RecoveryCoefficients.coefficient_integrable data parameter halfPlane
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) index vector).val evaluation =
        (Fintype.card (BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data)) : ℂ)⁻¹ *
          ∑ residue : BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data),
            FiniteCoefficientEvaluation.integral data vector.val (UniversalFiniteProfiles.boxes data key)
              parameter (GeneralLinearGroup.map integralEmbedding point)
                (evaluation * atFinite (FiniteQuotientIntegral.finiteRepresentative (RecoveryBinarySymmetry.quotient data) residue).val) := by
  rw [ProjectedCoefficientIntegral.recovery_realize data parameter halfPlane
    (GeneralLinearGroup.map integralEmbedding point) ⟨point, rfl⟩ key index vector evaluation]
  apply FiniteQuotientIntegral.level_integral
  · exact (ProjectedCoefficientIntegral.joint_integrable data.cusp vector.val _
      (RecoveryCoefficients.coefficient_integrable data parameter halfPlane
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) evaluation).integral_prod_right
  · exact integral_factors data vector.val parameter point key evaluation

def modeOperator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (index : ℤ) :
    fixedMode data.cusp finiteCongruence index →ₗ[ℂ] fixedMode data.cusp finiteCongruence index :=
  modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
    (RecoveryCoefficients.coefficient data parameter (atFinite (GeneralLinearGroup.map integralEmbedding point)) key)
    (RecoveryCoefficients.coefficient_integrable data parameter (by linarith)
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) index

theorem exists_meromorphic {degree : ℕ} (data : InducingData degree) (point : IntegralFiniteGL)
    (key : UniversalFiniteProfiles.Key data) (index : ℤ)
    (vector : fixedMode data.cusp finiteCongruence index) (evaluation : BinaryAdelicGL) :
    ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
      ∀ parameter (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re),
        continuation parameter = data.cusp.realize (modeOperator data parameter halfPlane point key index vector).val evaluation := by
  have fixed : vector.val.val ∈ fixedSubspace data.cusp finiteCongruence :=
    ((mem_fixedMode_iff data.cusp finiteCongruence index vector.val).mp vector.property).1
  choose continuations meromorphic equalities using
    fun residue : BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data) =>
      FiniteCoefficientEvaluation.recovery_exists_meromorphic data vector.val fixed
        (GeneralLinearGroup.map integralEmbedding point) key
        (evaluation * atFinite (FiniteQuotientIntegral.finiteRepresentative (RecoveryBinarySymmetry.quotient data) residue).val)
  refine ⟨fun parameter => (Fintype.card (BinaryQuotientAverage.image (RecoveryBinarySymmetry.quotient data)) : ℂ)⁻¹ *
    ∑ residue, continuations residue parameter, ?_, ?_⟩
  · intro parameter
    exact analyticAt_const.meromorphicAt.mul (MeromorphicAt.fun_sum (fun residue _ => meromorphic residue parameter))
  · intro parameter halfPlane
    dsimp only
    rw [modeOperator, realize_eq_sum data parameter (by linarith) point key index vector evaluation]
    congr 1
    apply Finset.sum_congr rfl
    intro residue _
    exact equalities residue parameter halfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryProjectedEntries
