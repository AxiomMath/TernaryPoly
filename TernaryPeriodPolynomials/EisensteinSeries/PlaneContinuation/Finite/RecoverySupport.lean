module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralIdeleNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.FinitePrimitiveRecovery
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoverySupport

def IntegralMatrix (binary : BinaryFiniteGL) : Prop :=
  ∃ integer : Matrix (Fin 2) (Fin 2) IntegralAdeles, integer.map integralEmbedding = binary.val

theorem finite_frame_left (point : AdelicGL) (binary : BinaryFiniteGL) :
    (finiteGroup point).val * finite (FrameProfile.frame point * (atFinite binary).val) =
      columns (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) * binary.val := by
  unfold finite FrameProfile.frame
  rw [Matrix.map_mul, Matrix.map_mul]
  change (finiteGroup point).val * ((finiteGroup point)⁻¹.val *
    columns (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) * binary.val) = _
  have inverse : (finiteGroup point).val * (finiteGroup point)⁻¹.val = 1 := (finiteGroup point).val_inv
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, inverse, Matrix.one_mul]

theorem integralMatrix_of_frame (point : AdelicGL)
    (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryFiniteGL)
    (frameIntegral : finite (FrameProfile.frame point * (atFinite binary).val) ∈ Set.range CompactFiniteFrames.embedding) :
    IntegralMatrix binary := by
  obtain ⟨integerPoint, pointEquality⟩ := pointIntegral
  obtain ⟨integerFrame, frameEquality⟩ := frameIntegral
  change integerFrame.map integralEmbedding = finite (FrameProfile.frame point * (atFinite binary).val) at frameEquality
  have matrixEquality : integerPoint.val.map integralEmbedding = (finiteGroup point).val :=
    congrArg Units.val pointEquality
  have product : (integerPoint.val * integerFrame).map integralEmbedding =
      columns (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) * binary.val := by
    rw [Matrix.map_mul, matrixEquality, frameEquality, finite_frame_left]
  refine ⟨fun row column => (integerPoint.val * integerFrame) row.castSucc column, ?_⟩
  apply Matrix.ext
  intro row column
  change integralEmbedding ((integerPoint.val * integerFrame) row.castSucc column) = binary.val row column
  have entry := congrArg (fun value : Rectangular FiniteAdeles => value row.castSucc column) product
  calc
    _ = (columns (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) * binary.val) row.castSucc column := entry
    _ = binary.val row column := by
      fin_cases row <;> simp [columns, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem determinant_integral (binary : BinaryFiniteGL) (integral : IntegralMatrix binary) :
    (GeneralLinearGroup.det binary).val ∈ Set.range integralEmbedding := by
  obtain ⟨integer, equality⟩ := integral
  exact ⟨integer.det, (RingHom.map_det integralEmbedding integer).trans (congrArg Matrix.det equality)⟩

theorem norm_le_one (binary : BinaryFiniteGL) (integral : IntegralMatrix binary) :
    (adeleNorm (GeneralLinearGroup.det (atFinite binary)) : ℝ) ≤ 1 := by
  rw [Norm.det_atFinite]
  exact IntegralIdeleNorm.norm_le_one _ (determinant_integral binary integral)

theorem integralGroup_of_norm_one (binary : BinaryFiniteGL) (integral : IntegralMatrix binary)
    (normOne : (adeleNorm (GeneralLinearGroup.det (atFinite binary)) : ℝ) = 1) : binary ∈ integralGroup := by
  obtain ⟨integer, equality⟩ := integral
  rw [Norm.det_atFinite] at normOne
  obtain ⟨unit, unitEquality⟩ := IntegralIdeleNorm.integralUnit_of_norm_one (GeneralLinearGroup.det binary)
    (determinant_integral binary ⟨integer, equality⟩) normOne
  have determinantEquality : integer.det = unit.val := by
    apply integralEmbedding_injective
    exact ((RingHom.map_det integralEmbedding integer).trans (congrArg Matrix.det equality)).trans
      (congrArg Units.val unitEquality).symm
  have unitDeterminant : IsUnit integer.det := determinantEquality ▸ unit.isUnit
  have unitMatrix : IsUnit integer := (Matrix.isUnit_iff_isUnit_det integer).mpr unitDeterminant
  refine ⟨unitMatrix.unit, Units.ext ?_⟩
  change unitMatrix.unit.val.map integralEmbedding = binary.val
  simpa only [unitMatrix.unit_spec] using equality

theorem norm_lt_one (binary : BinaryFiniteGL) (integral : IntegralMatrix binary)
    (nonprimitive : binary ∉ integralGroup) :
    (adeleNorm (GeneralLinearGroup.det (atFinite binary)) : ℝ) < 1 :=
  lt_of_le_of_ne (norm_le_one binary integral) (fun equality =>
    nonprimitive (integralGroup_of_norm_one binary integral equality))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRecoverySupport
