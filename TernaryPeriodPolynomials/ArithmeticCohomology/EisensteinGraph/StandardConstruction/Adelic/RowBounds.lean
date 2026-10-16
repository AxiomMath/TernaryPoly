module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FiniteMatrixBounds

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicRowBounds

theorem integer_row_primitive (integer : IntegralGL3) :
    ∃ coefficients : Fin 3 → ℤ, ∑ index, integer.inv 2 index * coefficients index = 1 := by
  refine ⟨fun index => integer.val index 2, ?_⟩
  exact congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℤ => matrix 2 2) integer.inv_val

theorem decomposition_rows (integer : IntegralGL3) (argument : AdelicGL)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL)
    (decomposition : rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ) integer)⁻¹) * argument =
      planeUnipotent first second * planeLevi binary unit * compact) :
    ((fun index => (integer.inv 2 index : ℝ)) ᵥ* (realGroup argument).val =
      unit.val.1 • (realGroup compact).val 2) ∧
    ((fun index => (integer.inv 2 index : FiniteAdeles)) ᵥ* (finiteGroup argument).val =
      unit.val.2 • (finiteGroup compact).val 2) := by
  have rows := (congrArg (fun matrix : AdelicGL => matrix.val 2) decomposition).trans
    (RealRowBounds.plane_lastRow first second binary unit compact)
  constructor
  · funext column
    have equality := congrArg Prod.fst (congrFun rows column)
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul,
      Pi.smul_apply, smul_eq_mul] at equality
    change (∑ index, ((integer.inv 2 index : ℚ) : ℝ) * (argument.val index column).1) =
      unit.val.1 * (compact.val 2 column).1 at equality
    change (∑ index, (integer.inv 2 index : ℝ) * (argument.val index column).1) =
      unit.val.1 * (compact.val 2 column).1
    simpa only [Rat.cast_intCast] using equality
  · funext column
    have equality := congrArg Prod.snd (congrFun rows column)
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Prod.snd_sum, Prod.snd_mul,
      Pi.smul_apply, smul_eq_mul] at equality
    change (∑ index, algebraMap ℚ FiniteAdeles (integer.inv 2 index : ℚ) *
      (argument.val index column).2) = unit.val.2 * (compact.val 2 column).2 at equality
    change (∑ index, (integer.inv 2 index : FiniteAdeles) * (argument.val index column).2) =
      unit.val.2 * (compact.val 2 column).2
    simpa only [map_intCast] using equality

theorem decomposition_height_bound (integer : IntegralGL3) (argument : AdelicGL)
    (number : ℕ) (nonzero : number ≠ 0) (integralInverse : Matrix (Fin 3) (Fin 3) IntegralAdeles)
    (inverseEquality : integralInverse.map integralEmbedding =
      (number : FiniteAdeles) • (finiteGroup argument).inv)
    (first second : Adeles) (binary : BinaryAdelicGL) (unit : Adelesˣ) (compact : AdelicGL)
    (membership : inMaximalCompact compact)
    (decomposition : rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ) integer)⁻¹) * argument =
      planeUnipotent first second * planeLevi binary unit * compact) :
    ‖fun index => (integer.inv 2 index : ℝ)‖ ≤
      (3 * ‖(realGroup argument).inv‖ * (number : ℝ)) * (adeleNorm unit : ℝ) := by
  obtain ⟨realRows, finiteRows⟩ := decomposition_rows integer argument first second binary unit compact decomposition
  obtain ⟨integralCompact, compactEquality⟩ := membership.2
  have finiteIntegral := FiniteMatrixBounds.primitive_row_denominator (integer.inv 2)
    (integer_row_primitive integer) (finiteGroup argument) number integralInverse inverseEquality
    (Units.map (RingHom.snd ℝ FiniteAdeles).toMonoidHom unit) integralCompact
    (by
      change _ = unit.val.2 • (GeneralLinearGroup.map integralEmbedding integralCompact).val 2
      rw [compactEquality]
      exact finiteRows)
  have integral : (((number : ℤ) : Adeles) * unit.inv).2 ∈ Set.range integralEmbedding := by
    change (number : FiniteAdeles) * unit.inv.2 ∈ Set.range integralEmbedding at finiteIntegral
    change (((number : ℤ) : FiniteAdeles) * unit.inv.2) ∈ Set.range integralEmbedding
    simpa only [Int.cast_natCast] using finiteIntegral
  have normLower := IntegralIdeleBound.norm_lower_bound unit (number : ℤ)
    (Int.natCast_ne_zero.mpr nonzero) integral
  rw [Int.cast_natCast,
    abs_of_nonneg (show (0 : ℝ) ≤ (number : ℝ) from Nat.cast_nonneg number)] at normLower
  have realUnitBound : |unit.val.1| ≤ (adeleNorm unit : ℝ) * (number : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero nonzero))).mp normLower
  have compactBound : ‖unit.val.1 • (realGroup compact).val 2‖ ≤ |unit.val.1| :=
    RealRowBounds.scaled_orthogonal_row_bound
      (Units.map (RingHom.fst ℝ FiniteAdeles).toMonoidHom unit) (realGroup compact) membership.1 2
  have rowBound := RealRowBounds.row_recover_bound
    (fun index => (integer.inv 2 index : ℝ)) (realGroup argument)
  rw [realRows] at rowBound
  calc
    ‖fun index => (integer.inv 2 index : ℝ)‖ ≤
        3 * ‖unit.val.1 • (realGroup compact).val 2‖ * ‖(realGroup argument).inv‖ := rowBound
    _ ≤ 3 * ((adeleNorm unit : ℝ) * (number : ℝ)) * ‖(realGroup argument).inv‖ := by
      gcongr
      exact compactBound.trans realUnitBound
    _ = _ := by ring

theorem argument_height_bound (argument : AdelicGL) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ integer : IntegralGL3, ∀ first second : Adeles, ∀ binary : BinaryAdelicGL,
      ∀ unit : Adelesˣ, ∀ compact : AdelicGL, inMaximalCompact compact →
      rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ) integer)⁻¹) * argument =
        planeUnipotent first second * planeLevi binary unit * compact →
      ‖fun index => (integer.inv 2 index : ℝ)‖ ≤ constant * (adeleNorm unit : ℝ) := by
  obtain ⟨number, nonzero, integralInverse, inverseEquality⟩ :=
    FiniteMatrixBounds.common_denominator (finiteGroup argument).inv
  refine ⟨3 * ‖(realGroup argument).inv‖ * (number : ℝ), ?_, ?_⟩
  · have inversePositive : 0 < ‖(realGroup argument).inv‖ := by
      apply norm_pos_iff.mpr
      intro zero
      have identity := (realGroup argument).inv_val
      rw [zero, zero_mul] at identity
      exact zero_ne_one identity
    exact mul_pos (mul_pos (by norm_num) inversePositive)
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero nonzero))
  · intro integer first second binary unit compact membership decomposition
    exact decomposition_height_bound integer argument number nonzero integralInverse inverseEquality
      first second binary unit compact membership decomposition

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicRowBounds
