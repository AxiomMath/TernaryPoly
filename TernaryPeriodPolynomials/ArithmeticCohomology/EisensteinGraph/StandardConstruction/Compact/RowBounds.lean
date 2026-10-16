module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.RowBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedContinuity

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactRowBounds

theorem integral_left_denominator (argument : FiniteGL) (number : ℕ)
    (integralInverse : Matrix (Fin 3) (Fin 3) IntegralAdeles)
    (inverseEquality : integralInverse.map integralEmbedding =
      (number : FiniteAdeles) • argument.inv)
    (left : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    (integralInverse * left.inv).map integralEmbedding =
      (number : FiniteAdeles) •
        (GeneralLinearGroup.map integralEmbedding left * argument).inv := by
  rw [Matrix.map_mul, inverseEquality, Matrix.smul_mul]
  rfl

theorem unipotent_denominator (argument : AdelicGL) (number : ℕ)
    (integralInverse : Matrix (Fin 3) (Fin 3) IntegralAdeles)
    (inverseEquality : integralInverse.map integralEmbedding =
      (number : FiniteAdeles) • (finiteGroup argument).inv)
    (coordinates : Adeles × Adeles)
    (membership : coordinates ∈
      InducedContinuity.additiveCompact ×ˢ InducedContinuity.additiveCompact) :
    ∃ integral : Matrix (Fin 3) (Fin 3) IntegralAdeles,
      integral.map integralEmbedding = (number : FiniteAdeles) •
        (finiteGroup (lineUnipotent coordinates.1 coordinates.2 * argument)).inv := by
  obtain ⟨first, firstEquality⟩ := membership.1.2
  obtain ⟨second, secondEquality⟩ := membership.2.2
  refine ⟨integralInverse * (lineUnipotent first second).inv, ?_⟩
  have unipotentEquality : GeneralLinearGroup.map integralEmbedding (lineUnipotent first second) =
      finiteGroup (lineUnipotent coordinates.1 coordinates.2) := by
    rw [LineDecomposition.map_lineUnipotent, firstEquality, secondEquality]
    exact (LineDecomposition.map_lineUnipotent (RingHom.snd ℝ FiniteAdeles) _ _).symm
  rw [map_mul, ← unipotentEquality]
  exact integral_left_denominator _ number integralInverse inverseEquality _

theorem real_inverse_continuous (argument : AdelicGL) :
    Continuous (fun coordinates : Adeles × Adeles =>
      (realGroup (lineUnipotent coordinates.1 coordinates.2 * argument)).inv) :=
  Units.continuous_coe_inv.comp
    (InducedContinuity.realGroup_continuous.comp
      (InducedContinuity.lineUnipotent_continuous.mul continuous_const))

theorem compact_height_bound (argument : AdelicGL) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ coordinates ∈ InducedContinuity.additiveCompact ×ˢ InducedContinuity.additiveCompact,
      ∀ integer : IntegralGL3, ∀ first second : Adeles, ∀ binary : BinaryAdelicGL,
      ∀ unit : Adelesˣ, ∀ compact : AdelicGL, inMaximalCompact compact →
      rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ) integer)⁻¹) *
          (lineUnipotent coordinates.1 coordinates.2 * argument) =
        planeUnipotent first second * planeLevi binary unit * compact →
      ‖fun index => (integer.inv 2 index : ℝ)‖ ≤ constant * (adeleNorm unit : ℝ) := by
  obtain ⟨number, nonzero, integralInverse, inverseEquality⟩ :=
    FiniteMatrixBounds.common_denominator (finiteGroup argument).inv
  obtain ⟨bound, bounded⟩ :=
    (InducedContinuity.additiveCompact_isCompact.prod
      InducedContinuity.additiveCompact_isCompact).exists_bound_of_continuousOn
        (real_inverse_continuous argument).continuousOn
  refine ⟨3 * (|bound| + 1) * (number : ℝ), by positivity, ?_⟩
  intro coordinates membership integer first second binary unit compact compactMembership decomposition
  obtain ⟨integral, equality⟩ :=
    unipotent_denominator argument number integralInverse inverseEquality coordinates membership
  have estimate := AdelicRowBounds.decomposition_height_bound integer
    (lineUnipotent coordinates.1 coordinates.2 * argument) number nonzero integral equality
    first second binary unit compact compactMembership decomposition
  apply estimate.trans
  have inverseBound : ‖(realGroup (lineUnipotent coordinates.1 coordinates.2 * argument)).inv‖ ≤
      |bound| + 1 := (bounded coordinates membership).trans (by linarith [le_abs_self bound])
  gcongr

theorem domain_height_bound (argument : AdelicGL) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain,
      ∀ integer : IntegralGL3, ∀ first second : Adeles, ∀ binary : BinaryAdelicGL,
      ∀ unit : Adelesˣ, ∀ compact : AdelicGL, inMaximalCompact compact →
      rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ) integer)⁻¹) *
          (lineUnipotent coordinates.1 coordinates.2 * argument) =
        planeUnipotent first second * planeLevi binary unit * compact →
      ‖fun index => (integer.inv 2 index : ℝ)‖ ≤ constant * (adeleNorm unit : ℝ) := by
  obtain ⟨constant, positive, bounded⟩ := compact_height_bound argument
  exact ⟨constant, positive, fun coordinates membership => bounded coordinates
    (Set.prod_mono InducedContinuity.additiveDomain_subset_compact
      InducedContinuity.additiveDomain_subset_compact membership)⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactRowBounds
