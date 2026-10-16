module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.RowBounds

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactDenominators

def denominatorSet (number : ℕ) : Set (Matrix (Fin 3) (Fin 3) FiniteAdeles) :=
  (fun matrix => (number : FiniteAdeles) • matrix) ⁻¹'
    Set.range (fun integral : Matrix (Fin 3) (Fin 3) IntegralAdeles =>
      integral.map integralEmbedding)

theorem denominatorSet_isOpen (number : ℕ) : IsOpen (denominatorSet number) := by
  unfold denominatorSet
  exact (TopologicalMatrices.matrixMap_isOpenEmbedding integralEmbedding
    integralEmbedding_isOpenEmbedding).isOpen_range.preimage
      (show Continuous (fun matrix : Matrix (Fin 3) (Fin 3) FiniteAdeles =>
        (number : FiniteAdeles) • matrix) from by
          apply continuous_pi
          intro row
          apply continuous_pi
          intro column
          exact continuous_const.mul ((continuous_apply column).comp (continuous_apply row)))

theorem denominatorSet_mono {first second : ℕ} (divides : first ∣ second) :
    denominatorSet first ⊆ denominatorSet second := by
  obtain ⟨factor, equality⟩ := divides
  rintro matrix ⟨integral, integralEquality⟩
  refine ⟨(factor : IntegralAdeles) • integral, ?_⟩
  apply Matrix.ext
  intro row column
  have coordinate := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) FiniteAdeles => matrix row column)
    integralEquality
  change integralEmbedding ((factor : IntegralAdeles) * integral row column) =
    (second : FiniteAdeles) * matrix row column
  rw [map_mul, map_natCast]
  change integralEmbedding (integral row column) = (first : FiniteAdeles) * matrix row column at coordinate
  rw [coordinate, equality, Nat.cast_mul]
  ring

theorem compact_denominator (set : Set (Matrix (Fin 3) (Fin 3) FiniteAdeles))
    (compact : IsCompact set) :
    ∃ number : ℕ, number ≠ 0 ∧ set ⊆ denominatorSet number := by
  let covers : {number : ℕ // number ≠ 0} → Set (Matrix (Fin 3) (Fin 3) FiniteAdeles) :=
    fun number => denominatorSet number.val
  have covered : set ⊆ ⋃ number, covers number := by
    intro matrix _
    obtain ⟨number, nonzero, integral, equality⟩ := FiniteMatrixBounds.common_denominator matrix
    exact Set.mem_iUnion.mpr ⟨⟨number, nonzero⟩, integral, equality⟩
  obtain ⟨finite, finiteCover⟩ := compact.elim_finite_subcover covers
    (fun number => denominatorSet_isOpen number.val) covered
  refine ⟨∏ number ∈ finite, (number : ℕ),
    Finset.prod_ne_zero_iff.mpr (fun number _ => number.property), ?_⟩
  intro matrix membership
  obtain ⟨number, numberMembership, cleared⟩ := Set.mem_iUnion₂.mp (finiteCover membership)
  have divides : (number : ℕ) ∣ ∏ number ∈ finite, (number : ℕ) :=
    Finset.dvd_prod_of_mem (fun number : {number : ℕ // number ≠ 0} => (number : ℕ)) numberMembership
  exact denominatorSet_mono divides cleared

theorem inverse_denominator (set : Set AdelicGL) (compact : IsCompact set) :
    ∃ number : ℕ, number ≠ 0 ∧ ∀ argument ∈ set,
      ∃ integral : Matrix (Fin 3) (Fin 3) IntegralAdeles,
        integral.map integralEmbedding = (number : FiniteAdeles) • (finiteGroup argument).inv := by
  have continuous : Continuous (fun argument : AdelicGL => (finiteGroup argument).inv) :=
    Units.continuous_coe_inv.comp InducedContinuity.finiteGroup_continuous
  obtain ⟨number, nonzero, clears⟩ := compact_denominator _ (compact.image continuous)
  exact ⟨number, nonzero, fun argument membership => clears ⟨argument, membership, rfl⟩⟩

theorem compact_height_bound (set : Set AdelicGL) (compact : IsCompact set) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ argument ∈ set,
      ∀ integer : IntegralGL3, ∀ first second : Adeles, ∀ binary : BinaryAdelicGL,
      ∀ unit : Adelesˣ, ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      rationalGroup ((GeneralLinearGroup.map (Int.castRingHom ℚ) integer)⁻¹) * argument =
        planeUnipotent first second * planeLevi binary unit * compactElement →
      ‖fun index => (integer.inv 2 index : ℝ)‖ ≤ constant * (adeleNorm unit : ℝ) := by
  obtain ⟨number, nonzero, clears⟩ := inverse_denominator set compact
  have continuous : Continuous (fun argument : AdelicGL => (realGroup argument).inv) :=
    Units.continuous_coe_inv.comp InducedContinuity.realGroup_continuous
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨3 * (|bound| + 1) * (number : ℝ), by positivity, ?_⟩
  intro argument argumentMembership integer first second binary unit compactElement membership decomposition
  obtain ⟨integral, equality⟩ := clears argument argumentMembership
  have estimate := AdelicRowBounds.decomposition_height_bound integer argument number nonzero integral equality
    first second binary unit compactElement membership decomposition
  apply estimate.trans
  have inverseBound : ‖(realGroup argument).inv‖ ≤ |bound| + 1 :=
    (bounded argument argumentMembership).trans (by linarith [le_abs_self bound])
  gcongr

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.CompactDenominators
