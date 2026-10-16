module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.ShrinkingCover

@[expose] public section


open Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def integerSpecialLinearReduction : SpecialLinearGroup (Fin 3) ℤ →* SpecialLinearGroup (Fin 3) (ZMod 3) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

def principalIntegerSpecialLinear : Subgroup (SpecialLinearGroup (Fin 3) ℤ) :=
  integerSpecialLinearReduction.ker

def principalRealSpecialLinear : Subgroup (SpecialLinearGroup (Fin 3) ℝ) :=
  principalIntegerSpecialLinear.map (SpecialLinearGroup.map (Int.castRingHom ℝ))

theorem principalRealSpecialLinear_le_integer : principalRealSpecialLinear ≤ integerSpecialLinearSubgroup := by
  rintro matrix ⟨integral, _, represents⟩
  exact ⟨integral, represents⟩

instance principalRealSpecialLinear_countable : Countable principalRealSpecialLinear :=
  Function.Injective.countable (Subgroup.inclusion_injective principalRealSpecialLinear_le_integer)

instance principalRealSpecialLinear_discrete : DiscreteTopology principalRealSpecialLinear := by
  have embedding : Topology.IsEmbedding (Subgroup.inclusion principalRealSpecialLinear_le_integer) :=
    (Topology.IsEmbedding.of_comp_iff (f := Subgroup.inclusion principalRealSpecialLinear_le_integer)
      (g := (Subtype.val : integerSpecialLinearSubgroup → SpecialLinearGroup (Fin 3) ℝ))
      Topology.IsEmbedding.subtypeVal).mp Topology.IsEmbedding.subtypeVal
  exact embedding.discreteTopology

instance integerSpecialLinearReduction_range_finite : Finite integerSpecialLinearReduction.range := by
  let : Finite (Matrix (Fin 3) (Fin 3) (ZMod 3)) := inferInstanceAs (Finite (Fin 3 → Fin 3 → ZMod 3))
  let : Finite (SpecialLinearGroup (Fin 3) (ZMod 3)) := inferInstanceAs
    (Finite {matrix : Matrix (Fin 3) (Fin 3) (ZMod 3) // matrix.det = 1})
  infer_instance

noncomputable def integerSpecialLinearReductionRepresentative (residue : integerSpecialLinearReduction.range) :
    SpecialLinearGroup (Fin 3) ℤ := Classical.choose residue.property

theorem integerSpecialLinearReductionRepresentative_spec (residue : integerSpecialLinearReduction.range) :
    integerSpecialLinearReduction (integerSpecialLinearReductionRepresentative residue) = residue.val :=
  Classical.choose_spec residue.property

theorem integerSpecialLinearReduction_factor (matrix : SpecialLinearGroup (Fin 3) ℤ) :
    ∃ residue : integerSpecialLinearReduction.range, ∃ principal : principalIntegerSpecialLinear,
      matrix = integerSpecialLinearReductionRepresentative residue * principal.val := by
  let residue : integerSpecialLinearReduction.range := ⟨integerSpecialLinearReduction matrix, matrix, rfl⟩
  let principal := (integerSpecialLinearReductionRepresentative residue)⁻¹ * matrix
  have member : principal ∈ principalIntegerSpecialLinear := by
    change integerSpecialLinearReduction principal = 1
    rw [map_mul, map_inv, integerSpecialLinearReductionRepresentative_spec]
    exact inv_mul_cancel _
  exact ⟨residue, ⟨principal, member⟩, (mul_inv_cancel_left _ _).symm⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
