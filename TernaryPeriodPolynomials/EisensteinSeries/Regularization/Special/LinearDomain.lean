module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.MeasurableGroupDomain
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

@[expose] public section


open Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance realSpecialLinear_locallyCompact : LocallyCompactSpace (SpecialLinearGroup (Fin 3) ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  exact SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance realSpecialLinear_polish : PolishSpace (SpecialLinearGroup (Fin 3) ℝ) := by
  let : PolishSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (PolishSpace (Fin 3 → Fin 3 → ℝ))
  exact SpecialLinearGroup.isClosedEmbedding_val.polishSpace

instance realSpecialLinear_measurableSpace : MeasurableSpace (SpecialLinearGroup (Fin 3) ℝ) :=
  borel (SpecialLinearGroup (Fin 3) ℝ)

instance realSpecialLinear_borelSpace : BorelSpace (SpecialLinearGroup (Fin 3) ℝ) := ⟨rfl⟩

def integerSpecialLinearSubgroup : Subgroup (SpecialLinearGroup (Fin 3) ℝ) :=
  (SpecialLinearGroup.map (Int.castRingHom ℝ)).range

instance integerSpecialLinearSubgroup_discrete : DiscreteTopology integerSpecialLinearSubgroup :=
  inferInstanceAs (DiscreteTopology (SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin 3)).range)

instance integerSpecialLinearSubgroup_countable : Countable integerSpecialLinearSubgroup := by
  let : Countable (Matrix (Fin 3) (Fin 3) ℤ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℤ))
  let : Countable (SpecialLinearGroup (Fin 3) ℤ) := inferInstanceAs
    (Countable {matrix : Matrix (Fin 3) (Fin 3) ℤ // matrix.det = 1})
  exact Set.countable_range (SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin 3))

noncomputable def realSpecialLinearHaar : Measure (SpecialLinearGroup (Fin 3) ℝ) := Measure.haar

instance realSpecialLinearHaar_isHaar : realSpecialLinearHaar.IsHaarMeasure :=
  inferInstanceAs (Measure.IsHaarMeasure (Measure.haar : Measure (SpecialLinearGroup (Fin 3) ℝ)))

theorem integerSpecialLinear_measurable_domain :
    ∃ domain : Set (SpecialLinearGroup (Fin 3) ℝ), MeasurableSet domain ∧
      IsFundamentalDomain integerSpecialLinearSubgroup domain realSpecialLinearHaar :=
  discrete_subgroup_measurable_fundamental_domain integerSpecialLinearSubgroup realSpecialLinearHaar

noncomputable def integerSpecialLinearDomain : Set (SpecialLinearGroup (Fin 3) ℝ) :=
  Classical.choose integerSpecialLinear_measurable_domain

theorem integerSpecialLinearDomain_measurable : MeasurableSet integerSpecialLinearDomain :=
  (Classical.choose_spec integerSpecialLinear_measurable_domain).1

theorem integerSpecialLinearDomain_fundamental :
    IsFundamentalDomain integerSpecialLinearSubgroup integerSpecialLinearDomain realSpecialLinearHaar :=
  (Classical.choose_spec integerSpecialLinear_measurable_domain).2

instance integerSpecialLinear_hasFundamentalDomain :
    HasFundamentalDomain integerSpecialLinearSubgroup (SpecialLinearGroup (Fin 3) ℝ) realSpecialLinearHaar :=
  integerSpecialLinearDomain_fundamental.hasFundamentalDomain realSpecialLinearHaar

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
