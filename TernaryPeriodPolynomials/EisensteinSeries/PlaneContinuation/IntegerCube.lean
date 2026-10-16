module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.TorusPeriodization

@[expose] public section


open MeasureTheory TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerCube

def integerCast : (Coordinate → ℤ) →+ (Coordinate → ℝ) where
  toFun integer := fun coordinate => (integer coordinate : ℝ)
  map_zero' := by ext coordinate; exact Int.cast_zero
  map_add' _ _ := by ext coordinate; exact Int.cast_add _ _

scoped instance integerAction : AddAction (Coordinate → ℤ) (Coordinate → ℝ) :=
  AddAction.compHom (Coordinate → ℝ) integerCast

scoped instance integerMeasurable : MeasurableConstVAdd (Coordinate → ℤ) (Coordinate → ℝ) :=
  ⟨fun _ => measurable_const.add measurable_id⟩

scoped instance integerInvariant : VAddInvariantMeasure (Coordinate → ℤ) (Coordinate → ℝ) volume :=
  ⟨fun integer _ _ => measure_preimage_add volume (integerCast integer) _⟩

def cube : Set (Coordinate → ℝ) := {vector | ∀ coordinate, vector coordinate ∈ Set.Ioc 0 1}

theorem cube_measurable : MeasurableSet cube := by
  have equality : cube = ⋂ coordinate : Coordinate, {vector : Coordinate → ℝ | vector coordinate ∈ Set.Ioc 0 1} := by
    ext vector
    simp [cube]
  rw [equality]
  exact MeasurableSet.iInter (fun coordinate => measurableSet_Ioc.preimage (measurable_pi_apply coordinate))

theorem exists_representative (vector : Coordinate → ℝ) : ∃ integer : Coordinate → ℤ, integer +ᵥ vector ∈ cube := by
  refine ⟨fun coordinate => 1 - ⌈vector coordinate⌉, fun coordinate => ?_⟩
  change 0 < ((1 - ⌈vector coordinate⌉ : ℤ) : ℝ) + vector coordinate ∧
    ((1 - ⌈vector coordinate⌉ : ℤ) : ℝ) + vector coordinate ≤ 1
  push_cast
  have lower := Int.le_ceil (vector coordinate)
  have upper := Int.ceil_lt_add_one (vector coordinate)
  constructor <;> linarith

theorem representative_unique (vector : Coordinate → ℝ) (first second : Coordinate → ℤ)
    (firstMembership : first +ᵥ vector ∈ cube) (secondMembership : second +ᵥ vector ∈ cube) : first = second := by
  funext coordinate
  have firstInterval : 0 < (first coordinate : ℝ) + vector coordinate ∧
      (first coordinate : ℝ) + vector coordinate ≤ 1 := firstMembership coordinate
  have secondInterval : 0 < (second coordinate : ℝ) + vector coordinate ∧
      (second coordinate : ℝ) + vector coordinate ≤ 1 := secondMembership coordinate
  have lower : ((first coordinate - second coordinate : ℤ) : ℝ) > -1 := by push_cast; linarith
  have upper : ((first coordinate - second coordinate : ℤ) : ℝ) < 1 := by push_cast; linarith
  have integerLower : first coordinate - second coordinate > (-1 : ℤ) := by exact_mod_cast lower
  have integerUpper : first coordinate - second coordinate < (1 : ℤ) := by exact_mod_cast upper
  omega

theorem cube_fundamental : IsAddFundamentalDomain (Coordinate → ℤ) cube volume := by
  apply IsAddFundamentalDomain.mk' cube_measurable.nullMeasurableSet
  intro vector
  obtain ⟨integer, membership⟩ := exists_representative vector
  exact ⟨integer, membership, fun other otherMembership => representative_unique vector other integer otherMembership membership⟩

theorem integral_unfold (function : (Coordinate → ℝ) → ℂ) (integrable : Integrable function volume) :
    ∫ vector, function vector = ∑' integer : Coordinate → ℤ,
      ∫ vector in cube, function (integerCast integer + vector) :=
  cube_fundamental.integral_eq_tsum'' function integrable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerCube
