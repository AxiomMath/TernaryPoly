module

public import TernaryPeriodPolynomials.Analysis.CompatibleMeasureGluing

@[expose] public section


namespace TernaryPoly.CompatibleMeasureGluing
open MeasureTheory Set
variable {X : Type*} [MeasurableSpace X]

/-- A further compatible chart agrees with the measure glued from any countable subcover. -/
theorem glued_restrict_other (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i))
    (hcover : (⋃ i, U i) = univ) (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i))
    (V : Set X) (ν : Measure X)
    (hν : ∀ i, (μ i).restrict V = ν.restrict (U i)) :
    (glued U μ).restrict V = ν := by
  apply unique U hcover
  intro i
  rw [Measure.restrict_comm (hU i), glued_restrict U hU hcover μ hcompat i, hν i]

end TernaryPoly.CompatibleMeasureGluing
