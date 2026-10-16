module

public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenAlgebra
public import TernaryPeriodPolynomials.ModularForm.Periods.SolutionTenDimension
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenLinearIndependence
public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenCuspBridge
public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodRelations

@[expose] public section



/-!
# Assembly of `example_degree_ten`

Final assembly of the target `TernaryPeriodPolynomials.example_degree_ten`
from its already-proved pieces:

* Conjunct 1 (universal over `F`) is a flat ten-way conjunction, closed directly by the
  eight `R`-generic algebra/membership facts of `ExampleDegreeTenAlgebra.lean` together with
  the two explicit-`F` facts `linearIndependent_tenSolution`/`solutionSpace_ten_eq_span` of
  `ExampleDegreeTenLinearIndependence.lean`/`SolutionTenDimension.lean`.
* Conjunct 2 (the cusp-form statement) splits into the odd half `conjunct2_odd`
  (`ExampleDegreeTenCuspBridge.lean`) and the even half `conjunct2_even`
  (`EvenPeriodRelations.lean`).
-/

noncomputable section
open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument.CuspForms

/-- Assembled proof of the target `example_degree_ten`. -/
theorem example_degree_ten_proof :
    (∀ (F : Type) [Field F] [CharZero F],
      symmetricTenPeriod F ∈ oddPeriodSpace F 10 ∧ alternatingTenPeriod F ∈ evenPeriodSpace F 10 ∧
      bind₁ ![X 1, X 0] (symmetricTenPeriod F) = symmetricTenPeriod F ∧
      bind₁ ![-X 0, X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 0, -X 1] (symmetricTenPeriod F) = -symmetricTenPeriod F ∧
      bind₁ ![X 1, X 0] (alternatingTenPeriod F) = -alternatingTenPeriod F ∧
      bind₁ ![-X 0, X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      bind₁ ![X 0, -X 1] (alternatingTenPeriod F) = alternatingTenPeriod F ∧
      LinearIndependent F ![symmetricTenSolution F, alternatingTenSolution F] ∧
      Submodule.span F {symmetricTenSolution F, alternatingTenSolution F} = solutionSpace F 10) ∧
    ∀ h : CuspForm levelOne 12, h ≠ 0 →
      (∃ c : ℂ, c ≠ 0 ∧ symmetricTenPeriod ℂ = c • oddPeriodPart 10 h) ∧
      (∃ c : ℂ, c ≠ 0 ∧ alternatingTenPeriod ℂ = c • normalizedEvenPeriodPart 10 h) := by
  refine ⟨?_, ?_⟩
  · intro F _ _
    exact ⟨symmetricTenPeriod_mem_oddPeriodSpace, alternatingTenPeriod_mem_evenPeriodSpace,
      symmetricTenPeriod_swap, symmetricTenPeriod_oddX, symmetricTenPeriod_oddY,
      alternatingTenPeriod_antiswap, alternatingTenPeriod_evenX, alternatingTenPeriod_evenY,
      linearIndependent_tenSolution F, solutionSpace_ten_eq_span F⟩
  · intro h hh0
    exact ⟨conjunct2_odd hh0, conjunct2_even hh0⟩

end TernaryPeriodPolynomials.Argument.CuspForms
