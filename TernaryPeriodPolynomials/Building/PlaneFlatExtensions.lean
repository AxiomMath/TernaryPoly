module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.Building.PlaneFlatExtensions.Construction

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.PlaneFlatExtensions

theorem plane_flat_extensions : ∀ (n : ℕ) (D : InducingData n),
    ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f →
    ∃ F : ℂ → AdelicGL → ℂ, IsFlatSection D F ∧ F cohomologicalPoint = f := by
  intro degree data inputSection induced
  exact Helpers.planeHeight.flat_extension data inputSection induced

end TernaryPeriodPolynomials.PlaneFlatExtensions
