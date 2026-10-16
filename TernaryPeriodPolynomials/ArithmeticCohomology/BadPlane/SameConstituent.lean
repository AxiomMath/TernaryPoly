module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent.BoundarySupport

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative

theorem bad_plane_same_constituent_representative : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
    ∀ ξ : boundarySummand D .plane, VanishesOnGood n D.chi .plane ξ.val →
    BadPlaneRepresentative D ξ := by
  intro degree _ data _ boundary_class vanishing
  obtain ⟨source, cycle, source_closed, evaluation, class_eq⟩ :=
    Helpers.boundary_summand_has_representative data .plane boundary_class
  refine ⟨Helpers.badSource source, Helpers.flagCutCycle false cycle,
    Helpers.bad_source_cocycle source_closed, Helpers.bad_source_evaluates evaluation,
    ?_, Helpers.bad_source_support source⟩
  rw [Helpers.bad_cut_same_class cycle (by simpa only [class_eq] using vanishing), class_eq]

end TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative
