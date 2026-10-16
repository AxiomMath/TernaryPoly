module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Representation
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryCuspidalRep (cusp : CuspidalRepresentation) (degree : ℕ) : Rep ℂ BinaryRealGL :=
  Rep.of (X := binaryCuspidalValues cusp degree) (binaryCuspidalRepresentation cusp degree)

def binaryCocycleToGroupCocycle {degree : ℕ} (cusp : CuspidalRepresentation)
    (cycle : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : ∀ matrix, BinaryValues cusp degree (cycle matrix))
    (cocycle : ∀ first second argument, cycle (first * second) argument =
      cycle first argument + binaryCohomologicalAction degree first (cycle second) argument) :
    groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree) := by
  refine ⟨fun matrix => ⟨cycle matrix, cuspidal matrix⟩, ?_⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro first second
  apply Subtype.ext
  funext argument
  exact (cocycle first second argument).trans (add_comm _ _)

theorem binaryCocycleToGroupCocycle_H1_zero_iff {degree : ℕ}
    (cusp : CuspidalRepresentation)
    (cycle : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1))
    (cuspidal : ∀ matrix, BinaryValues cusp degree (cycle matrix))
    (cocycle : ∀ first second argument, cycle (first * second) argument =
      cycle first argument + binaryCohomologicalAction degree first (cycle second) argument) :
    groupCohomology.H1π (binaryCuspidalRep cusp degree)
      (binaryCocycleToGroupCocycle cusp cycle cuspidal cocycle) = 0 ↔
    ∃ values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1),
      BinaryValues cusp degree values ∧ ∀ matrix argument,
        cycle matrix argument = binaryCohomologicalAction degree matrix values argument -
          values argument := by
  rw [groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨values, boundary⟩
    refine ⟨values.val, values.property, ?_⟩
    intro matrix argument
    have equality := congrArg
      (fun vector : binaryCuspidalValues cusp degree => vector.val argument)
      (congrFun boundary matrix)
    exact equality.symm
  · rintro ⟨values, cuspidal_values, boundary⟩
    refine ⟨⟨values, cuspidal_values⟩, ?_⟩
    funext matrix
    apply Subtype.ext
    funext argument
    exact (boundary matrix argument).symm

theorem cohomological_exists_nonzero_H1 {degree : ℕ}
    (cusp : CuspidalRepresentation) (cohomological : Cohomological cusp degree) :
    ∃ cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree),
      groupCohomology.H1π (binaryCuspidalRep cusp degree) cycle ≠ 0 := by
  rcases cohomological with ⟨cycle, cuspidal, _, _, cocycle, nonboundary⟩
  refine ⟨binaryCocycleToGroupCocycle cusp cycle cuspidal cocycle, ?_⟩
  exact fun zero => nonboundary
    ((binaryCocycleToGroupCocycle_H1_zero_iff cusp cycle cuspidal cocycle).mp zero)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
