module

public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.GroupSecondCohomology
public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.Descent
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

@[expose] public section

noncomputable section
namespace TernaryPoly.VirtuallyFreeSecondCohomology
open CategoryTheory CategoryTheory.Limits

variable {G I : Type} [Group G]

/-- An actual finite-index free subgroup forces rational H² to vanish for every representation. -/
theorem isZero_H2 (H : Subgroup G) [H.FiniteIndex] (e : FreeGroup I ≃* H)
    (A : Rep ℚ G) : IsZero (groupCohomology A 2) := by
  apply RationalCohomologyDescent.finiteIndex_isZero H A 2
  let B := Rep.res e.toMonoidHom (Rep.res H.subtype A)
  have hz : IsZero (groupCohomology B 2) := FreeGroupSecondCohomology.isZero_H2 B
  let iso : groupCohomology B 2 ≅ groupCohomology (Rep.res H.subtype A) 2 :=
    groupCohomology.mapIso e (LinearEquiv.refl ℚ _) (fun _ => rfl) 2
  exact hz.of_iso iso.symm

/-- The basis-free interface for an actual finite-index free subgroup. -/
theorem isZero_H2_of_isFreeGroup (H : Subgroup G) [H.FiniteIndex] [IsFreeGroup H]
    (A : Rep ℚ G) : IsZero (groupCohomology A 2) :=
  isZero_H2 H (IsFreeGroup.mulEquiv H) A

end TernaryPoly.VirtuallyFreeSecondCohomology
