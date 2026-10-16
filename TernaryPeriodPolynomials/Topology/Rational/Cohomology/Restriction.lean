module

public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.RestrictionShapiro
public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.RestrictionNaturality

@[expose] public section


noncomputable section

namespace TernaryPoly.RationalCohomologyRestriction
open CategoryTheory
open RationalCohomologyDescent

variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (A : Rep.{0} ℚ G)

/-- The normalized corestriction, built from inverse Shapiro and the trace. -/
def normalizedCorestriction (n : ℕ) :
    groupCohomology (Rep.res H.subtype A) n ⟶ groupCohomology A n :=
  (groupCohomology.coindIso (Rep.res H.subtype A) n).inv ≫
    groupCohomology.map (MonoidHom.id G) (coindRetraction H A) n

/-- Actual finite-index restriction has the normalized trace as a left inverse
in every degree, for every rational representation. -/
theorem restriction_corestriction (n : ℕ) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n ≫
      normalizedCorestriction H A n = 𝟙 (groupCohomology A n) := by
  rw [restriction_eq_coind_shapiro]
  change (groupCohomology.map (MonoidHom.id G) (coindUnit H A) n ≫
      (groupCohomology.coindIso (Rep.res H.subtype A) n).hom) ≫
      ((groupCohomology.coindIso (Rep.res H.subtype A) n).inv ≫
        groupCohomology.map (MonoidHom.id G) (coindRetraction H A) n) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← groupCohomology.map_id_comp]
  exact (congrArg (fun f : A ⟶ A => groupCohomology.map (MonoidHom.id G) f n)
    (coindUnit_retraction H A)).trans (groupCohomology.map_id n)

/-- The literal group-cohomology restriction map is injective in every degree. -/
theorem restriction_injective (n : ℕ) :
    Function.Injective (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n) := by
  intro x y hxy
  have h := congrArg (fun z => normalizedCorestriction H A n z) hxy
  have hleft (z : groupCohomology A n) :
      normalizedCorestriction H A n
        (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n z) = z :=
    congrArg (fun f => f z) (restriction_corestriction H A n)
  simpa only [hleft] using h

/-- Vanishing after actual finite-index restriction detects vanishing of the
original rational cohomology class. -/
theorem restriction_eq_zero_iff (n : ℕ) (x : groupCohomology A n) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply restriction_injective H A n
    simpa only [map_zero] using hx
  · rintro rfl
    exact map_zero _

end TernaryPoly.RationalCohomologyRestriction
