module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MV

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits TopologicalSpace
open SingularLocalSupport SingularLocalCompactMV EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  [T2Space B] [LocallyCompactSpace B] (U D : Opens B) (hUD : U ⊔ D = ⊤)

include hUD

/-- Vanishing at the two opens and in the next intersection degree propagates through the actual
compact-support Mayer–Vietoris sequence. -/
theorem compactCohomology_isZero_of_twoOpen (a : ℕ)
    (hU : IsZero (compactCohomology (restrictedProjection p U) V a))
    (hD : IsZero (compactCohomology (restrictedProjection p D) V a))
    (hI : IsZero (compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V (a+1))) :
    IsZero (compactCohomology p V a) :=
  (compactAmbientSegment_exact p V U D hUD a).isZero_of_both_isZero
    ((biprod_isZero_iff _ _).mpr ⟨hU,hD⟩) hI

/-- Above-dimension compact cohomology vanishing propagates over an actual two-open cover. -/
theorem compactCohomology_above_isZero_of_twoOpen (d : ℕ)
    (hU : ∀ a, d < a → IsZero (compactCohomology (restrictedProjection p U) V a))
    (hD : ∀ a, d < a → IsZero (compactCohomology (restrictedProjection p D) V a))
    (hI : ∀ a, d < a → IsZero (compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V a))
    (a : ℕ) (ha : d < a) : IsZero (compactCohomology p V a) :=
  compactCohomology_isZero_of_twoOpen p V U D hUD a (hU a ha) (hD a ha) (hI (a+1) (by omega))

/-- The actual compact-support sum is surjective whenever the next intersection group vanishes. -/
theorem compactSum_epi_of_isZero (a : ℕ)
    (hI : IsZero (compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V (a+1))) :
    Epi (compactSum p V U D a) := by
  rw [← compactAmbientSegment_f p V U D hUD a]
  exact (compactAmbientSegment_exact p V U D hUD a).epi_f (hI.eq_of_tgt _ _)

end TernaryPoly.SingularLocalCompactCapMV
