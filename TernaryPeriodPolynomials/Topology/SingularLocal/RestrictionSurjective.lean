module

public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionSurjective
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Cochains
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex SingularLocalCoefficient SingularCoverNaturality
open EquivariantSingularSmall EquivariantSingularMayerVietoris SphereOddDegree

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']

/-- An actual local-cochain pullback along an injective map upstairs is surjective in every degree.
The graded extension used in its proof is not asserted to be a cochain map. -/
theorem localPullback_surjective (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
    (hsquare : F ≫ p' = p ≫ f) (hp : IsQuotientCoveringMap p G)
    (hp' : IsQuotientCoveringMap p' G) (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hinj : Function.Injective F) (V : Rep.{0} ℚ G) (k : ℕ) :
    Function.Surjective ((localPullback p p' F f hsquare hp hp' hF V).f k) := by
  intro c
  obtain ⟨c,rfl⟩ := (homVertexEquiv p hp V k).surjective c
  obtain ⟨d,hd⟩ := SingularBoundaryRestriction.cochainPullback_surjective F hF hinj V k c
  refine ⟨homVertexEquiv p' hp' V k d,?_⟩
  exact (homVertexEquiv_pullback p p' F f hsquare hp hp' hF V k d).symm.trans
    (congrArg (homVertexEquiv p hp V k) hd)

variable (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Actual restriction to any base subset is degreewise surjective. -/
theorem localRestriction_surjective (A : Set B) (k : ℕ) :
    Function.Surjective ((localRestriction p A V).f k) :=
  localPullback_surjective (restrictedProjection p A) p (sInclusion (p ⁻¹' A)) (sInclusion A)
    (restricted_square p A) (restrictedQuotientCovering p A) hp.out (fun _ _ => rfl)
    Subtype.val_injective V k

/-- The actual restriction morphism is epi in the category of cochain complexes. -/
instance localRestriction_epi (A : Set B) : Epi (localRestriction p A V) :=
  epi_of_epi_f _ (fun k => (ModuleCat.epi_iff_surjective _).mpr (localRestriction_surjective p V A k))

end TernaryPoly.SingularLocalSupport
