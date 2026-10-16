module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Cochains
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceFibers

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex
open EquivariantSingularSmall SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality
open FreeActionLinearization CoveringSingularOrbits SphereOddDegree

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
    (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Actual geometric restriction vanishes exactly when the cochain vanishes on every simplex
in the specified subset; this uses injectivity of the genuine fiber pullback. -/
theorem localRestriction_zero_iff (A : Set B) (a : ℕ)
    (φ : VertexCochain p hp.out V a) :
    (localRestriction p A V).f a φ = 0 ↔
      ∀ σ : SingularSimplex (TopCat.of A) a, φ (projection (sInclusion A) a σ) = 0 := by
  constructor
  · intro h σ
    apply (coefficientPullback_bijective (restrictedProjection p A) p
      (sInclusion (p ⁻¹' A)) (sInclusion A) (restricted_square p A)
      (restrictedQuotientCovering p A) hp.out (fun _ _ => rfl) V (atVertex σ)).injective
    exact (congrFun h σ).trans (map_zero _).symm
  · intro h
    funext σ
    change coefficientPullback (restrictedProjection p A) p (sInclusion (p ⁻¹' A))
      (sInclusion A) (restricted_square p A) (restrictedQuotientCovering p A) hp.out
      (fun _ _ => rfl) V (atVertex σ) (φ (projection (sInclusion A) a σ)) = 0
    erw [h σ,map_zero]

end TernaryPoly.SingularLocalSupport
