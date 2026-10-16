module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationRelative
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapRelative

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapNormalization
open CategoryTheory Limits
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open EquivariantSingularSmall SphereOddDegree

/-- The identity quotient covering supplies the fact expected by actual support cochains. -/
instance identityCoverFact (X : TopCat.{0}) : Fact (IsQuotientCoveringMap (𝟙 X) Unit) :=
  ⟨identityCover X⟩

variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- Evaluation of an actual support cochain on an actual relative support chain. -/
def supportEvaluation (K : Set X) (a : ℕ) :
    (supportCochains (𝟙 X) (constantRep V) K).X a →ₗ[ℚ]
      (RationalManifoldCompact.supportChains K).X a →ₗ[ℚ] V :=
  relativeEvaluation (restrictedProjection (𝟙 X) Kᶜ) (sInclusion ((𝟙 X) ⁻¹' Kᶜ))
    (sInclusion Kᶜ) (restricted_square (𝟙 X) Kᶜ) (restrictedQuotientCovering (𝟙 X) Kᶜ)
    (fun _ _ => rfl) V a

/-- Support evaluation on an ambient-chain representative is literal cochain evaluation. -/
theorem supportEvaluation_projection (K : Set X) (a : ℕ)
    (φ : (supportCochains (𝟙 X) (constantRep V) K).X a) (c : (scalarChains X).X a) :
    supportEvaluation X V K a φ ((cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f a c) =
      SingularLocalConstant.evaluation X V a ((supportInclusion (𝟙 X) (constantRep V) K).f a φ) c :=
  relativeEvaluation_projection (restrictedProjection (𝟙 X) Kᶜ) (sInclusion ((𝟙 X) ⁻¹' Kᶜ))
    (sInclusion Kᶜ) (restricted_square (𝟙 X) Kᶜ) (restrictedQuotientCovering (𝟙 X) Kᶜ)
    (fun _ _ => rfl) V a φ c

/-- The actual support cap followed by H0 augmentation is evaluation of the actual
support cochain and scalar relative cycle representatives. -/
theorem supportCapHomology_evaluation (K : Set X) (a : ℕ)
    (φ : Homology.Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (a-1) a (a+1)))
    (c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (a+1) a (a-1))) :
    augmentation X V (supportCapHomology (𝟙 X) (constantRep V) K a 0
      (Descent.cochainClass _ a φ) (Descent.chainClass _ a c)) =
      supportEvaluation X V K a φ.val c.val :=
  relativeCapHomology_evaluation (restrictedProjection (𝟙 X) Kᶜ) (sInclusion ((𝟙 X) ⁻¹' Kᶜ))
    (sInclusion Kᶜ) (restricted_square (𝟙 X) Kᶜ) (restrictedQuotientCovering (𝟙 X) Kᶜ)
    (fun _ _ => rfl) V a φ c

/-- Any actual scalar representative of a relative support cycle gives the same literal
normalization of the cap on homology. -/
theorem supportCapHomology_ambient_evaluation (K : Set X) (a : ℕ)
    (φ : Homology.Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (a-1) a (a+1)))
    (c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (a+1) a (a-1)))
    (z : (scalarChains X).X a)
    (hz : (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f a z = c.val) :
    augmentation X V (supportCapHomology (𝟙 X) (constantRep V) K a 0
      (Descent.cochainClass _ a φ) (Descent.chainClass _ a c)) =
      SingularLocalConstant.evaluation X V a ((supportInclusion (𝟙 X) (constantRep V) K).f a φ.val) z := by
  rw [supportCapHomology_evaluation, ← hz]
  exact supportEvaluation_projection X V K a φ.val z

end TernaryPoly.SingularLocalCapNormalization
