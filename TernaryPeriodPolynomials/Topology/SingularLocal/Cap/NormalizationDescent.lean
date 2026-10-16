module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationSupport

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCapNormalization
open CategoryTheory
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open SingularLocalCompactCap.Algebra
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ) (K : Set X) (a : ℕ)

/-- Literal relative evaluation has a unique bilinear descent to the actual cohomology
and homology objects, characterized on their genuine cycle representatives. -/
theorem existsUnique_supportHomologyEvaluation :
    ∃! e : (supportCochains (𝟙 X) (constantRep V) K).homology a →ₗ[ℚ]
      (RationalManifoldCompact.supportChains K).homology a →ₗ[ℚ] V,
      ∀ (φ : Homology.Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (a-1) a (a+1)))
        (c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (a+1) a (a-1))),
        e (Descent.cochainClass _ a φ) (Descent.chainClass _ a c) =
          supportEvaluation X V K a φ.val c.val := by
  refine ⟨(supportCapHomology (𝟙 X) (constantRep V) K a 0).compr₂ (augmentation X V).hom, ?_, ?_⟩
  · intro φ c
    exact supportCapHomology_evaluation X V K a φ c
  · intro e he
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    obtain ⟨φ,rfl⟩ := cochainClass_surjective _ a x
    obtain ⟨c,rfl⟩ := chainClass_surjective _ a z
    exact (he φ c).trans (supportCapHomology_evaluation X V K a φ c).symm

/-- The canonical bilinear evaluation on actual support cohomology and support homology,
defined by its literal cycle-evaluation universal property. -/
def supportHomologyEvaluation :
    (supportCochains (𝟙 X) (constantRep V) K).homology a →ₗ[ℚ]
      (RationalManifoldCompact.supportChains K).homology a →ₗ[ℚ] V :=
  (existsUnique_supportHomologyEvaluation X V K a).choose

/-- The canonical homological evaluation retains literal relative cochain evaluation. -/
theorem supportHomologyEvaluation_representatives
    (φ : Homology.Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (a-1) a (a+1)))
    (c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (a+1) a (a-1))) :
    supportHomologyEvaluation X V K a (Descent.cochainClass _ a φ) (Descent.chainClass _ a c) =
      supportEvaluation X V K a φ.val c.val :=
  (existsUnique_supportHomologyEvaluation X V K a).choose_spec.1 φ c

/-- The existing cap on actual homology, composed with actual augmentation, is precisely
the uniquely descended literal evaluation pairing. -/
theorem supportCapHomology_evaluation_classes
    (x : (supportCochains (𝟙 X) (constantRep V) K).homology a)
    (z : (RationalManifoldCompact.supportChains K).homology a) :
    augmentation X V (supportCapHomology (𝟙 X) (constantRep V) K a 0 x z) =
      supportHomologyEvaluation X V K a x z := by
  obtain ⟨φ,rfl⟩ := cochainClass_surjective _ a x
  obtain ⟨c,rfl⟩ := chainClass_surjective _ a z
  exact (supportCapHomology_evaluation X V K a φ c).trans
    (supportHomologyEvaluation_representatives X V K a φ c).symm

end TernaryPoly.SingularLocalCapNormalization
