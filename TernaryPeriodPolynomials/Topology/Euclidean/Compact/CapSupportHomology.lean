module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapSupportComplex
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationDescent
public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsConsequences

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCap SingularLocalCapNormalization SingularLocalSupport
open SingularLocalCoefficient SingularLocalCap.Homology SingularLocalCompactCap.Algebra
open RationalHomologyCoefficients
variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The actual cohomology of an arbitrary fixed support is the full V-valued linear Hom
of its actual relative rational homology, by independent evaluation. -/
def supportHomologyEvaluationEquiv (K : Set X) (a : ℕ) :
    (supportCochains (𝟙 X) (constantRep V) K).homology a ≃ₗ[ℚ]
      ((RationalManifoldCompact.supportChains K).homology a →ₗ[ℚ] V) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) a).mapIso
    (supportHomCochainIso X V K)).toLinearEquiv ≪≫ₗ
      homologyEvaluationEquiv (RationalManifoldCompact.supportChains K) V a

/-- The fixed-support universal-coefficient isomorphism retains the literal independent
scalar/vector evaluation on the actual cycle representatives. -/
theorem supportHomologyEvaluationEquiv_classes (K : Set X) (a : ℕ)
    (φ : Cycles ((supportCochains (𝟙 X) (constantRep V) K).sc' (a-1) a (a+1)))
    (c : Cycles ((RationalManifoldCompact.supportChains K).sc' (a+1) a (a-1))) :
    supportHomologyEvaluationEquiv X V K a (Descent.cochainClass _ a φ)
      (Descent.chainClass _ a c) = supportEvaluation X V K a φ.val c.val := by
  change homologyEvaluationEquiv _ V a
    (homologyMap (supportHomCochainIso X V K).hom a (Descent.cochainClass _ a φ))
      (Descent.chainClass _ a c) = _
  rw [cochainClass_natural (supportHomCochainIso X V K).hom a φ
    (mapComplexCycle (supportHomCochainIso X V K).hom (a-1) a (a+1) φ) rfl]
  erw [homologyEvaluationEquiv_classes]
  rfl

/-- The isomorphism is exactly the independent support evaluation used to
normalize the actual cap operation. -/
theorem supportHomologyEvaluationEquiv_eq (K : Set X) (a : ℕ)
    (h : (supportCochains (𝟙 X) (constantRep V) K).homology a)
    (c : (RationalManifoldCompact.supportChains K).homology a) :
    supportHomologyEvaluationEquiv X V K a h c = supportHomologyEvaluation X V K a h c := by
  obtain ⟨φ,rfl⟩ := cochainClass_surjective _ a h
  obtain ⟨z,rfl⟩ := chainClass_surjective _ a c
  rw [supportHomologyEvaluationEquiv_classes, supportHomologyEvaluation_representatives]

/-- Vanishing of the actual relative rational homology forces vanishing of actual
fixed-support cohomology for every rational coefficient module. -/
theorem supportCohomology_isZero (K : Set X) (a : ℕ)
    (h : IsZero ((RationalManifoldCompact.supportChains K).homology a)) :
    IsZero ((supportCochains (𝟙 X) (constantRep V) K).homology a) := by
  let := ModuleCat.subsingleton_of_isZero h
  let : Subsingleton ((supportCochains (𝟙 X) (constantRep V) K).homology a) :=
    (supportHomologyEvaluationEquiv X V K a).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end TernaryPoly.EuclideanCompactCap
