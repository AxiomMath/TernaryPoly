module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Main
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.Assemble

@[expose] public section


/-!
# Naturality of the Lemma 3.3 diagram in the coefficient system

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Normalized

variable {V W : Rep.{0} ℚ principalSix}

/-- The inclusion of the boundary commutes with the coefficient map on geometric local chains. -/
theorem boundaryInclusionMap_natural (φ : V ⟶ W) :
    boundaryInclusionMap V ≫ localCoefficientMap bordifiedProjection bordifiedProjection_quotientCovering φ =
      localCoefficientMap boundaryProjection boundaryQuotientCovering φ ≫ boundaryInclusionMap W := by
  have h : coinvariantSpaceMap boundaryInclusion boundaryInclusion_equivariant V ≫
      coinvariantCoefficientMap (E := _) φ =
      coinvariantCoefficientMap (E := _) φ ≫
        coinvariantSpaceMap boundaryInclusion boundaryInclusion_equivariant W := by
    apply HomologicalComplex.hom_ext
    intro n
    exact ((Rep.coinvariantsTensor ℚ principalSix).map φ).naturality _
  unfold boundaryInclusionMap localSpaceMap localCoefficientMap
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h]


open TernaryPeriodPolynomials.Argument.CoefficientNaturality
  (bordifiedGroupLocalHomologyIso_natural coefHomPost homologyEvaluation_coefHomPost groupOrdinaryIso_natural)
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

/-- **The boundary-to-group map is natural in the coefficients.** -/
theorem boundaryToGroup_natural (φ : V ⟶ W) :
    homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3 ≫
        SymmetricSpaceBoundaryDuality.boundaryToGroup W 3 =
      SymmetricSpaceBoundaryDuality.boundaryToGroup V 3 ≫ groupHomology.map (MonoidHom.id _) φ 3 := by
  have key : (bordifiedGroupLocalHomologyIso V 3).inv ≫ groupHomology.map (MonoidHom.id _) φ 3 =
      homologyMap (localCoefficientMap bordifiedProjection bordifiedProjection_quotientCovering φ) 3 ≫
        (bordifiedGroupLocalHomologyIso W 3).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact bordifiedGroupLocalHomologyIso_natural φ 3
  unfold SymmetricSpaceBoundaryDuality.boundaryToGroup
  rw [← Category.assoc, ← homologyMap_comp, ← boundaryInclusionMap_natural, homologyMap_comp,
    Category.assoc, Category.assoc, key]

/-- The top evaluator is natural in the coefficients. -/
theorem groupApartmentEvaluation_natural (φ : V ⟶ W) (x : groupHomology V 3) :
    OrdinaryTopBoundaryComparison.groupApartmentEvaluation W
        ((groupHomology.map (MonoidHom.id principalSix) φ 3).hom x) =
      φ.hom (OrdinaryTopBoundaryComparison.groupApartmentEvaluation V x) := by
  have h := groupOrdinaryIso_natural φ x
  change OrdinaryTopBoundaryComparison.identityApartmentEvaluation W
      ((OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom
        ((groupHomology.map (MonoidHom.id principalSix) φ 3).hom x)) =
    φ.hom (OrdinaryTopBoundaryComparison.identityApartmentEvaluation V
      ((OrdinaryTopBoundaryComparison.groupOrdinaryIso V).hom x))
  rw [h]
  rfl

/-- **The bottom arrow is natural in the coefficients.** -/
theorem flatBoundaryPairing_natural (φ : V ⟶ W)
    (ω : (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains V).homology 1) :
    flatBoundaryPairing W
        (homologyMap (coefHomPost SymmetricSpaceBoundaryIncidenceHomology.boundaryChains φ) 1 ω) =
      φ.hom (flatBoundaryPairing V ω) := by
  rw [Statements.Lemma33Diagram.flatBoundaryPairing_apply, Statements.Lemma33Diagram.flatBoundaryPairing_apply,
    homologyEvaluation_coefHomPost]
  rfl

/-- **The composite `c ↦ ⟨PD_∂ c, ∂a⟩` of the diagram is natural in the coefficients**: for a morphism `φ : V ⟶ W` of
coefficient systems and a boundary class `c`, the pairing of `φ_* c` is `φ` of the pairing of `c`.  (Proved through the
commuting diagram and the naturality of `boundaryToGroup` and of the top evaluator.) -/
theorem pairing_natural (φ : V ⟶ W) (c : (boundaryLocalChains V).homology 3) :
    flatBoundaryPairing W
        (PDboundary W ((homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3).hom c)) =
      φ.hom (flatBoundaryPairing V (PDboundary V c)) := by
  rw [← Statements.Lemma33Diagram.diagram_apply, ← Statements.Lemma33Diagram.diagram_apply]
  have h := congrArg (fun f => f.hom c) (boundaryToGroup_natural φ)
  change SymmetricSpaceBoundaryDuality.boundaryToGroup W 3
      ((homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3).hom c) =
    (groupHomology.map (MonoidHom.id _) φ 3).hom (SymmetricSpaceBoundaryDuality.boundaryToGroup V 3 c) at h
  rw [h]
  exact groupApartmentEvaluation_natural φ _

end TernaryPeriodPolynomials.Argument.Lemma33.Normalized
