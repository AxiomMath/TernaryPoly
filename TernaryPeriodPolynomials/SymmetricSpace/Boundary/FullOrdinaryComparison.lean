module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullOrdinaryDifferentials
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullInvariantComponent

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex EquivariantSingularSmall OrdinaryParabolicGroups OrdinaryBoundaryCone
open PolynomialGLAction

/-- Pullback along the actual canonical-cone-to-entire-boundary chain map. -/
def boundaryToCanonical (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    homCochains fullBoundaryChains W ⟶ canonicalCochains W :=
  homPullback canonicalBoundaryEquiv.inv W

instance boundaryToCanonical_quasiIso (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    QuasiIso (boundaryToCanonical W) :=
  homPullback_quasiIso_of_homotopyEquiv canonicalBoundaryEquiv.symm W

/-- Full-level geometric boundary H1 is the literal ordinary cone H1 for the same coefficients. -/
def fullBoundaryOrdinaryH1Iso (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    (homCochains fullBoundaryChains W).homology 1 ≅ ModuleCat.of ℚ (H1 W P Q) :=
  isoOfQuasiIsoAt (boundaryToCanonical W) 1 ≪≫ canonicalOrdinaryH1Iso W

/-- The exact finite-invariant component of the entire principal-six boundary, with all 26 covectors. -/
def fullLevelOrdinaryEquiv (n : ℕ) (e : ℤ) :
    fullLevelComponent n e 1 ≃ₗ[ℚ] actualH1 n e :=
  (fullLevelComponentEquiv n e 1).symm.trans
    (fullBoundaryOrdinaryH1Iso (actualCoefficients n e)).toLinearEquiv

/-- Applying finite-cover restriction and then the comparison recovers the full-level class. -/
theorem fullLevelOrdinaryEquiv_restrict (n : ℕ) (e : ℤ)
    (x : (fullBoundaryCochains n e).homology 1) :
    fullLevelOrdinaryEquiv n e (fullLevelComponentEquiv n e 1 x) =
      (fullBoundaryOrdinaryH1Iso (actualCoefficients n e)).hom x := by
  change (fullBoundaryOrdinaryH1Iso (actualCoefficients n e)).toLinearEquiv
    ((fullLevelComponentEquiv n e 1).symm (fullLevelComponentEquiv n e 1 x)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Descent on the full-level summand is the actual normalized finite-cover transfer. -/
theorem fullLevelComponentEquiv_symm_transfer (n : ℕ) (e : ℤ)
    (x : fullLevelComponent n e 1) :
    (fullLevelComponentEquiv n e 1).symm x = homologyMap (boundaryTransfer n e) 1 x.val := by
  apply boundaryRestriction_injective n e 1
  have he := congrArg Subtype.val ((fullLevelComponentEquiv n e 1).apply_symm_apply x)
  have ht : homologyMap (boundaryRestriction n e) 1 (homologyMap (boundaryTransfer n e) 1 x.val) = x.val := by
    change (homologyMap (boundaryTransfer n e) 1 ≫ homologyMap (boundaryRestriction n e) 1) x.val = _
    rw [←homologyMap_comp]
    exact (mem_fullLevelComponent n e 1 x.val).mp x.property
  exact he.trans ht.symm

/-- The ordinary class of an invariant boundary class uses precisely that normalized transfer. -/
theorem fullLevelOrdinaryEquiv_transfer (n : ℕ) (e : ℤ) (x : fullLevelComponent n e 1) :
    fullLevelOrdinaryEquiv n e x =
    (fullBoundaryOrdinaryH1Iso (actualCoefficients n e)).hom (homologyMap (boundaryTransfer n e) 1 x.val) :=
  congrArg (fun y => (fullBoundaryOrdinaryH1Iso (actualCoefficients n e)).hom y)
    (fullLevelComponentEquiv_symm_transfer n e x)

/-- Every genuine full-level component class has the ordinary pairwise normal form. -/
theorem fullLevel_class_pairwise_representative (n : ℕ) (e : ℤ)
    (x : fullLevelComponent n e 1) :
    ∃ c : actualCycles n e, classOf (actualCoefficients n e) P Q c = fullLevelOrdinaryEquiv n e x ∧
      (∀ g : P, Pairwise (OrdinaryBoundaryCommonRoot.evaluation n (c.val.1 g) : Poly)) ∧
      (∀ g : Q, Pairwise (OrdinaryBoundaryCommonRoot.evaluation n (c.val.2.1 g) : Poly)) ∧
      Pairwise (OrdinaryBoundaryCommonRoot.evaluation n c.val.2.2 : Poly) :=
  actual_class_pairwise_representative n e (fullLevelOrdinaryEquiv n e x)

/-- The same normal form for every actual full-level geometric boundary class. -/
theorem fullBoundary_class_pairwise_representative (n : ℕ) (e : ℤ)
    (x : (fullBoundaryCochains n e).homology 1) :
    ∃ c : actualCycles n e, classOf (actualCoefficients n e) P Q c =
      (fullBoundaryOrdinaryH1Iso (actualCoefficients n e)).hom x ∧
      (∀ g : P, Pairwise (OrdinaryBoundaryCommonRoot.evaluation n (c.val.1 g) : Poly)) ∧
      (∀ g : Q, Pairwise (OrdinaryBoundaryCommonRoot.evaluation n (c.val.2.1 g) : Poly)) ∧
      Pairwise (OrdinaryBoundaryCommonRoot.evaluation n c.val.2.2 : Poly) :=
  actual_class_pairwise_representative n e ((fullBoundaryOrdinaryH1Iso (actualCoefficients n e)).hom x)

end TernaryPoly.SymmetricSpaceBoundaryFull
