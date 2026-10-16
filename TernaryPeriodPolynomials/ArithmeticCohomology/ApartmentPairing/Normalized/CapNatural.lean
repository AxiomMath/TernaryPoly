module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.Assemble
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Manifold
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Apartment
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Defs

@[expose] public section


/-!
# Coefficient naturality of boundary Poincaré duality

Formalized by Claude Sonnet 5.5.

For a morphism `φ : V ⟶ W` of rational `Γ(6)`-coefficient systems, the ordinary cap on a compact manifold is natural
(`ordinaryCapMap_natural`): at the top support it is the support cap against the (coefficient-independent) compact fundamental
class (`topSupport_cap`), and the support cap is the relative cap, natural by the Descent framework
(`supportCapHomology_natural`, reusing `relativeCochainCap_natural`).  Hence the boundary cap isomorphism
(`boundaryH1CapIso_natural`), the identification of geometric and equivariant boundary cohomology
(`boundaryCohomologyIso_natural`) and boundary Poincaré duality `PD_∂` of Lemma 3.3 ("compatible with
induction of coefficients") are natural in the coefficients (`PDboundary_natural`).
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Normalized

open SphereOddDegree TernaryPoly TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalSupport
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalHomology
  TernaryPeriodPolynomials.Argument.CoefficientNaturality

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] {V W : Rep.{0} ℚ G} (φ : V ⟶ W)
  [IsCancelSMul G E]

/-- The coefficient map on support cochains. -/
def supportCochainMap (K : Set B) : supportCochains p V K ⟶ supportCochains p W K :=
  relativeLocalCochainMap (restrictedProjection p Kᶜ) p (sInclusion (p ⁻¹' Kᶜ)) (sInclusion Kᶜ)
    (restricted_square p Kᶜ) (restrictedQuotientCovering p Kᶜ) hp.out (fun _ _ => rfl) φ

theorem supportCapHomology_natural (K : Set B) (a b : ℕ)
    (x : (supportCochains p V K).homology a)
    (c : (RationalManifoldCompact.supportChains K).homology (a + b)) :
    homologyMap (localCoefficientMap p hp.out φ) b (supportCapHomology p V K a b x c) =
      supportCapHomology p W K a b (homologyMap (supportCochainMap p φ K) a x) c :=
  descentHomology_natural (supportCochainMap p φ K) (localCoefficientMap p hp.out φ)
    (supportCap p V K) (supportCap_leibniz p V K) (supportCap p W K) (supportCap_leibniz p W K)
    (fun a b x c => relativeCochainCap_natural (restrictedProjection p Kᶜ) p (sInclusion (p ⁻¹' Kᶜ))
      (sInclusion Kᶜ) (restricted_square p Kᶜ) (restrictedQuotientCovering p Kᶜ) hp.out
      (fun _ _ => rfl) φ a b x c) a b x c


omit [IsCancelSMul G E] in
theorem supportInclusion_natural (K : Set B) :
    supportCochainMap p φ K ≫ supportInclusion p W K = supportInclusion p V K ≫ localCochainMap p hp.out φ :=
  relativeLocalCochainMap_ι (restrictedProjection p Kᶜ) p (sInclusion (p ⁻¹' Kᶜ)) (sInclusion Kᶜ)
    (restricted_square p Kᶜ) (restrictedQuotientCovering p Kᶜ) hp.out (fun _ _ => rfl) φ

section Compact

open TopologicalSpace TernaryPoly.CompactOrdinaryCap TernaryPoly.RationalLocalOrientation

variable {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B]
  [ChartedSpace H B] [CompactSpace B] (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
  (o : Orientation (n+2) B)

omit [SecondCountableTopology B] in
/-- At the top support the ordinary cap is the support cap against the fundamental class. -/
theorem topSupport_cap (V : Rep.{0} ℚ G) (a b : ℕ) (hab : a+b = n+2) :
    (topSupportHomologyIso p V a).hom ≫ ordinaryCapMap p V n e o a b hab =
      compactCapAt p V n e o (⊤ : Compacts B) a b hab := by
  unfold ordinaryCapMap
  rw [compactOrdinaryIso_inv_top, Category.assoc, Iso.hom_inv_id_assoc]
  exact compactCapMap_classMap p V n e o (⊤ : Compacts B) a b hab

omit [SecondCountableTopology B] in
/-- **The ordinary cap on a compact manifold is natural in the coefficients.** -/
theorem ordinaryCapMap_natural (a b : ℕ) (hab : a+b = n+2) :
    ordinaryCapMap p V n e o a b hab ≫ homologyMap (localCoefficientMap p hp.out φ) b =
      homologyMap (localCochainMap p hp.out φ) a ≫ ordinaryCapMap p W n e o a b hab := by
  rw [← cancel_epi (topSupportHomologyIso p V a).hom]
  have hinc : (topSupportHomologyIso p V a).hom ≫ homologyMap (localCochainMap p hp.out φ) a =
      homologyMap (supportCochainMap p φ (⊤ : Compacts B)) a ≫ (topSupportHomologyIso p W a).hom := by
    rw [topSupportHomologyIso_hom, topSupportHomologyIso_hom, ← homologyMap_comp, ← homologyMap_comp]
    exact congrArg (fun f => homologyMap f a) (supportInclusion_natural p φ ((⊤ : Compacts B) : Set B)).symm
  rw [← Category.assoc, topSupport_cap, ← Category.assoc (topSupportHomologyIso p V a).hom,
    hinc, Category.assoc, topSupport_cap]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact supportCapHomology_natural p φ ((⊤ : Compacts B) : Set B) a b x
    (capFundamentalClass n e o (⊤ : Compacts B) a b hab)

end Compact


section Boundary

open TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.OrdinaryBoundaryActualEvaluation

variable {V W : Rep.{0} ℚ principalSix} (φ : V ⟶ W)

/-- **The boundary cap isomorphism is natural in the coefficients.** -/
theorem boundaryH1CapIso_natural :
    (SymmetricSpaceBoundaryManifold.boundaryH1CapIso V
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom ≫
      homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3 =
    homologyMap (localCochainMap boundaryProjection boundaryQuotientCovering φ) 1 ≫
      (SymmetricSpaceBoundaryManifold.boundaryH1CapIso W
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom :=
  ordinaryCapMap_natural boundaryProjection φ 2 SymmetricSpaceBoundaryManifold.boundaryEuclidean
    SymmetricSpaceBoundaryOrientation.boundaryOrientation 1 3 rfl

/-- The identification of geometric and equivariant boundary cohomology is natural in the coefficients. -/
theorem boundaryCohomologyIso_natural :
    (boundaryCohomologyIso V).hom ≫
      homologyMap (localCochainMap boundaryProjection boundaryQuotientCovering φ) 1 =
    homologyMap (coefHomPost SymmetricSpaceBoundaryIncidenceHomology.boundaryChains φ) 1 ≫
      (boundaryCohomologyIso W).hom := by
  have h := congrArg (fun f => homologyMap f 1)
    (cochainIso_natural boundaryProjection boundaryQuotientCovering φ)
  simp only [homologyMap_comp] at h
  exact h.symm

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary)

/-- **Boundary Poincaré duality is natural in the coefficients**: for `φ : V ⟶ W`,
`φ_* ≫ PD_∂^W = PD_∂^V ≫ φ^*` on boundary `H₃ → H¹`. -/
theorem PDboundary_natural :
    homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3 ≫ PDboundary W =
      PDboundary V ≫ homologyMap (coefHomPost SymmetricSpaceBoundaryIncidenceHomology.boundaryChains φ) 1 := by
  have hA := boundaryH1CapIso_natural φ
  have hC := boundaryCohomologyIso_natural φ
  have h1 : (SymmetricSpaceBoundaryManifold.boundaryH1CapIso V
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv ≫
      homologyMap (localCochainMap boundaryProjection boundaryQuotientCovering φ) 1 =
    homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering φ) 3 ≫
      (SymmetricSpaceBoundaryManifold.boundaryH1CapIso W
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hA, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 : (boundaryCohomologyIso V).inv ≫
      homologyMap (coefHomPost SymmetricSpaceBoundaryIncidenceHomology.boundaryChains φ) 1 =
    homologyMap (localCochainMap boundaryProjection boundaryQuotientCovering φ) 1 ≫
      (boundaryCohomologyIso W).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hC, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold PDboundary
  rw [← Category.assoc, ← h1, Category.assoc, Category.assoc, ← h2]

end Boundary

end TernaryPeriodPolynomials.Argument.Lemma33.Normalized
