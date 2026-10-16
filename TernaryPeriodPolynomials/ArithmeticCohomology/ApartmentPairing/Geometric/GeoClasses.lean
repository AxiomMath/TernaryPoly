module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33Diagram
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Main

@[expose] public section


/-!
# Geometric normalization of the fundamental class, the cap products and the top evaluator

Formalized by Claude Sonnet 5.5.

The library's relative fundamental class (`SymmetricSpaceRelativeFundamentalClass`)
is characterized by the choice-normalized rational generators `interiorOrientation`.  Rescaling them by `d₅` gives the
GEOMETRIC orientation (`interiorOrientationGeo`: the positive-cell generator of `PosOrientation5`, transported by the
global Euclidean chart of the symmetric space) with the geometric relative fundamental class `fundamentalClassGeo` and boundary
orientation `boundaryOrientationGeo`.  Everything built from them differs from the library's by ONE global factor, never a
new choice: the boundary cap (`boundaryH1CapIsoGeo_hom`), boundary Poincaré duality (`PDboundaryGeo_apply`, factor `d₅⁻¹`), the
relative cap (`relativeFundamentalCapGeo_apply`), and the top evaluator (`groupApartmentEvaluationGeo_apply`, factor `d₅⁻¹`).
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.RationalLocalOrientation TernaryPoly.RationalRelativeSingular
open TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport (d5)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Geometric

/-- Rescaling an orientation by a non-zero rational (the change between two choices of rational local generators). -/
def Orientation.scale {k : ℕ} {X : Type} [TopologicalSpace X] (c : ℚ) (hc : c ≠ 0) (o : Orientation k X) :
    Orientation k X where
  generator x := c • o.generator x
  nonzero x := smul_ne_zero hc (o.nonzero x)
  locallyRepresented x := by
    obtain ⟨U, K, hx, hUK, c0, h0⟩ := o.locallyRepresented x
    refine ⟨U, K, hx, hUK, c • c0, fun y hy hK => ?_⟩
    rw [map_smul, h0 y hy hK]

theorem Orientation.scale_generator {k : ℕ} {X : Type} [TopologicalSpace X] (c : ℚ) (hc : c ≠ 0)
    (o : Orientation k X) (x : X) : (Orientation.scale c hc o).generator x = c • o.generator x := rfl

section Classes

open TernaryPoly.RationalManifoldCompact TernaryPoly.HalfSpaceBoundaryOrientation

variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H] [ChartedSpace H X]

/-- The compact fundamental class of a rescaled orientation is the rescaled class. -/
theorem compactFundamentalClass_scale (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n + 2)))
    (o : Orientation (n + 2) X) (c : ℚ) (hc : c ≠ 0) (K : Set X) (hK : IsCompact K) :
    compactFundamentalClass n e (Orientation.scale c hc o) K hK = c • compactFundamentalClass n e o K hK := by
  symm
  apply compactFundamentalClass_unique
  intro x hx
  rw [map_smul, compactFundamentalClass_at_point]
  rfl

/-- The ordinary fundamental class of a rescaled orientation is the rescaled class. -/
theorem ordinaryFundamentalClass_scale [CompactSpace X] (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n + 2)))
    (o : Orientation (n + 2) X) (c : ℚ) (hc : c ≠ 0) :
    ordinaryFundamentalClass n e (Orientation.scale c hc o) = c • ordinaryFundamentalClass n e o := by
  unfold ordinaryFundamentalClass
  rw [compactFundamentalClass_scale, map_smul]

end Classes

section BoundaryCap

open TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.SymmetricSpaceBoundaryOrientation
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.RelativeCapConnecting TernaryPoly.CompactOrdinaryCap

/-- **The geometric orientation of the boundary**: the library's boundary orientation (the connecting image of the
choice-normalized relative fundamental class) rescaled by `d₅`. -/
def boundaryOrientationGeo : Orientation 4 BoundaryBase :=
  Orientation.scale d5 Normalized.d5_ne_zero' boundaryOrientation

/-- **Scaling comparison for the boundary cap**: the boundary cap against the geometric orientation is `d₅` times the
library's. -/
theorem boundaryH1CapIsoGeo_hom (W : Rep.{0} ℚ principalSix)
    (x : (SingularLocalCoefficient.localCochains boundaryProjection boundaryQuotientCovering W).homology 1) :
    (boundaryH1CapIso W boundaryOrientationGeo).hom x = d5 • (boundaryH1CapIso W boundaryOrientation).hom x := by
  change ordinaryCapMap boundaryProjection W 2 boundaryEuclidean boundaryOrientationGeo 1 3 rfl x =
    d5 • ordinaryCapMap boundaryProjection W 2 boundaryEuclidean boundaryOrientation 1 3 rfl x
  rw [ordinaryCap_eq_absolute, ordinaryCap_eq_absolute]
  unfold boundaryOrientationGeo
  rw [ordinaryFundamentalClass_scale, map_smul, map_smul]

/-- **Boundary Poincaré duality for the geometric orientation.** -/
def PDboundaryGeo (W : Rep.{0} ℚ principalSix) :
    (SingularLocalHomology.boundaryLocalChains W).homology 3 ⟶
      (EquivariantSingularSmall.homCochains SymmetricSpaceBoundaryIncidenceHomology.boundaryChains W).homology 1 :=
  (boundaryH1CapIso W boundaryOrientationGeo).inv ≫
    (OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso W).inv

/-- **Scaling comparison for boundary Poincaré duality**: one global rational factor `d₅⁻¹`. -/
theorem PDboundaryGeo_apply (W : Rep.{0} ℚ principalSix)
    (c : (SingularLocalHomology.boundaryLocalChains W).homology 3) :
    PDboundaryGeo W c = d5⁻¹ • Statements.Lemma33Diagram.PDboundary W c := by
  have hinv : (boundaryH1CapIso W boundaryOrientationGeo).inv c =
      d5⁻¹ • (boundaryH1CapIso W boundaryOrientation).inv c := by
    apply (ConcreteCategory.bijective_of_isIso (boundaryH1CapIso W boundaryOrientationGeo).hom).injective
    rw [Iso.inv_hom_id_apply, boundaryH1CapIsoGeo_hom, map_smul, smul_smul, mul_inv_cancel₀
      Normalized.d5_ne_zero', one_smul, Iso.inv_hom_id_apply]
  change (OrdinaryBoundaryActualEvaluation.boundaryCohomologyIso W).inv
      ((boundaryH1CapIso W boundaryOrientationGeo).inv c) = _
  rw [hinv, map_smul]
  rfl

end BoundaryCap

section Relative

open TernaryPoly.SymmetricSpaceRelativeFundamental TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SingularLocalCap TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceRelativeCapConnecting TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SingularLocalHomology

/-- **The geometric orientation of the arithmetic interior**: the choice-normalized `interiorOrientation` rescaled by `d₅`, the
degree of the positive staircase product cell.  At every point of the support `Nset` of the reference cell (in the product chart
`psi`), and at the identity point of the symmetric space, its generator is the restriction of the class of the positive reference cell
(`stair_generator_at`, and `ChartCompare.stairClassSpace_at` for the pushed cell in the symmetric space; the product chart and
the library's chart `spaceHomeomorph` differ by a linear map of positive determinant, `OrientTransport.localGenerator_eq_psiGenerator`).
At other points the generator is the translate of the reference cell (`ChartCompare.stairClassTrans_at`); it is the generator of
`d₅` times the library's consistent orientation everywhere (`Orientation.scale`), which is the only definition used downstream. -/
def interiorOrientationGeo : Orientation 5 ↥(boundary principalSix)ᶜ :=
  Orientation.scale d5 Normalized.d5_ne_zero' interiorOrientation

/-- **The geometric relative fundamental class**: `d₅` times the choice-normalized one. -/
def fundamentalClassGeo : (RationalRelativeSingular.relativeChains (boundary principalSix)).homology 5 :=
  d5 • fundamentalClass

/-- It has the geometric generator at every interior point ... -/
theorem fundamentalClassGeo_at_point (x : BordifiedOrbit) (hx : x ∉ boundary principalSix) :
    homologyMap (RationalCompactBoundary.boundaryPointMap (boundary principalSix) x hx) 5 fundamentalClassGeo =
      homologyMap (RationalRelativeExcision.pointExcisionMap x (boundary principalSix)ᶜ hx) 5
        (interiorOrientationGeo.generator ⟨x, hx⟩) := by
  unfold fundamentalClassGeo
  rw [map_smul, fundamentalClass_at_point, interiorOrientationGeo, Orientation.scale_generator, map_smul]

/-- ... and is the unique relative class with this property. -/
theorem fundamentalClassGeo_unique (c : (RationalRelativeSingular.relativeChains (boundary principalSix)).homology 5)
    (hc : ∀ x (hx : x ∉ boundary principalSix),
      homologyMap (RationalCompactBoundary.boundaryPointMap (boundary principalSix) x hx) 5 c =
        homologyMap (RationalRelativeExcision.pointExcisionMap x (boundary principalSix)ᶜ hx) 5
          (interiorOrientationGeo.generator ⟨x, hx⟩)) : c = fundamentalClassGeo := by
  have h : d5⁻¹ • c = fundamentalClass := by
    apply fundamentalClass_unique
    intro x hx
    rw [map_smul, hc x hx, interiorOrientationGeo, Orientation.scale_generator, map_smul, smul_smul,
      inv_mul_cancel₀ Normalized.d5_ne_zero', one_smul]
  unfold fundamentalClassGeo
  rw [← h, smul_smul, mul_inv_cancel₀ Normalized.d5_ne_zero', one_smul]

/-- Cap against the geometric relative fundamental class. -/
def relativeFundamentalCapGeo (V : Rep.{0} ℚ principalSix) :
    (geometricRelativeCochains V).homology 2 ⟶ (bordifiedLocalChains V).homology 3 :=
  ModuleCat.ofHom ((relativeCochainCapHomology boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 2 3).flip fundamentalClassGeo)

/-- **Scaling comparison for the relative cap.** -/
theorem relativeFundamentalCapGeo_apply (V : Rep.{0} ℚ principalSix)
    (x : (geometricRelativeCochains V).homology 2) :
    relativeFundamentalCapGeo V x = d5 • relativeFundamentalCap V x := by
  exact map_smul ((relativeCochainCapHomology boundaryProjection wholeProjection
    boundaryInclusion boundaryBaseInclusion boundary_square boundaryQuotientCovering
    wholeQuotientCovering boundaryInclusion_equivariant V 2 3) x) d5 fundamentalClass

theorem relativeHomCapGeo_hom_eq (W : Rep.{0} ℚ principalSix) :
    homologyMap (relativeHomGeometricIso W).hom 2 ≫ relativeFundamentalCapGeo W =
      d5 • (relativeHomCapIso W).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change relativeFundamentalCapGeo W (homologyMap (relativeHomGeometricIso W).hom 2 x) =
    d5 • relativeFundamentalCap W (homologyMap (relativeHomGeometricIso W).hom 2 x)
  exact relativeFundamentalCapGeo_apply W _

/-- **The cap isomorphism against the geometric relative fundamental class.** -/
def relativeHomCapIsoGeo (W : Rep.{0} ℚ principalSix) :
    (EquivariantSingularSmall.homCochains upstairsRelativeChains W).homology 2 ≅
      (bordifiedLocalChains W).homology 3 where
  hom := homologyMap (relativeHomGeometricIso W).hom 2 ≫ relativeFundamentalCapGeo W
  inv := d5⁻¹ • (relativeHomCapIso W).inv
  hom_inv_id := by
    rw [relativeHomCapGeo_hom_eq, Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.hom_inv_id,
      mul_inv_cancel₀ Normalized.d5_ne_zero', one_smul]
  inv_hom_id := by
    rw [relativeHomCapGeo_hom_eq, Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.inv_hom_id,
      inv_mul_cancel₀ Normalized.d5_ne_zero', one_smul]

/-- **The `G`-level Borel--Serre duality for the geometric orientation**:
`H₃(Γ(6), W) ≅ Hom_{Γ(6)}(St, W)`, built with the cap isomorphism against the geometric fundamental class. -/
def groupOrdinaryIsoGeo (W : Rep.{0} ℚ principalSix) : groupHomology W 3 ≅ ordinaryFunctionals W :=
  bordifiedGroupLocalHomologyIso W 3 ≪≫ (relativeHomCapIsoGeo W).symm ≪≫ relativeOrdinaryCohomologyIso W

/-- The top evaluator (value on the identity apartment) for the geometric orientation. -/
def groupApartmentEvaluationGeo (W : Rep.{0} ℚ principalSix) : groupHomology W 3 ⟶ ModuleCat.of ℚ W :=
  (groupOrdinaryIsoGeo W).hom ≫ identityApartmentEvaluation W

/-- **Scaling comparison for the top evaluator**: one global rational factor `d₅⁻¹`. -/
theorem groupApartmentEvaluationGeo_apply (W : Rep.{0} ℚ principalSix) (x : groupHomology W 3) :
    groupApartmentEvaluationGeo W x = d5⁻¹ • groupApartmentEvaluation W x := by
  change identityApartmentEvaluation W ((groupOrdinaryIsoGeo W).hom x) =
    d5⁻¹ • identityApartmentEvaluation W ((groupOrdinaryIso W).hom x)
  rw [← map_smul]
  congr 1
  change (relativeOrdinaryCohomologyIso W).hom ((relativeHomCapIsoGeo W).inv
    ((bordifiedGroupLocalHomologyIso W 3).hom x)) =
    d5⁻¹ • (relativeOrdinaryCohomologyIso W).hom ((relativeHomCapIso W).inv ((bordifiedGroupLocalHomologyIso W 3).hom x))
  rw [← map_smul]
  rfl

end Relative

end TernaryPeriodPolynomials.Argument.Lemma33.Geometric
