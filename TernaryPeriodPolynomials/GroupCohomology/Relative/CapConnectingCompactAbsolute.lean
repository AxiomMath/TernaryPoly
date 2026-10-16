module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.CapConnectingGeometric
public import TernaryPeriodPolynomials.Analysis.Compact.OrdinaryCapDuality
public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationGlobal

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeCapConnecting
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCap SingularLocalCoefficient SingularLocalHomology SingularLocalSupport
open SingularLocalCompactCap SingularLocalCompactCap.Algebra RationalManifoldCompact
open CompactOrdinaryCap RationalLocalOrientation HalfSpaceBoundaryOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]

/-- Projecting an actual scalar class to relative support and forgetting cochain support
preserves the literal absolute cap pairing. -/
theorem supportCapHomology_projection (K : Set B) (a b : ℕ)
    (x : (supportCochains p V K).homology a) (c : (scalarChains B).homology (a+b)) :
    supportCapHomology p V K a b x
      (homologyMap (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)) (a+b) c) =
      absolute p hp.out V a b (homologyMap (supportInclusion p V K) a x) c := by
  obtain ⟨x,rfl⟩ := cochainClass_surjective (supportCochains p V K) a x
  obtain ⟨c,rfl⟩ := chainClass_surjective (scalarChains B) (a+b) c
  let q := cokernel.π (RationalRelativeSingular.inclusion Kᶜ)
  let y : Homology.Cycles ((localCochains p hp.out V).sc' (a-1) a (a+1)) :=
    ⟨(supportInclusion p V K).f a x.val,by
      change (localCochains p hp.out V).d a (a+1) _ = 0
      erw [complexMap_d]
      have hx : (supportCochains p V K).d a (a+1) x.val = 0 := x.property
      rw [hx,map_zero]⟩
  let d : Homology.Cycles ((supportChains K).sc' (a+b+1) (a+b) (a+b-1)) :=
    ⟨q.f (a+b) c.val,by
      change (supportChains K).d (a+b) (a+b-1) _ = 0
      erw [complexMap_d]
      have hc : (scalarChains B).d (a+b) (a+b-1) c.val = 0 := c.property
      rw [hc,map_zero]⟩
  rw [chainClass_natural q (a+b) c d rfl,
    cochainClass_natural (supportInclusion p V K) a x y rfl,
    supportCapHomology_representatives,absolute_representatives]
  congr 1
  apply Subtype.ext
  exact supportCap_projection p V K a b x.val c.val

variable {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B] [CompactSpace B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)

/-- Ordinary cap is the literal absolute cap against any ordinary scalar class whose actual
whole-support projection is the specified compact fundamental class. -/
theorem ordinaryCap_eq_absolute_of_projection (a b : ℕ) (hab : a+b = n+2)
    (c : (scalarChains B).homology (a+b))
    (hc : homologyMap absoluteSupportProjection (a+b) c =
      capFundamentalClass n e o (⊤ : Compacts B) a b hab)
    (x : (localCochains p hp.out V).homology a) :
    ordinaryCapMap p V n e o a b hab x = absolute p hp.out V a b x c := by
  rw [ordinaryCap_top]
  change supportCapHomology p V Set.univ a b ((topSupportHomologyIso p V a).inv x)
    (capFundamentalClass n e o (⊤ : Compacts B) a b hab) = _
  rw [← hc,supportCapHomology_projection]
  have hx : homologyMap (supportInclusion p V Set.univ) a
      ((topSupportHomologyIso p V a).inv x) = x :=
    (topSupportHomologyIso p V a).toLinearEquiv.apply_symm_apply x
  rw [hx]

/-- The ordinary fundamental class projects to the actual compact whole-support class. -/
theorem ordinaryFundamentalClass_projection :
    homologyMap (absoluteSupportProjection (X := B)) (n+2)
      (ordinaryFundamentalClass n e o) =
        compactFundamentalClass n e o Set.univ isCompact_univ :=
  (absoluteSupportHomologyIso (X := B) (n+2)).toLinearEquiv.apply_symm_apply _

/-- Ordinary cap uses precisely the ordinary scalar fundamental class, with only the canonical
transport to its equal total cap degree. -/
theorem ordinaryCap_eq_absolute (a b : ℕ) (hab : a+b = n+2)
    (x : (localCochains p hp.out V).homology a) :
    ordinaryCapMap p V n e o a b hab x =
      absolute p hp.out V a b x
        (homologyDegreeChange (scalarChains B) (n+2) (a+b) hab.symm
          (ordinaryFundamentalClass n e o)) := by
  apply ordinaryCap_eq_absolute_of_projection p V n e o a b hab
  change (homologyDegreeChange (scalarChains B) (n+2) (a+b) hab.symm ≫
    homologyMap absoluteSupportProjection (a+b)) (ordinaryFundamentalClass n e o) = _
  rw [homologyDegreeChange_natural]
  change homologyDegreeChange _ (n+2) (a+b) hab.symm
    (homologyMap absoluteSupportProjection (n+2) (ordinaryFundamentalClass n e o)) = _
  rw [ordinaryFundamentalClass_projection]
  rfl

end TernaryPoly.RelativeCapConnecting
