module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityProperty
public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.Union

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap RationalLocalOrientation RationalManifoldCompact
open EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- The complete actual duality property propagates across a genuine binary open cover. -/
theorem duality_twoOpen [LocallyCompactSpace B] (U D : Opens B)
    [ChartedSpace H U] [ChartedSpace H D] [ChartedSpace H (U ⊓ D : Opens B)] (hUD : U ⊔ D = ⊤)
    (hU : Duality (restrictedProjection p U) V n e)
    (hD : Duality (restrictedProjection p D) V n e)
    (hI : Duality (restrictedProjection p (U ⊓ D : Opens B)) V n e) : Duality p V n e := by
  let : IsCancelSMul G E := hp.out.isCancelSMul
  constructor
  · intro o a b hab
    exact SingularLocalCompactCapMV.compactCap_isIso_of_twoOpen p V n e o U D hUD
      (hU.1 (openOrientation n e o U)) (hD.1 (openOrientation n e o D))
      (hI.1 (openOrientation n e o (U ⊓ D))) (hI.2 (n+3) (by omega)) a b hab
  · exact SingularLocalCompactCapMV.compactCohomology_above_isZero_of_twoOpen p V U D hUD
      (n+2) hU.2 hD.2 hI.2

/-- Actual compact cohomology vanishing propagates through increasing open unions. -/
theorem compactCohomology_isZero_increasing (U : ℕ → Opens B) (hU : Monotone U)
    (hcover : (⋃ i, (U i : Set B)) = Set.univ) (a : ℕ)
    (hz : ∀ i, IsZero (compactCohomology (restrictedProjection p (U i)) V a)) :
    IsZero (compactCohomology p V a) := by
  let F := SingularLocalOpenUnion.compactDiagram p V U hU a
  have hF : IsZero F := F.isZero_iff.mpr hz
  exact ((colimit.isColimit F).isZero_pt hF).of_iso
    (SingularLocalOpenUnion.compactColimitIso p V U hU hcover a).symm

/-- The complete actual duality property propagates through a genuine increasing open cover. -/
theorem duality_increasing (U : ℕ → Opens B) [∀ i, ChartedSpace H (U i)] (hU : Monotone U)
    (hcover : (⋃ i, (U i : Set B)) = Set.univ)
    (hd : ∀ i, Duality (restrictedProjection p (U i)) V n e) : Duality p V n e := by
  let : IsCancelSMul G E := hp.out.isCancelSMul
  constructor
  · intro o a b hab
    exact SingularLocalOpenUnion.increasing_union_compactCap_isIso p V n e o U hU hcover a b hab
      (fun i => (hd i).1 (openOrientation n e o (U i)) a b hab)
  · intro a ha
    exact compactCohomology_isZero_increasing p V U hU hcover a (fun i => (hd i).2 a ha)

end TernaryPoly.SingularLocalCompactDuality
