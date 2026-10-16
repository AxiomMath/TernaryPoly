module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVLadder
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVVanishing

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace ComposableArrows Abelian
open SingularLocalSupport SingularLocalCompactMV SingularLocalCompactCap
open EquivariantSingularSmall RationalManifoldCompact RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  {H : Type} [TopologicalSpace H] [T2Space B] [LocallyCompactSpace B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (U D : Opens B) [ChartedSpace H U] [ChartedSpace H D] [ChartedSpace H (U ⊓ D : Opens B)]
  (hUD : U ⊔ D = ⊤)

include hUD in
/-- Degree-zero actual cap duality glues through the genuine quotient diagrams, with the necessary
next-degree compact intersection vanishing hypothesis made explicit. -/
theorem compactCap_isIso_of_twoOpen_zero
    (hI : IsZero (compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V (n+3)))
    [IsIso (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
      (openOrientation n e o (U ⊓ D)) (n+2) 0 (by omega))]
    [IsIso (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) (n+2) 0 (by omega))]
    [IsIso (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) (n+2) 0 (by omega))] :
    IsIso (compactCapMap p V n e o (n+2) 0 (by omega)) := by
  have hab : n+2+0 = n+2 := by omega
  let R := mk₂ (compactDiagonal p V U D (n+2)) (compactSum p V U D (n+2))
  let S := mk₂ (ordinaryDiagonal p V U D 0) (ordinarySum p V U D 0)
  let φ : R ⟶ S := homMk₂
    (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
      (openOrientation n e o (U ⊓ D)) (n+2) 0 hab)
    (pairCap p V n e o U D (n+2) 0 hab)
    (compactCapMap p V n e o (n+2) 0 hab)
    (compactCap_diagonal p V n e o U D (n+2) 0 hab)
    (compactCap_sum p V n e o U D (n+2) 0 hab)
  have hR := (compactMiddleSegment_exact p V U D hUD (n+2)).exact_toComposableArrows
  change (mk₂ (compactMiddleSegment p V U D hUD (n+2)).f (compactMiddleSegment p V U D hUD (n+2)).g).Exact at hR
  rw [compactMiddleSegment_f,compactMiddleSegment_g] at hR
  have hS := (ordinaryMiddleSegment_exact p V U D hUD 0).exact_toComposableArrows
  change (mk₂ (ordinaryMiddleSegment p V U D hUD 0).f (ordinaryMiddleSegment p V U D hUD 0).g).Exact at hS
  rw [ordinaryMiddleSegment_f,ordinaryMiddleSegment_g] at hS
  have hp₀ : IsIso (pairCap p V n e o U D (n+2) 0 hab) := by
    exact inferInstanceAs (IsIso (biprod.mapIso
      (asIso (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) (n+2) 0 hab))
      (asIso (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) (n+2) 0 hab))).hom)
  exact isIso_of_epi_of_isIso φ hR hS
    (compactSum_epi_of_isZero p V U D hUD (n+2) hI) (ordinarySum_zero_epi p V U D hUD)
    (by change Epi (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
          (openOrientation n e o (U ⊓ D)) (n+2) 0 hab); infer_instance) hp₀

end TernaryPoly.SingularLocalCompactCapMV
