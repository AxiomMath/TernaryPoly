module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVRows

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

/-- The genuine five-term cap ladder. Its last two vertical maps carry the derived Leibniz sign. -/
def capLadder (a b : ℕ) (hab : a+(b+1) = n+2) :
    compactRow p V U D hUD a ⟶ ordinaryRow p V U D hUD b :=
  homMk₄
    (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e (openOrientation n e o (U ⊓ D)) a (b+1) hab)
    (pairCap p V n e o U D a (b+1) hab)
    (compactCapMap p V n e o a (b+1) hab)
    ((-1 : ℤ)^(a+1) • compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
      (openOrientation n e o (U ⊓ D)) (a+1) b (by omega))
    ((-1 : ℤ)^(a+1) • pairCap p V n e o U D (a+1) b (by omega))
    (compactCap_diagonal p V n e o U D a (b+1) hab)
    (compactCap_sum p V n e o U D a (b+1) hab)
    (by
      change compactConnecting p V U D hUD a ≫ ((-1 : ℤ)^(a+1) •
        compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
          (openOrientation n e o (U ⊓ D)) (a+1) b (by omega)) =
        compactCapMap p V n e o a (b+1) hab ≫ ordinaryConnecting p V U D hUD b
      rw [Preadditive.comp_zsmul]
      exact (compactCap_connecting p V n e o U D hUD a b hab).symm)
    (by
      change compactDiagonal p V U D (a+1) ≫ ((-1 : ℤ)^(a+1) •
        pairCap p V n e o U D (a+1) b (by omega)) =
        ((-1 : ℤ)^(a+1) • compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
          (openOrientation n e o (U ⊓ D)) (a+1) b (by omega)) ≫ ordinaryDiagonal p V U D b
      rw [Preadditive.comp_zsmul,Preadditive.zsmul_comp,compactCap_diagonal])

include hUD in
/-- Actual cap duality in positive homological degree propagates over two opens from the four
neighboring genuine cap isomorphisms; the pair hypotheses split into the two actual open pieces. -/
theorem compactCap_isIso_of_twoOpen_succ (a b : ℕ) (hab : a+(b+1) = n+2)
    [IsIso (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
      (openOrientation n e o (U ⊓ D)) a (b+1) hab)]
    [IsIso (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) a (b+1) hab)]
    [IsIso (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) a (b+1) hab)]
    [IsIso (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
      (openOrientation n e o (U ⊓ D)) (a+1) b (by omega))]
    [IsIso (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) (a+1) b (by omega))]
    [IsIso (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) (a+1) b (by omega))] :
    IsIso (compactCapMap p V n e o a (b+1) hab) := by
  have hab' : a+1+b = n+2 := by omega
  have hp₀ : IsIso (pairCap p V n e o U D a (b+1) hab) := by
    exact inferInstanceAs (IsIso (biprod.mapIso
      (asIso (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) a (b+1) hab))
      (asIso (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) a (b+1) hab))).hom)
  have hp₁ : IsIso (pairCap p V n e o U D (a+1) b hab') := by
    exact inferInstanceAs (IsIso (biprod.mapIso
      (asIso (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) (a+1) b hab'))
      (asIso (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) (a+1) b hab'))).hom)
  have hi := signed_isIso (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
    (openOrientation n e o (U ⊓ D)) (a+1) b hab') (a+1)
  have hp := signed_isIso (pairCap p V n e o U D (a+1) b hab') (a+1)
  exact isIso_of_epi_of_isIso_of_isIso_of_mono (compactRow_exact p V U D hUD a)
    (ordinaryRow_exact p V U D hUD b) (capLadder p V n e o U D hUD a b hab)
    (by change Epi (compactCapMap _ _ _ _ _ _ _ _); infer_instance) hp₀ hi
    (by change Mono ((-1 : ℤ)^(a+1) • pairCap p V n e o U D (a+1) b _); infer_instance)

end TernaryPoly.SingularLocalCompactCapMV
