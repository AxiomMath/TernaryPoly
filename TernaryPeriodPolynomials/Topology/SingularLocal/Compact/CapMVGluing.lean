module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVZero

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap
open EquivariantSingularSmall RationalManifoldCompact RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  {H : Type} [TopologicalSpace H] [T2Space B] [LocallyCompactSpace B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (U D : Opens B) [ChartedSpace H U] [ChartedSpace H D] [ChartedSpace H (U ⊓ D : Opens B)]
  (hUD : U ⊔ D = ⊤)

include hUD in
/-- All complementary-degree actual compact cap isomorphisms propagate over two opens, including
homological degree zero. The necessary next intersection vanishing is an explicit hypothesis. -/
theorem compactCap_isIso_of_twoOpen
    (hU : ∀ a b (hab : a+b = n+2), IsIso
      (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) a b hab))
    (hD : ∀ a b (hab : a+b = n+2), IsIso
      (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) a b hab))
    (hI : ∀ a b (hab : a+b = n+2), IsIso
      (compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
        (openOrientation n e o (U ⊓ D)) a b hab))
    (hIz : IsZero (compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V (n+3)))
    (a b : ℕ) (hab : a+b = n+2) : IsIso (compactCapMap p V n e o a b hab) := by
  cases b with
  | zero =>
      have ha : a = n+2 := by omega
      subst a
      have := hU (n+2) 0 hab
      have := hD (n+2) 0 hab
      have := hI (n+2) 0 hab
      exact compactCap_isIso_of_twoOpen_zero p V n e o U D hUD hIz
  | succ b =>
      have hab' : a+1+b = n+2 := by omega
      have := hU a (b+1) hab
      have := hD a (b+1) hab
      have := hI a (b+1) hab
      have := hU (a+1) b hab'
      have := hD (a+1) b hab'
      have := hI (a+1) b hab'
      exact compactCap_isIso_of_twoOpen_succ p V n e o U D hUD a b hab

end TernaryPoly.SingularLocalCompactCapMV
