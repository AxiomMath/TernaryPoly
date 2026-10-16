module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVFixedCap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap SingularLocalCompactMV
open RationalManifoldCompact RationalLocalOrientation EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  {H : Type} [TopologicalSpace H] [T2Space B] [LocallyCompactSpace B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (U D : Opens B) [ChartedSpace H (U ⊓ D : Opens B)] (hUD : U ⊔ D = ⊤)

/-- The actual compact-support cap and genuine ordinary Mayer–Vietoris connecting map commute
with the genuine compact-support connecting map, with the exact sign forced by cap Leibniz. -/
theorem compactCap_connecting (a b : ℕ) (hab : a+(b+1) = n+2) :
    compactCapMap p V n e o a (b+1) hab ≫ ordinaryConnecting p V U D hUD b =
      (-1 : ℤ)^(a+1) • (compactConnecting p V U D hUD a ≫
        compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
          (openOrientation n e o (U ⊓ D)) (a+1) b (by omega)) := by
  apply compactCohomology_hom_ext
  intro S
  obtain ⟨K,L,hK,hL,_,_,hKU,hLD,hKL⟩ := compact_binary_refinement U D hUD S S.isCompact
  let K' : Compacts B := ⟨K,hK⟩
  let L' : Compacts B := ⟨L,hL⟩
  have hS : K' ⊔ L' = S := SetLike.coe_injective hKL
  rw [← hS,← Category.assoc,compactCapMap_classMap,Preadditive.comp_zsmul,
    ← Category.assoc,compactConnecting_ambient_pair p V U D hUD K' L' hKU hLD a,Category.assoc]
  exact fixedConnecting_cap p V n e o K' L' U D hKU hLD hUD a b hab

end TernaryPoly.SingularLocalCompactCapMV
