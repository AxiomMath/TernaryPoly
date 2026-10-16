module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVHomology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVNaturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCompactMV SingularLocalCompactCap
open EquivariantSingularSmall RationalManifoldCompact RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (U D : Opens B) [ChartedSpace H U] [ChartedSpace H D] [ChartedSpace H (U ⊓ D : Opens B)]
  [IsCancelSMul G E]

/-- The actual pair of compact caps with the canonical ambient-induced open orientations. -/
def pairCap (a b : ℕ) (hab : a+b = n+2) :=
  biprod.map
    (compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) a b hab)
    (compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) a b hab)

/-- The signed intersection-extension square commutes for actual compact caps and geometric inclusions. -/
theorem compactCap_diagonal (a b : ℕ) (hab : a+b = n+2) :
    compactDiagonal p V U D a ≫ pairCap p V n e o U D a b hab =
      compactCapMap (restrictedProjection p (U ⊓ D : Opens B)) V n e
        (openOrientation n e o (U ⊓ D : Opens B)) a b hab ≫ ordinaryDiagonal p V U D b := by
  unfold compactDiagonal pairCap ordinaryDiagonal
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.map_fst,biprod.lift_fst_assoc,biprod.lift_fst]
    exact compactCapMap_between p V n e o (U ⊓ D) U inf_le_left a b hab
  · simp only [Category.assoc,biprod.map_snd,biprod.lift_snd_assoc,biprod.lift_snd,
      Preadditive.neg_comp,Preadditive.comp_neg]
    exact congrArg Neg.neg (compactCapMap_between p V n e o (U ⊓ D) D inf_le_right a b hab)

omit [ChartedSpace H (U ⊓ D : Opens B)] in
/-- The sum-extension square commutes for actual compact caps and geometric inclusions. -/
theorem compactCap_sum (a b : ℕ) (hab : a+b = n+2) :
    compactSum p V U D a ≫ compactCapMap p V n e o a b hab =
      pairCap p V n e o U D a b hab ≫ ordinarySum p V U D b := by
  unfold compactSum pairCap ordinarySum
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc,biprod.inl_map_assoc,biprod.inl_desc]
    exact compactCapMap_open_canonical p V n e o U a b hab
  · simp only [biprod.inr_desc_assoc,biprod.inr_map_assoc,biprod.inr_desc]
    exact compactCapMap_open_canonical p V n e o D a b hab

end TernaryPoly.SingularLocalCompactCapMV
