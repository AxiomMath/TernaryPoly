module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.CochainHomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.CofiberMap

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex BoundaryFaceResolutionComparison

variable {G : Type} [Group G] {A B : ChainComplex (Rep.{0} ℚ G) ℕ}
  (f : A ⟶ B) (W : Rep.{0} ℚ G) (a : A.X 0 ⟶ W) (ha : A.d 1 0 ≫ a = 0)

/-- The literal shifted corner coordinate followed by its actual augmentation. -/
def coneCornerCochain : (homotopyCofiber f).X 1 ⟶ W := CofiberSequence.first f 0 ≫ a

include ha in
/-- The corner augmentation is a genuine degree-one cocycle; the suspension differential is negative. -/
theorem coneCornerCochain_boundary :
    (homotopyCofiber f).d 2 1 ≫ coneCornerCochain f W a = 0 := by
  unfold coneCornerCochain CofiberSequence.first
  erw [← Category.assoc, homotopyCofiber.d_fstX f 2 1 0 (Cone.downRel 1) (Cone.downRel 0),
    Preadditive.neg_comp, Category.assoc, ha, comp_zero, neg_zero]

/-- The actual homology map detecting the cone's shifted augmented corner. -/
def coneCornerHomology : (homotopyCofiber f).homology 1 ⟶ W :=
  evaluationOfCochain (homotopyCofiber f) W 1 (coneCornerCochain f W a)
    (coneCornerCochain_boundary f W a ha)

/-- The corner homology map is literally the augmented first coordinate on every represented cycle. -/
theorem coneCornerHomology_projection :
    (homotopyCofiber f).homologyπ 1 ≫ coneCornerHomology f W a ha =
      (homotopyCofiber f).iCycles 1 ≫ CofiberSequence.first f 0 ≫ a :=
  evaluationOfCochain_projection _ _ _ _ _

variable {A' B' : ChainComplex (Rep.{0} ℚ G) ℕ} (g : A' ⟶ B')
  (u : A ⟶ A') (v : B ⟶ B') (h : Homotopy (f ≫ v) (u ≫ g))
  (a' : A'.X 0 ⟶ W) (ha' : A'.d 1 0 ≫ a' = 0) (hu : u.f 0 ≫ a' = a)

include hu in
/-- Homotopy-square cofiber comparison retains the corner augmentation exactly. -/
theorem coneComparison_corner :
    (CofiberSequence.comparisonMap f g u v h).f 1 ≫ coneCornerCochain g W a' =
      coneCornerCochain f W a := by
  have hp := HomologicalComplex.congr_hom (CofiberSequence.comparisonMap_projection f g u v h) 1
  change (CofiberSequence.comparisonMap f g u v h).f 1 ≫ CofiberSequence.first g 0 =
    CofiberSequence.first f 0 ≫ u.f 0 at hp
  unfold coneCornerCochain
  erw [← Category.assoc, hp, Category.assoc, hu]

include hu in
/-- The actual augmented corner homology map commutes with the actual cofiber comparison. -/
theorem coneComparison_cornerHomology :
    homologyMap (CofiberSequence.comparisonMap f g u v h) 1 ≫ coneCornerHomology g W a' ha' =
      coneCornerHomology f W a ha :=
  evaluationOfCochain_natural (homotopyCofiber f) W 1
    (CofiberSequence.comparisonMap f g u v h) (coneCornerCochain f W a) (coneCornerCochain g W a')
    (coneCornerCochain_boundary f W a ha) (coneCornerCochain_boundary g W a' ha')
    (coneComparison_corner f W a g u v h a' hu)

end TernaryPoly.OrdinaryBoundaryActualEvaluation
