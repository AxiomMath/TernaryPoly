module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceAugmentationComplete
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G] {X Y : Rep.{0} ℚ G}
  (P R : ProjectiveResolution X) (Q S : ProjectiveResolution Y)

/-- Actual augmentation-preserving equivalence between two projective resolutions. -/
def comparison : _root_.HomotopyEquiv P.complex R.complex := ProjectiveResolution.homotopyEquiv P R

theorem comparison_augmentation : (comparison P R).hom ≫ R.π=P.π :=
  ProjectiveResolution.homotopyEquiv_hom_π P R

/-- The two comparisons form a coherent square with every specified resolution morphism. -/
def comparisonHomotopy (f : X ⟶ Y) (φ : ProjectiveResolution.Hom P Q f) :
    Homotopy (φ.hom ≫ (comparison Q S).hom)
      ((comparison P R).hom ≫ ProjectiveResolution.lift f R S) := by
  apply ProjectiveResolution.liftHomotopy f (P := P) (Q := S)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => φ.hom ≫ m) (comparison_augmentation Q S)).trans φ.hom_comp_π)
  · rw [Category.assoc,ProjectiveResolution.lift_commutes,←Category.assoc,comparison_augmentation]

/-- The resolution comparison acts on arbitrary rational coefficients by actual precomposition. -/
def cochainComparison (W : Rep.{0} ℚ G) : homCochains R.complex W ⟶ homCochains P.complex W :=
  homPullback (comparison P R).hom W

instance cochainComparison_quasiIso (W : Rep.{0} ℚ G) : QuasiIso (cochainComparison P R W) :=
  homPullback_quasiIso_of_homotopyEquiv (comparison P R) W

/-- The comparison of incidence cochains retains a genuine cochain homotopy. -/
def cochainComparisonHomotopy (f : X ⟶ Y) (φ : ProjectiveResolution.Hom P Q f) (W : Rep.{0} ℚ G) :
    Homotopy (cochainComparison Q S W ≫ homPullback φ.hom W)
      (homPullback (ProjectiveResolution.lift f R S) W ≫ cochainComparison P R W) :=
  (((linearYoneda ℚ (Rep ℚ G)).obj W).rightOp.mapHomotopy
    (comparisonHomotopy P R Q S f φ)).unop

/-- In every degree the cohomology comparison preserves the actual incidence arrow. -/
theorem cochainComparison_natural (f : X ⟶ Y) (φ : ProjectiveResolution.Hom P Q f)
    (W : Rep.{0} ℚ G) (n : ℕ) :
    homologyMap (cochainComparison Q S W) n ≫ homologyMap (homPullback φ.hom W) n=
      homologyMap (homPullback (ProjectiveResolution.lift f R S) W) n ≫
        homologyMap (cochainComparison P R W) n := by
  rw [←homologyMap_comp,←homologyMap_comp]
  exact (cochainComparisonHomotopy P R Q S f φ W).homologyMap_eq n

end TernaryPoly.BoundaryFaceResolutionComparison
