module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory HomologicalComplex EquivariantSingularSmall
open SymmetricSpaceBoundaryFaceAugmentation IntegralGL3Congruence

/-- Chosen projective resolutions resolve the literal full label permutation modules. -/
abbrev lineModel := CategoryTheory.projectiveResolution lineLabels
abbrev planeModel := CategoryTheory.projectiveResolution planeLabels
abbrev flagModel := CategoryTheory.projectiveResolution flagLabels

def lineComparison := comparison lineResolution lineModel
def planeComparison := comparison planeResolution planeModel
def flagComparison := comparison flagResolution flagModel

/-- The chosen algebraic line arrow lifts the actual flag-to-line incidence. -/
def lineArrow := ProjectiveResolution.lift lineIncidence flagModel lineModel
/-- The chosen algebraic plane arrow lifts the actual flag-to-plane incidence. -/
def planeArrow := ProjectiveResolution.lift planeIncidence flagModel planeModel

/-- Coherent comparison with the literal geometric flag-to-line inclusion. -/
def lineComparisonHomotopy : Homotopy (lineChainMap ≫ lineComparison.hom)
    (flagComparison.hom ≫ lineArrow) :=
  comparisonHomotopy flagResolution flagModel lineResolution lineModel lineIncidence lineResolutionMap

/-- Coherent comparison with the literal geometric flag-to-plane inclusion. -/
def planeComparisonHomotopy : Homotopy (planeChainMap ≫ planeComparison.hom)
    (flagComparison.hom ≫ planeArrow) :=
  comparisonHomotopy flagResolution flagModel planeResolution planeModel planeIncidence planeResolutionMap

def lineCochainComparison (W : Rep.{0} ℚ principalSix) := cochainComparison lineResolution lineModel W
def planeCochainComparison (W : Rep.{0} ℚ principalSix) := cochainComparison planeResolution planeModel W
def flagCochainComparison (W : Rep.{0} ℚ principalSix) := cochainComparison flagResolution flagModel W

instance lineCochainComparison_quasiIso (W : Rep.{0} ℚ principalSix) : QuasiIso (lineCochainComparison W) :=
  cochainComparison_quasiIso _ _ W
instance planeCochainComparison_quasiIso (W : Rep.{0} ℚ principalSix) : QuasiIso (planeCochainComparison W) :=
  cochainComparison_quasiIso _ _ W
instance flagCochainComparison_quasiIso (W : Rep.{0} ℚ principalSix) : QuasiIso (flagCochainComparison W) :=
  cochainComparison_quasiIso _ _ W

/-- The actual line restriction square commutes up to the specified cochain homotopy. -/
def lineCochainHomotopy (W : Rep.{0} ℚ principalSix) :
    Homotopy (lineCochainComparison W ≫ homPullback lineChainMap W)
      (homPullback lineArrow W ≫ flagCochainComparison W) :=
  cochainComparisonHomotopy flagResolution flagModel lineResolution lineModel lineIncidence lineResolutionMap W

/-- The actual plane restriction square commutes up to the specified cochain homotopy. -/
def planeCochainHomotopy (W : Rep.{0} ℚ principalSix) :
    Homotopy (planeCochainComparison W ≫ homPullback planeChainMap W)
      (homPullback planeArrow W ≫ flagCochainComparison W) :=
  cochainComparisonHomotopy flagResolution flagModel planeResolution planeModel planeIncidence planeResolutionMap W

/-- Comparison with each chosen resolution preserves the actual coefficient-label augmentation. -/
theorem comparison_augmentations :
    lineComparison.hom ≫ lineModel.π=lineAugmentationChain ∧
    planeComparison.hom ≫ planeModel.π=planeAugmentationChain ∧
    flagComparison.hom ≫ flagModel.π=flagAugmentationChain :=
  ⟨comparison_augmentation _ _,comparison_augmentation _ _,comparison_augmentation _ _⟩

end TernaryPoly.BoundaryFaceResolutionComparison
