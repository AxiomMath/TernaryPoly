module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Stabilizers
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeEvaluation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory Category Limits HomologicalComplex EquivariantSingularSmall
open IntegralGL3Congruence OrdinaryIncidence SymmetricSpaceBoundaryFaceAugmentation
open BoundaryFaceResolutionComparison SymmetricSpaceBoundaryMV

/-- The genuine induced-bar resolutions range over every actual principal-six label orbit. -/
abbrev lineStabilizerModel := stabilizerResolution principalSix Line
abbrev planeStabilizerModel := stabilizerResolution principalSix Plane
abbrev flagStabilizerModel := stabilizerResolution principalSix Flag

def lineStabilizerComparison := comparison lineResolution lineStabilizerModel
def planeStabilizerComparison := comparison planeResolution planeStabilizerModel
def flagStabilizerComparison := comparison flagResolution flagStabilizerModel

/-- These chain arrows lift the literal flag-to-face label incidence maps. -/
def lineStabilizerArrow := ProjectiveResolution.lift lineIncidence flagStabilizerModel lineStabilizerModel
def planeStabilizerArrow := ProjectiveResolution.lift planeIncidence flagStabilizerModel planeStabilizerModel

abbrev lineStabilizerCochains (W : Rep.{0} ℚ principalSix) := stabilizerCochains principalSix Line W
abbrev planeStabilizerCochains (W : Rep.{0} ℚ principalSix) := stabilizerCochains principalSix Plane W
abbrev flagStabilizerCochains (W : Rep.{0} ℚ principalSix) := stabilizerCochains principalSix Flag W

/-- Actual full-family cochain comparisons, including explicit Shapiro coordinate changes. -/
def lineStabilizerCochainComparison (W : Rep.{0} ℚ principalSix) :
    lineStabilizerCochains W ⟶ homCochains lineChains W :=
  (fullShapiroIso principalSix Line W).inv ≫ cochainComparison lineResolution lineStabilizerModel W

def planeStabilizerCochainComparison (W : Rep.{0} ℚ principalSix) :
    planeStabilizerCochains W ⟶ homCochains planeChains W :=
  (fullShapiroIso principalSix Plane W).inv ≫ cochainComparison planeResolution planeStabilizerModel W

def flagStabilizerCochainComparison (W : Rep.{0} ℚ principalSix) :
    flagStabilizerCochains W ⟶ homCochains flagChains W :=
  (fullShapiroIso principalSix Flag W).inv ≫ cochainComparison flagResolution flagStabilizerModel W

instance lineStabilizerCochainComparison_quasiIso (W : Rep.{0} ℚ principalSix) :
    QuasiIso (lineStabilizerCochainComparison W) := by
  have := cochainComparison_quasiIso lineResolution lineStabilizerModel W
  exact _root_.quasiIso_comp (fullShapiroIso principalSix Line W).inv
    (cochainComparison lineResolution lineStabilizerModel W)
instance planeStabilizerCochainComparison_quasiIso (W : Rep.{0} ℚ principalSix) :
    QuasiIso (planeStabilizerCochainComparison W) := by
  have := cochainComparison_quasiIso planeResolution planeStabilizerModel W
  exact _root_.quasiIso_comp (fullShapiroIso principalSix Plane W).inv
    (cochainComparison planeResolution planeStabilizerModel W)
instance flagStabilizerCochainComparison_quasiIso (W : Rep.{0} ℚ principalSix) :
    QuasiIso (flagStabilizerCochainComparison W) := by
  have := cochainComparison_quasiIso flagResolution flagStabilizerModel W
  exact _root_.quasiIso_comp (fullShapiroIso principalSix Flag W).inv
    (cochainComparison flagResolution flagStabilizerModel W)

/-- Genuine line-to-flag cochain restriction, transported through the full-family Shapiro isomorphisms. -/
def lineStabilizerRestriction (W : Rep.{0} ℚ principalSix) :
    lineStabilizerCochains W ⟶ flagStabilizerCochains W :=
  (fullShapiroIso principalSix Line W).inv ≫ homPullback lineStabilizerArrow W ≫
    (fullShapiroIso principalSix Flag W).hom

/-- Genuine plane-to-flag cochain restriction, transported through the full-family Shapiro isomorphisms. -/
def planeStabilizerRestriction (W : Rep.{0} ℚ principalSix) :
    planeStabilizerCochains W ⟶ flagStabilizerCochains W :=
  (fullShapiroIso principalSix Plane W).inv ≫ homPullback planeStabilizerArrow W ≫
    (fullShapiroIso principalSix Flag W).hom

/-- Iso-conjugation retains the specified comparison homotopy. -/
def shapiroComparisonHomotopy {A A' B B' C D : CochainComplex (ModuleCat ℚ) ℕ}
    (e : A ≅ A') (t : B ≅ B') (a : A ⟶ C) (b : B ⟶ D)
    (f : C ⟶ D) (g : A ⟶ B) (h : Homotopy (a ≫ f) (g ≫ b)) :
    Homotopy ((e.inv ≫ a) ≫ f) ((e.inv ≫ g ≫ t.hom) ≫ (t.inv ≫ b)) := by
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h.compLeft e.inv

/-- The line restriction square retains its actual projective-comparison homotopy. -/
def lineStabilizerCochainHomotopy (W : Rep.{0} ℚ principalSix) :
    Homotopy (lineStabilizerCochainComparison W ≫ homPullback lineChainMap W)
      (lineStabilizerRestriction W ≫ flagStabilizerCochainComparison W) :=
  shapiroComparisonHomotopy (fullShapiroIso principalSix Line W) (fullShapiroIso principalSix Flag W)
    _ _ _ _ (cochainComparisonHomotopy flagResolution flagStabilizerModel
      lineResolution lineStabilizerModel lineIncidence lineResolutionMap W)

/-- The plane restriction square retains its actual projective-comparison homotopy. -/
def planeStabilizerCochainHomotopy (W : Rep.{0} ℚ principalSix) :
    Homotopy (planeStabilizerCochainComparison W ≫ homPullback planeChainMap W)
      (planeStabilizerRestriction W ≫ flagStabilizerCochainComparison W) :=
  shapiroComparisonHomotopy (fullShapiroIso principalSix Plane W) (fullShapiroIso principalSix Flag W)
    _ _ _ _ (cochainComparisonHomotopy flagResolution flagStabilizerModel
      planeResolution planeStabilizerModel planeIncidence planeResolutionMap W)

/-- The full-family stabilizer incidence has the same literal line-minus-plane sign. -/
def stabilizerRestrictionDifference (W : Rep.{0} ℚ principalSix) :
    lineStabilizerCochains W ⊞ planeStabilizerCochains W ⟶ flagStabilizerCochains W :=
  biprod.desc (lineStabilizerRestriction W) (-planeStabilizerRestriction W)

/-- Both actual augmentation maps are preserved by the chosen stabilizer incidence lifts. -/
theorem stabilizerArrow_augmentations :
    lineStabilizerArrow ≫ lineStabilizerModel.π = flagStabilizerModel.π ≫
      (ChainComplex.single₀ (Rep ℚ principalSix)).map lineIncidence ∧
    planeStabilizerArrow ≫ planeStabilizerModel.π = flagStabilizerModel.π ≫
      (ChainComplex.single₀ (Rep ℚ principalSix)).map planeIncidence :=
  ⟨ProjectiveResolution.lift_commutes _ _ _,ProjectiveResolution.lift_commutes _ _ _⟩

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
