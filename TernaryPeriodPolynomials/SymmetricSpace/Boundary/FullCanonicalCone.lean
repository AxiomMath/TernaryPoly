module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullCanonicalIncidence
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeEquivalence

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory Category Limits HomologicalComplex Preadditive
open BoundaryFaceResolutionComparison EquivariantSingularSmall

/-- The literal full induced-bar incidence, ordered line then plane with line-minus-plane sign. -/
def canonicalFaceArrow : inducedBarComplex OrdinaryParabolicGroups.B ⟶
    inducedBarComplex OrdinaryParabolicGroups.Q ⊞ inducedBarComplex OrdinaryParabolicGroups.P :=
  biprod.lift canonicalLineArrow (-canonicalPlaneArrow)

abbrev canonicalFaceCone := homotopyCofiber canonicalFaceArrow

/-- Identity on all parabolic face complexes, with the actual augmentation-induced homotopies. -/
def canonicalFaceSquare : Homotopy (parabolicFaceArrow ≫ 𝟙 _)
    (𝟙 _ ≫ canonicalFaceArrow) := by
  have hl : Homotopy (parabolicLineArrow ≫ 𝟙 _) (𝟙 _ ≫ canonicalLineArrow) := by
    exact (Homotopy.ofEq (Category.comp_id _)).trans
      (canonicalLineHomotopy.trans (Homotopy.ofEq (Category.id_comp _).symm))
  have hp : Homotopy (parabolicPlaneArrow ≫ 𝟙 _) (𝟙 _ ≫ canonicalPlaneArrow) := by
    exact (Homotopy.ofEq (Category.comp_id _)).trans
      (canonicalPlaneHomotopy.trans (Homotopy.ofEq (Category.id_comp _).symm))
  have hid : biprod.map (𝟙 lineParabolicResolution.complex) (𝟙 planeParabolicResolution.complex) =
      𝟙 (lineParabolicResolution.complex ⊞ planeParabolicResolution.complex) := by
    apply biprod.hom_ext <;> simp
  have h := SymmetricSpaceBoundaryGeometricCone.signedSquareHomotopy _ _ _ _ _ _ _ hl hp
  rw [hid] at h
  exact h

/-- Genuine total comparison from the resolution-lift cone to the literal restriction cone. -/
def parabolicToCanonical : parabolicFaceCone ⟶ canonicalFaceCone :=
  CofiberSequence.comparisonMap parabolicFaceArrow canonicalFaceArrow (𝟙 _) (𝟙 _) canonicalFaceSquare

instance parabolicToCanonical_quasiIso : QuasiIso parabolicToCanonical :=
  CofiberSequence.comparisonMap_quasiIso _ _ _ _ _ (_root_.HomotopyEquiv.refl _) rfl
    (_root_.HomotopyEquiv.refl _) rfl

theorem parabolicToCanonical_inr : homotopyCofiber.inr parabolicFaceArrow ≫ parabolicToCanonical =
    homotopyCofiber.inr canonicalFaceArrow := by
  exact (CofiberSequence.inr_comparisonMap parabolicFaceArrow canonicalFaceArrow (𝟙 _) (𝟙 _) canonicalFaceSquare).trans (Category.id_comp _)

theorem canonicalFaceCone_projective (n : ℕ) : Projective (canonicalFaceCone.X n) := by
  have : ∀ n, Projective ((inducedBarComplex OrdinaryParabolicGroups.B).X n) := flagParabolicResolution.projective
  have : ∀ n, Projective (((inducedBarComplex OrdinaryParabolicGroups.Q) ⊞ (inducedBarComplex OrdinaryParabolicGroups.P)).X n) :=
    parabolicMiddle_projective
  exact projectiveCone canonicalFaceArrow n

theorem exists_parabolicCanonicalEquiv : ∃ e : _root_.HomotopyEquiv parabolicFaceCone canonicalFaceCone,
    e.hom=parabolicToCanonical := by
  have : ∀ n, Projective (parabolicFaceCone.X n) := parabolicFaceCone_projective
  have : ∀ n, Projective (canonicalFaceCone.X n) := canonicalFaceCone_projective
  exact (ChainComplex.quasiIso_iff_of_projective parabolicToCanonical).mp inferInstance

def parabolicCanonicalEquiv := Classical.choose exists_parabolicCanonicalEquiv

theorem parabolicCanonicalEquiv_hom : parabolicCanonicalEquiv.hom=parabolicToCanonical :=
  Classical.choose_spec exists_parabolicCanonicalEquiv

/-- The entire genuine geometric boundary has the canonical full induced P/Q/B cone model. -/
def canonicalBoundaryEquiv : _root_.HomotopyEquiv fullBoundaryChains canonicalFaceCone :=
  (fullFaceBoundaryEquiv.symm.trans fullFaceConeParabolicEquiv).trans parabolicCanonicalEquiv

abbrev canonicalCochains (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) := homCochains canonicalFaceCone W

def canonicalToBoundary (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    canonicalCochains W ⟶ homCochains fullBoundaryChains W := homPullback canonicalBoundaryEquiv.hom W

instance canonicalToBoundary_quasiIso (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    QuasiIso (canonicalToBoundary W) := homPullback_quasiIso_of_homotopyEquiv canonicalBoundaryEquiv W

end TernaryPoly.SymmetricSpaceBoundaryFull
