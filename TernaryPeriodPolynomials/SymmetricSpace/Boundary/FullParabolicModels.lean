module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullIncidence
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullOrbits

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory ModThreeGoodAction OrdinaryIncidence SymmetricSpaceBoundaryMV
open SymmetricSpaceBoundaryFaces BoundaryFaceResolutionComparison EquivariantSingularSmall

section Generic
variable (G : Type) [Group G] {X : Type} [MulAction G X] (a : X)
    (ha : ∀ x : X, ∃ g : G, g • a = x)

def fullOrbitEquiv : MulAction.orbit G a ≃ X :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,fun x =>
    ⟨⟨x,ha x⟩,rfl⟩⟩

/-- The transitive orbit module is the complete boundary label module. -/
def fullOrbitLabelIso : orbitLabels G a ≅ Rep.ofMulAction ℚ G X :=
  permutationIso G (fullOrbitEquiv G a ha) (fun _ _ => rfl)

/-- Genuine induction from the actual full stabilizer resolves all labels. -/
def fullParabolicResolution : ProjectiveResolution (Rep.ofMulAction ℚ G X) where
  complex := (orbitResolution G a).complex
  projective := (orbitResolution G a).projective
  π := (orbitResolution G a).π ≫ (ChainComplex.single₀ (Rep ℚ G)).map (fullOrbitLabelIso G a ha).hom
  quasiIso := by infer_instance

/-- Identity-induction evaluation gives the exact full-stabilizer bar complex. -/
def fullParabolicShapiro (W : Rep.{0} ℚ G) :
    homCochains (fullParabolicResolution G a ha).complex W ≅
      homCochains (Rep.barResolution ℚ (stabilizer G a)).complex (Rep.res (stabilizer G a).subtype W) :=
  orbitShapiroIso G a W

theorem fullParabolic_augmentation (g : G)
    (b : (Rep.barResolution ℚ (stabilizer G a)).complex.X 0) :
    (fullParabolicResolution G a ha).π.f 0
      (Representation.IndV.mk (stabilizer G a).subtype
        ((Rep.barResolution ℚ (stabilizer G a)).complex.X 0).ρ g b) =
      MonoidAlgebra.single (g⁻¹ • a) (barAugmentValue G a b) := by
  change (fullOrbitLabelIso G a ha).hom
    ((orbitResolution G a).π.f 0 _) = _
  rw [orbitResolution_augmentation_mk]
  exact SingularComponentAugmentation.permutationMap_single (fullOrbitEquiv G a ha)
    (fun _ _ => rfl) (orbitPoint G a g⁻¹) (barAugmentValue G a b)

/-- Induction from the literal specified parabolic, with its proved actual stabilizer equality. -/
def fullInducedLabelIso (S : Subgroup G) (hs : stabilizer G a = S) :
    Rep.ind S.subtype (Rep.trivial ℚ S ℚ) ≅ Rep.ofMulAction ℚ G X := by
  cases hs
  exact inducedOrbitIso G a ≪≫ fullOrbitLabelIso G a ha

def fullParabolicResolutionAt (S : Subgroup G) (hs : stabilizer G a = S) :
    ProjectiveResolution (Rep.ofMulAction ℚ G X) where
  complex := ((Rep.indFunctor ℚ S.subtype).mapProjectiveResolution (Rep.barResolution ℚ S)).complex
  projective := ((Rep.indFunctor ℚ S.subtype).mapProjectiveResolution (Rep.barResolution ℚ S)).projective
  π := ((Rep.indFunctor ℚ S.subtype).mapProjectiveResolution (Rep.barResolution ℚ S)).π ≫
    (ChainComplex.single₀ (Rep ℚ G)).map (fullInducedLabelIso G a ha S hs).hom
  quasiIso := by infer_instance

def fullParabolicShapiroAt (S : Subgroup G) (hs : stabilizer G a = S) (W : Rep.{0} ℚ G) :
    homCochains (fullParabolicResolutionAt G a ha S hs).complex W ≅
      homCochains (Rep.barResolution ℚ S).complex (Rep.res S.subtype W) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (Rep.indResHomEquiv S.subtype _ W).toModuleIso) (fun _ _ _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro b
      rfl)

def fullParabolicShapiroAtDegree (S : Subgroup G) (hs : stabilizer G a = S) (W : Rep.{0} ℚ G)
    (n : ℕ) (c : (fullParabolicResolutionAt G a ha S hs).complex.X n ⟶ W) :
    (Rep.barResolution ℚ S).complex.X n ⟶ Rep.res S.subtype W :=
  (fullParabolicShapiroAt G a ha S hs W).hom.f n c

/-- Literal identity-induction evaluation for the exact subgroup, with no discarded coefficient coordinates. -/
theorem fullParabolicShapiroAt_evaluation (S : Subgroup G) (hs : stabilizer G a = S) (W : Rep.{0} ℚ G)
    (n : ℕ) (c : (fullParabolicResolutionAt G a ha S hs).complex.X n ⟶ W)
    (b : (Rep.barResolution ℚ S).complex.X n) :
    (fullParabolicShapiroAtDegree G a ha S hs W n c).hom b =
      c.hom (Representation.IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X n).ρ 1 b) := rfl


end Generic

abbrev lineParabolicResolution := fullParabolicResolutionAt IntegralGL standardLine fullLine_transitive
  OrdinaryParabolicGroups.Q standardLine_stabilizer
abbrev planeParabolicResolution := fullParabolicResolutionAt IntegralGL standardPlane fullPlane_transitive
  OrdinaryParabolicGroups.P standardPlane_stabilizer
abbrev flagParabolicResolution := fullParabolicResolutionAt IntegralGL standardFlag fullFlag_transitive
  OrdinaryParabolicGroups.B standardFlag_stabilizer

/-- Actual augmentation-preserving comparison to the full integral parabolic line model. -/
def lineParabolicComparison := comparison fullLineResolution lineParabolicResolution

def planeParabolicComparison := comparison fullPlaneResolution planeParabolicResolution

def flagParabolicComparison := comparison fullFlagResolution flagParabolicResolution

def parabolicLineArrow := ProjectiveResolution.lift fullLineIncidence flagParabolicResolution lineParabolicResolution

def parabolicPlaneArrow := ProjectiveResolution.lift fullPlaneIncidence flagParabolicResolution planeParabolicResolution

def parabolicLineHomotopy : Homotopy (fullLineChainMap ≫ lineParabolicComparison.hom)
    (flagParabolicComparison.hom ≫ parabolicLineArrow) :=
  comparisonHomotopy fullFlagResolution flagParabolicResolution fullLineResolution lineParabolicResolution
    fullLineIncidence fullLineResolutionMap

def parabolicPlaneHomotopy : Homotopy (fullPlaneChainMap ≫ planeParabolicComparison.hom)
    (flagParabolicComparison.hom ≫ parabolicPlaneArrow) :=
  comparisonHomotopy fullFlagResolution flagParabolicResolution fullPlaneResolution planeParabolicResolution
    fullPlaneIncidence fullPlaneResolutionMap

end TernaryPoly.SymmetricSpaceBoundaryFull
