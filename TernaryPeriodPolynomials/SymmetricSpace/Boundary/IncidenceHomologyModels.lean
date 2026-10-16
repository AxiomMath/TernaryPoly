module

public import TernaryPeriodPolynomials.Topology.Equivariant.MayerVietoris.HomologyFunctor
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FaceAugmentationComplete
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisExact
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallSubspaceNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open IntegralGL3Congruence SingularBoundaryRestriction SymmetricSpaceBoundaryMV
open EquivariantSingularResolution EquivariantSingularSmall EquivariantSingularMayerVietoris
open EquivariantMayerVietorisHomology SymmetricSpaceBoundaryFaceAugmentation

abbrev ambient := TopCat.of BoundaryCover
abbrev boundaryChains := equivariantChains principalSix ambient

def lineOpen : Opens ambient := ⟨UpstairsLine,upstairsLine_open⟩
def planeOpen : Opens ambient := ⟨UpstairsPlane,upstairsPlane_open⟩

theorem lineOpen_invariant : InvariantSet principalSix ambient (lineOpen : Set ambient) :=
  fun g x hx => (upstairs_invariant lineNeighborhood g x).mpr hx

theorem planeOpen_invariant : InvariantSet principalSix ambient (planeOpen : Set ambient) :=
  fun g x hx => (upstairs_invariant planeNeighborhood g x).mpr hx

theorem opens_cover : lineOpen ⊔ planeOpen=⊤ := by
  apply SetLike.coe_injective
  exact upstairs_cover

abbrev Intersection := ((lineOpen : Set ambient) ∩ (planeOpen : Set ambient))

theorem intersection_invariant : InvariantSet principalSix ambient Intersection :=
  invariant_inter principalSix ambient _ _ lineOpen_invariant planeOpen_invariant

instance intersectionAction : MulAction principalSix Intersection where
  smul g x := ⟨g • x.val,intersection_invariant g x.val x.property⟩
  one_smul x := Subtype.ext (one_smul principalSix x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance intersectionContinuous : ContinuousConstSMul principalSix Intersection :=
  ⟨fun g => ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

abbrev leftComplex := leftChains principalSix ambient lineOpen lineOpen_invariant
abbrev rightComplex := rightChains principalSix ambient planeOpen planeOpen_invariant
abbrev interComplex := interChains principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant
abbrev smallComplex := coverChains principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover

def mvComplex : ShortComplex (ChainComplex (Rep ℚ principalSix) ℕ) :=
  chainShortComplex principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover

theorem mvShortExact : mvComplex.ShortExact :=
  chainShortExact principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover

/-- The actual small-chain equivalence retains the literal ambient inclusion. -/
def smallEquiv : _root_.HomotopyEquiv smallComplex boundaryChains :=
  smallHomotopyEquiv principalSix ambient _
    (twoSetCover_invariant principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover)

def ambientHomologyIso (n : ℕ) : smallComplex.homology n ≅ boundaryChains.homology n :=
  smallEquiv.toHomologyIso n

def lineSubspaceIso : equivariantChains principalSix (TopCat.of UpstairsLine) ≅ leftComplex :=
  subspaceIso principalSix ambient UpstairsLine lineOpen_invariant (fun _ _ => rfl)

def planeSubspaceIso : equivariantChains principalSix (TopCat.of UpstairsPlane) ≅ rightComplex :=
  subspaceIso principalSix ambient UpstairsPlane planeOpen_invariant (fun _ _ => rfl)

def interSubspaceIso : equivariantChains principalSix (TopCat.of Intersection) ≅ interComplex :=
  subspaceIso principalSix ambient Intersection intersection_invariant (fun _ _ => rfl)

/-- The intersection here is literally the overlap of the invariant two-open cover. -/
def intersectionHomeomorph : Intersection ≃ₜ UpstairsOverlap := Homeomorph.setCongr upstairs_inter

theorem intersectionHomeomorph_equivariant (g : principalSix) (x : Intersection) :
    intersectionHomeomorph (g • x)=g • intersectionHomeomorph x := rfl

theorem intersectionHomeomorph_symm_equivariant (g : principalSix) (x : UpstairsOverlap) :
    intersectionHomeomorph.symm (g • x)=g • intersectionHomeomorph.symm x := rfl

def cornerModelEquiv : ContinuousMap.HomotopyEquiv CornerFaceSum Intersection :=
  cornerFaceSumEquiv.trans intersectionHomeomorph.symm.toHomotopyEquiv

theorem cornerModelEquiv_equivariant (g : principalSix) (x : CornerFaceSum) :
    cornerModelEquiv (g • x)=g • cornerModelEquiv x := by
  exact congrArg intersectionHomeomorph.symm (cornerFaceSumEquiv_equivariant g x)

theorem cornerModelEquiv_inv_equivariant (g : principalSix) (x : Intersection) :
    cornerModelEquiv.invFun (g • x)=g • cornerModelEquiv.invFun x :=
  cornerSumRetraction_equivariant g (intersectionHomeomorph x)

/-- Each subordinate-chain homology is identified by the actual face retraction. -/
def leftFaceHomologyIso (n : ℕ) : leftComplex.homology n ≅ lineChains.homology n :=
  (homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) n).mapIso lineSubspaceIso.symm ≪≫
    (spaceHomologyIso lineFaceSumEquiv lineFaceSumEquiv_equivariant lineSumRetraction_equivariant n).symm

def rightFaceHomologyIso (n : ℕ) : rightComplex.homology n ≅ planeChains.homology n :=
  (homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) n).mapIso planeSubspaceIso.symm ≪≫
    (spaceHomologyIso planeFaceSumEquiv planeFaceSumEquiv_equivariant planeSumRetraction_equivariant n).symm

def interFaceHomologyIso (n : ℕ) : interComplex.homology n ≅ flagChains.homology n :=
  (homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) n).mapIso interSubspaceIso.symm ≪≫
    (spaceHomologyIso cornerModelEquiv cornerModelEquiv_equivariant cornerModelEquiv_inv_equivariant n).symm

def leftH0Iso : leftComplex.homology 0 ≅ lineLabels := leftFaceHomologyIso 0 ≪≫ lineH0Iso
def rightH0Iso : rightComplex.homology 0 ≅ planeLabels := rightFaceHomologyIso 0 ≪≫ planeH0Iso
def interH0Iso : interComplex.homology 0 ≅ flagLabels := interFaceHomologyIso 0 ≪≫ flagH0Iso

theorem left_positive (n : ℕ) (hn : n≠0) : IsZero (leftComplex.homology n) :=
  (linePositiveHomology n hn).of_iso (leftFaceHomologyIso n)

theorem right_positive (n : ℕ) (hn : n≠0) : IsZero (rightComplex.homology n) :=
  (planePositiveHomology n hn).of_iso (rightFaceHomologyIso n)

theorem inter_positive (n : ℕ) (hn : n≠0) : IsZero (interComplex.homology n) :=
  (flagPositiveHomology n hn).of_iso (interFaceHomologyIso n)

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
