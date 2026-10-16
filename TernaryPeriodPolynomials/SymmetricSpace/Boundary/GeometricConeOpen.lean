module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Cone
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyComplete
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory Category Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryIncidenceHomology EquivariantSingularSmall
open EquivariantSingularMayerVietoris SingularLocalCoefficient

/-- The actual graded Mayer–Vietoris splitting for the entire geometric boundary. -/
def openSplitting (n : ℕ) :=
  evaluatedSplitting principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover n

def openRetraction (n : ℕ) : mvComplex.X₂.X n ⟶ mvComplex.X₁.X n := (openSplitting n).r
def openSection (n : ℕ) : mvComplex.X₃.X n ⟶ mvComplex.X₂.X n := (openSplitting n).s

theorem open_f_r (n : ℕ) : mvComplex.f.f n ≫ openRetraction n=𝟙 _ := (openSplitting n).f_r
theorem open_s_g (n : ℕ) : openSection n ≫ mvComplex.g.f n=𝟙 _ := (openSplitting n).s_g
theorem open_split (n : ℕ) : openRetraction n ≫ mvComplex.f.f n + mvComplex.g.f n ≫ openSection n=𝟙 _ :=
  (openSplitting n).id

/-- The actual shifted total cone of the signed open-cover chain incidence. -/
abbrev openCone := homotopyCofiber mvComplex.f

def openConeSmallEquiv : _root_.HomotopyEquiv openCone smallComplex :=
  BoundaryFaceResolutionComparison.Cone.equivalence mvComplex openRetraction open_f_r openSection open_s_g open_split

/-- The actual cone comparison to the entire boundary has no auxiliary acyclicity hypothesis. -/
def openConeBoundaryEquiv : _root_.HomotopyEquiv openCone boundaryChains := openConeSmallEquiv.trans smallEquiv

/-- The forward chain map is literally the cone projection followed by the small-chain inclusion. -/
theorem openConeBoundaryEquiv_hom : openConeBoundaryEquiv.hom=
    BoundaryFaceResolutionComparison.Cone.projection mvComplex ≫ smallEquiv.hom := rfl

/-- The cone comparison retains the genuine geometric Mayer–Vietoris sum map. -/
theorem openConeBoundaryEquiv_inr : homotopyCofiber.inr mvComplex.f ≫ openConeBoundaryEquiv.hom=
    mvComplex.g ≫ smallEquiv.hom := by
  change _ ≫ (BoundaryFaceResolutionComparison.Cone.projection mvComplex ≫ smallEquiv.hom)=_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun m => m ≫ smallEquiv.hom) (BoundaryFaceResolutionComparison.Cone.inr_projection mvComplex))

/-- Arbitrary rational-coefficient total cochains of the genuine signed open-cover cone. -/
abbrev openTotalCochains (W : Rep.{0} ℚ principalSix) := homCochains openCone W

/-- Actual equivariant boundary cochains map to the total cone by genuine chain precomposition. -/
def boundaryToOpenTotal (W : Rep.{0} ℚ principalSix) : homCochains boundaryChains W ⟶ openTotalCochains W :=
  homPullback openConeBoundaryEquiv.hom W

instance boundaryToOpenTotal_quasiIso (W : Rep.{0} ℚ principalSix) : QuasiIso (boundaryToOpenTotal W) :=
  homPullback_quasiIso_of_homotopyEquiv openConeBoundaryEquiv W

/-- Actual geometric local-system cochains on the quotient boundary. -/
abbrev localBoundaryCochains (W : Rep.{0} ℚ principalSix) :=
  localCochains SingularBoundaryRestriction.boundaryProjection SingularBoundaryRestriction.boundaryQuotientCovering W

/-- The actual geometric local-system comparison with the total open-cover cone. -/
def localBoundaryToOpenTotal (W : Rep.{0} ℚ principalSix) : localBoundaryCochains W ⟶ openTotalCochains W :=
  (cochainIso SingularBoundaryRestriction.boundaryProjection SingularBoundaryRestriction.boundaryQuotientCovering W).inv ≫
    boundaryToOpenTotal W

instance localBoundaryToOpenTotal_quasiIso (W : Rep.{0} ℚ principalSix) : QuasiIso (localBoundaryToOpenTotal W) := by
  unfold localBoundaryToOpenTotal
  infer_instance

/-- Total-cone restriction is exactly the actual boundary restriction to the two open pieces. -/
theorem boundaryToOpenTotal_restriction (W : Rep.{0} ℚ principalSix) :
    boundaryToOpenTotal W ≫ homPullback (homotopyCofiber.inr mvComplex.f) W=
      homPullback (mvComplex.g ≫ smallEquiv.hom) W :=
  (homPullback_comp _ _ W).symm.trans (congrArg (fun m => homPullback m W) openConeBoundaryEquiv_inr)

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
