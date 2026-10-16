module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeRestriction

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory Category Limits HomologicalComplex ModThreeGoodAction IntegralGL3Congruence
open SymmetricSpaceBoundaryMV SingularCoverNaturality SymmetricSpaceBoundaryFullTransfer
open EquivariantMayerVietorisHomology SymmetricSpaceBoundaryFaceAugmentation

/-- The full integral line-face inclusion is the actual geometric inclusion. -/
theorem fullLineToBoundary_equivariant (g : IntegralGL) (x : LineFaceSum) :
    SymmetricSpaceBoundaryGeometricCone.lineToBoundary (g • x) =
      g • SymmetricSpaceBoundaryGeometricCone.lineToBoundary x := by
  apply Subtype.ext
  exact fullLineSum_value g x

theorem fullPlaneToBoundary_equivariant (g : IntegralGL) (x : PlaneFaceSum) :
    SymmetricSpaceBoundaryGeometricCone.planeToBoundary (g • x) =
      g • SymmetricSpaceBoundaryGeometricCone.planeToBoundary x := by
  apply Subtype.ext
  exact fullPlaneSum_value g x

def fullLineChainToBoundary : fullLineChains ⟶ fullBoundaryChains :=
  chainMap SymmetricSpaceBoundaryGeometricCone.lineToBoundary fullLineToBoundary_equivariant

def fullPlaneChainToBoundary : fullPlaneChains ⟶ fullBoundaryChains :=
  chainMap SymmetricSpaceBoundaryGeometricCone.planeToBoundary fullPlaneToBoundary_equivariant

def fullFacesToBoundary : fullLineChains ⊞ fullPlaneChains ⟶ fullBoundaryChains :=
  biprod.desc fullLineChainToBoundary fullPlaneChainToBoundary

/-- Both corner inclusions are the same actual singular boundary inclusion. -/
theorem fullFlag_boundary_square :
    fullLineChainMap ≫ fullLineChainToBoundary = fullPlaneChainMap ≫ fullPlaneChainToBoundary := by
  unfold fullLineChainMap fullLineChainToBoundary fullPlaneChainMap fullPlaneChainToBoundary
  rw [← chainMap_comp,← chainMap_comp]
  congr 1
  ext x : 1
  apply Subtype.ext
  change (cornerToLineSum x).2.val = (cornerToPlaneSum x).2.val
  rcases x with ⟨F,x⟩
  rw [cornerToLineSum_apply,cornerToPlaneSum_apply]

theorem fullFace_boundary_zero : fullFaceArrow ≫ fullFacesToBoundary = 0 := by
  change biprod.lift fullLineChainMap (-fullPlaneChainMap) ≫
    biprod.desc fullLineChainToBoundary fullPlaneChainToBoundary = 0
  rw [biprod.lift_desc,Preadditive.neg_comp,fullFlag_boundary_square,add_neg_cancel]

/-- The full integral face cone maps to the entire geometric boundary by actual inclusions. -/
def fullFaceConeToBoundary : fullFaceCone ⟶ fullBoundaryChains :=
  homotopyCofiber.desc fullFaceArrow fullFacesToBoundary (Homotopy.ofEq fullFace_boundary_zero)

theorem fullFaceConeToBoundary_inr :
    homotopyCofiber.inr fullFaceArrow ≫ fullFaceConeToBoundary = fullFacesToBoundary :=
  homotopyCofiber.inr_desc _ _ _

theorem fullFaceConeToBoundary_inl (n : ℕ) :
    homotopyCofiber.inlX fullFaceArrow n (n+1) rfl ≫ (fullFaceConeToBoundary.f (n+1)) = 0 :=
  homotopyCofiber.inlX_desc_f _ _ _ _ _ _

end TernaryPoly.SymmetricSpaceBoundaryFull
