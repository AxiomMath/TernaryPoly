module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FaceCarriers
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCap

@[expose] public section


/-!
# The face cone of the library as a labelled pushout cone

`faceCone = homotopyCofiber (biprod.lift lineChainMap (-planeChainMap))` is the pushout cone of the equivariant
singular chains of the three face sums.  This file records its data: the diagonal systems of the three strata
(`singDiagSystem`), strictness of `lineChainMap`, `planeChainMap` (naturality of the Alexander-Whitney diagonal), the
label carriers `T` of `FaceCarriers`, and their acyclicity.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.OrdinaryIncidence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

namespace FaceCone

/-- The face cone as a pushout cone of the three face-sum chain complexes. -/
abbrev cone : PushCone flagChains lineChains planeChains
    (pushCone lineChainMap planeChainMap) lineChainMap planeChainMap :=
  pushConeOfCofiber lineChainMap planeChainMap

/-- The three diagonal systems. -/
abbrev SA := singDiagSystem (G := principalSix) (TopCat.of CornerFaceSum)
abbrev SL := singDiagSystem (G := principalSix) (TopCat.of LineFaceSum)
abbrev SP := singDiagSystem (G := principalSix) (TopCat.of PlaneFaceSum)

theorem strict : PushCone.Strict (a := lineChainMap) (b := planeChainMap) SA SL SP where
  a_strict p q n h := singDiag_natural (TopCat.of CornerFaceSum) lineFaceMap lineFaceMap_equivariant p q n h
  b_strict p q n h := singDiag_natural (TopCat.of CornerFaceSum) planeFaceMap planeFaceMap_equivariant p q n h
  a_eps := spaceChainMap_eps (TopCat.of CornerFaceSum) lineFaceMap lineFaceMap_equivariant
  b_eps := spaceChainMap_eps (TopCat.of CornerFaceSum) planeFaceMap planeFaceMap_equivariant

/-- The label carriers of the face cone. -/
def targets : PushTargets cone Flag Line Plane flagLine flagPlane where
  FA := flagFaceK
  FL := lineFaceK
  FP := planeFaceK
  FA_smul := flagFaceK_smul
  FL_smul := lineFaceK_smul
  FP_smul := planeFaceK_smul
  ha := fun f m _ hx => lineChainMap_flagFaceK f m hx
  hb := fun f m _ hx => planeChainMap_flagFaceK f m hx

theorem good : PushCone.PushTargets.Good cone SA SL SP targets where
  hA f := { sub := fun m _ hx => flagFaceK_subcomplex hx
            acyc0 := fun y hy h0 => flagFaceK_acyc0 f hy h0
            acyc := fun m _ hy h0 => flagFaceK_acyc f m hy h0
            surj := flagFaceK_exists_vertex f }
  hL z := { sub := fun m _ hx => lineFaceK_subcomplex hx
            acyc0 := fun y hy h0 => lineFaceK_acyc0 z hy h0
            acyc := fun m _ hy h0 => lineFaceK_acyc z m hy h0
            surj := lineFaceK_exists_vertex z }
  hP z := { sub := fun m _ hx => planeFaceK_subcomplex hx
            acyc0 := fun y hy h0 => planeFaceK_acyc0 z hy h0
            acyc := fun m _ hy h0 => planeFaceK_acyc z m hy h0
            surj := planeFaceK_exists_vertex z }
  haeps x := by
    have := congrArg (fun φ => φ.hom x)
      (spaceChainMap_eps (TopCat.of CornerFaceSum) lineFaceMap lineFaceMap_equivariant)
    exact this
  hbeps x := by
    have := congrArg (fun φ => φ.hom x)
      (spaceChainMap_eps (TopCat.of CornerFaceSum) planeFaceMap planeFaceMap_equivariant)
    exact this

theorem respects_flag (f : Flag) : DiagRespects SA (flagFaceK f) := fun p q n h _ hx => flagFaceK_diag f p q n h hx
theorem respects_line (z : Line) : DiagRespects SL (lineFaceK z) := fun p q n h _ hx => lineFaceK_diag z p q n h hx
theorem respects_plane (z : Plane) : DiagRespects SP (planeFaceK z) := fun p q n h _ hx => planeFaceK_diag z p q n h hx

end FaceCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
