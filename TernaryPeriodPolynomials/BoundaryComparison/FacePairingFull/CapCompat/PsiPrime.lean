module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.ConeInstance
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FaceBoundary

@[expose] public section


/-!
# The comparison `Ψ' : coneR ⟶ boundaryChains`

`Ψ' = Ψ_F' ≫ faceConeToBoundary` is a quasi-isomorphism from the model cone to the singular chains of the boundary
cover, whose cap product with every cocycle `c` of the boundary chains agrees, up to a homotopy, with the cap of the
model cone against `Ψ' ≫ c` (`exists_PsiPrime`).  The cap on the boundary chains is the Alexander-Whitney cap `capE`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.OrdinaryIncidence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

/-- The Alexander-Whitney diagonal system of the boundary singular chains. -/
abbrev boundaryDiagSystem : DiagSystem boundaryChains :=
  singDiagSystem (G := principalSix) (TopCat.of ambient)

theorem faceConeToBoundary_capStrict :
    faceDiagSystem.toCapSystem.Strict boundaryDiagSystem.toCapSystem faceConeToBoundary :=
  DiagSystem.capStrict faceDiagSystem boundaryDiagSystem faceConeToBoundary faceConeToBoundary_strict

/-- **The carrier-respecting comparison `Ψ' : coneR ⟶ boundaryChains`.** -/
theorem exists_PsiPrime : ∃ Ψ : coneR ⟶ boundaryChains, QuasiIso Ψ ∧
    ∀ {W : Rep.{0} ℚ Γ6} {n : ℕ} (c : boundaryChains.X n ⟶ W) (hc : boundaryChains.d (n+1) n ≫ c = 0),
      CapSystem.Homotopic modelDiagSystem.toCapSystem boundaryDiagSystem.toCapSystem Ψ c hc := by
  obtain ⟨u, hq, -, H⟩ := exists_PsiF
  refine ⟨u ≫ faceConeToBoundary, inferInstance, fun c hc => ?_⟩
  exact (H (faceConeToBoundary.f _ ≫ c) (chainMap_cocycle faceConeToBoundary c hc)).comp_strict
    faceConeToBoundary faceConeToBoundary_capStrict c hc

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
