module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.ConePairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingCob
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TwistRep
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TraceEvalV
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.ConeInstance
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.GeoBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.InnerLift

@[expose] public section


/-!
# Basics for evaluating the cone pairing: coordinates and rational functionals

The coordinates `modelPush.iA/iL/iP ≫ innerLineCochain` of the line-supported cone cochains, the identification of
the corner projection `pA` of the push cone structure with the homotopy cofiber's `fstX` (so `pA 3 v` is
`cornerChain v`), and the evaluation `hom_eq_evalChain_r` of a morphism `ℚ[Y] ⟶ ℚ` of representations through a
`ℚ`-linear functional `r : ℂ → ℚ`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

attribute [local instance] Comparison.vertexAction

section Coordinates

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- The model cone as a push cone. -/
abbrev modelPush : PushCone (resFlag.complex) (resLine.complex) (resPlane.complex) coneR
    flagLineHom.hom flagPlaneHom.hom :=
  pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom

theorem innerLine_corner (z : cochains N6 (functionRepresentation ρ (Flags .line)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    modelPush.iA 1 ≫ innerLineCochain ρ z u = modelHomOf ρ psiEdge psiEdge_smul u := by
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerLineCochain ρ z u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerLineCochain ρ z u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg Prod.fst h).symm

theorem innerLine_line (z : cochains N6 (functionRepresentation ρ (Flags .line)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    modelPush.iL 2 ≫ innerLineCochain ρ z u = modelHomOf ρ psiLine psiLine_smul z := by
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerLineCochain ρ z u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerLineCochain ρ z u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.1) h).symm

theorem innerLine_plane (z : cochains N6 (functionRepresentation ρ (Flags .line)) 2)
    (u : cochains N6 (functionRepresentation ρ Edges) 1) :
    modelPush.iP 2 ≫ innerLineCochain ρ z u = 0 := by
  have h := signedConeHomSucc_apply flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1 (innerLineCochain ρ z u)
  have hc : signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
      (innerLineCochain ρ z u) =
      (modelHomOf ρ psiEdge psiEdge_smul u, (modelHomOf ρ psiLine psiLine_smul z, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  rw [hc] at h
  exact (congrArg (fun p => p.2.2) h).symm

end Coordinates

open HomologicalComplex in
theorem pA_eq_fstX :
    modelPush.pA 3 = homotopyCofiber.fstX (signedArrow flagLineHom.hom flagPlaneHom.hom) (3 + 1) 3
      (downSucc 3) := by
  apply modelPush.ext 3
  · rw [PushCone.pA, modelPush.iA_desc]
    exact (homotopyCofiber.inlX_fstX (signedArrow flagLineHom.hom flagPlaneHom.hom) 3 (3 + 1)
      (downSucc 3)).symm
  · rw [PushCone.pA, modelPush.iL_desc]
    change _ = coneIL flagLineHom.hom flagPlaneHom.hom (3 + 1) ≫ _
    unfold coneIL
    rw [Category.assoc, homotopyCofiber.inrX_fstX _ (3 + 1) 3 (downSucc 3), comp_zero]
  · rw [PushCone.pA, modelPush.iP_desc]
    change _ = coneIP flagLineHom.hom flagPlaneHom.hom (3 + 1) ≫ _
    unfold coneIP
    rw [Category.assoc, homotopyCofiber.inrX_fstX _ (3 + 1) 3 (downSucc 3), comp_zero]

section Functional

/-- The inclusion `ℚ ⟶ ℂ` of trivial representations. -/
def qToC : 𝟙_ (Rep.{0} ℚ Γ6) ⟶ Wℂ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (Algebra.linearMap ℚ ℂ)
    (fun g x => by simp))

theorem qToC_apply (x : ℚ) : qToC.hom x = (x : ℂ) := rfl

theorem evalChain_comp {Y : Type} (Ω : MonoidAlgebra ℚ Y) (f : Y → ℂ) (g : ℂ →ₗ[ℚ] ℂ) :
    g (evalChain Ω f) = evalChain Ω (fun y => g (f y)) := by
  simp only [evalChain, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    map_smul]

/-- A morphism out of `ℚ[Y]` to the trivial representation `ℚ`, whose values on the basis are `r (f y)`, evaluates a
chain `Ω` as `r (evalChain Ω f)`. -/
theorem hom_eq_evalChain_r {Y : Type} [MulAction Γ6 Y] (F : Rep.ofMulAction ℚ Γ6 Y ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (r : ℂ →ₗ[ℚ] ℚ) (f : Y → ℂ) (h : ∀ y, F.hom (MonoidAlgebra.single y 1) = r (f y))
    (Ω : MonoidAlgebra ℚ Y) : F.hom Ω = r (evalChain Ω f) := by
  have h1 := hom_eq_evalChain (F ≫ qToC) Ω
  have h2 : (F ≫ qToC).hom Ω = (F.hom Ω : ℂ) := rfl
  have h3 : (fun y => (F ≫ qToC).hom (MonoidAlgebra.single y 1)) =
      fun y => ((Algebra.linearMap ℚ ℂ).comp r) (f y) := by
    funext y
    exact congrArg (fun x : ℚ => (x : ℂ)) (h y)
  rw [h3, ← evalChain_comp] at h1
  have h4 := h2.symm.trans h1
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply, eq_ratCast] at h4
  exact_mod_cast h4

end Functional

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
