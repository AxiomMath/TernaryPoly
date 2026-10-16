module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerCoordinate
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.HomClass
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.FaceRestrictionModel

@[expose] public section


/-!
# The Shapiro coordinate in Mathlib's group cohomology of the stabilizer is the model's stabilizer cocycle

Let `ψ : X ≃ Z` identify a `GL₃(ℚ)`-set with a `Γ(6)`-set, `F : X` a point, `z = ψ F` and
`S = Stab_{Γ(6)}(z)`.  The Shapiro coordinate `faceCoord` of a class of the Hom complex of the model
resolution `ℚ[V^{•+1} × Z]` takes values in Mathlib's `groupCohomology (Rep.res S ρ) n`.  On the standard
resolution of `S` it is the cochain `(s_0, ..., s_k) ↦ c(s_0·1, ..., s_k·1; z)`.  For the Hom cochain
`modelHomOf f` of a model cochain `f` this is exactly the value of the model's Shapiro coordinate
`fixedPointCochain N6 ρ F` on the vertices `ι s_i` (`stabCoord_modelHomOf`), where `ι : S → N6 ⊓ Stab F`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open Finsupp

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)
  {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z] (ψ : X ≃ Z)
  (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x)

/-- The stabilizer in `Γ(6)` of a point. -/
abbrev stabΓ6 (z : Z) : Subgroup Γ6 := MulAction.stabilizer Γ6 z

theorem stabΓ6_fix (z : Z) : ∀ g : stabΓ6 z, g • z = z := fun g => g.2

include hψ in
/-- The image of the stabilizer in `Γ(6)` of `ψ F` lies in the stabilizer of `F` in the model level. -/
theorem iotaQ_mem_fixedPointLevel (F : X) (s : stabΓ6 (ψ F)) :
    iotaQ s.val ∈ fixedPointLevel N6 F := by
  refine ⟨iotaQ_mem s.val, ?_⟩
  show iotaQ s.val ∈ MulAction.stabilizer RationalGL3 F
  rw [MulAction.mem_stabilizer_iff]
  apply ψ.injective
  rw [hψ, s.2]

/-- **The Shapiro coordinate of a model cochain is its fixed-point cochain**, on the bar generator
`(x_1, ..., x_k)`: the vertices are the images `ι (x_1 ⋯ x_i)` of the partial products. -/
theorem stabCoord_modelHomOf (F : X) (k : ℕ) (f : cochains N6 (functionRepresentation ρ X) k)
    (x : Fin k → stabΓ6 (ψ F)) :
    (((stabCoord (stabΓ6 (ψ F)) (coeffRep ρ) (1 : RationalGL3) (ψ F) (stabΓ6_fix (ψ F))).f k).hom
        (modelHomOf ρ ψ hψ f)).hom (single x (MonoidAlgebra.single 1 1)) =
      (fixedPointCochain N6 ρ F k f).val
        (fun i => iotaQ ((Fin.partialProd x i : stabΓ6 (ψ F)) : Γ6)) := by
  rw [stabCoord_single, homFunA_modelHomOf]
  change f.1 (fun i => ((Fin.partialProd x i : stabΓ6 (ψ F)) : Γ6) • (1 : RationalGL3))
    (ψ.symm (ψ F)) = _
  rw [Equiv.symm_apply_apply]
  have hv : (fun i => ((Fin.partialProd x i : stabΓ6 (ψ F)) : Γ6) • (1 : RationalGL3)) =
      fun i => iotaQ ((Fin.partialProd x i : stabΓ6 (ψ F)) : Γ6) :=
    funext fun i => mul_one _
  rw [hv]
  rfl

/-- In degree two, with `x = (a, b)`: the vertices are `1, ι a, ι (a b)`, the cocycle `(a, b) ↦ F(1, a, ab)`
of `bridgeCocycle`. -/
theorem stabCoord_modelHomOf_two (F : X) (f : cochains N6 (functionRepresentation ρ X) 2)
    (a b : stabΓ6 (ψ F)) :
    (((stabCoord (stabΓ6 (ψ F)) (coeffRep ρ) (1 : RationalGL3) (ψ F) (stabΓ6_fix (ψ F))).f 2).hom
        (modelHomOf ρ ψ hψ f)).hom (single ![a, b] (MonoidAlgebra.single 1 1)) =
      (fixedPointCochain N6 ρ F 2 f).val ![1, iotaQ a.val, iotaQ (a * b).val] := by
  rw [stabCoord_modelHomOf ρ ψ hψ F 2 f ![a, b]]
  refine congrArg (fixedPointCochain N6 ρ F 2 f).val ?_
  have h1 : Fin.partialProd ![a, b] 1 = a := by
    rw [show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.partialProd_succ]
    simp [Fin.partialProd_zero]
  have h2 : Fin.partialProd ![a, b] 2 = a * b := by
    rw [show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.partialProd_succ]
    simp [h1]
  funext i
  fin_cases i
  · simp [Fin.partialProd_zero]
  · exact congrArg (fun t : stabΓ6 (ψ F) => iotaQ t.val) h1
  · exact congrArg (fun t : stabΓ6 (ψ F) => iotaQ t.val) h2

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
