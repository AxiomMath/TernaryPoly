module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneSelfGroup

@[expose] public section


/-!
# The big stabilizer of a plane face as a `FaceAction`

Formalized by Claude Sonnet 5.5.

`planeFaceAction`: the group `bigPlaneStabAt h` acts on the extension of the plane cusp `h⁻¹ P h` of `Γ(N)` (`N ≥ 3`) by conjugation, on the radical lattice by `planeGφ`, on the Levi `Γ(N)` by conjugation by the Levi block `planeGA`, and on a coefficient module of `SL₃(ℤ)` by `ρ f`.
`planeFaceAction_radDet`: the determinant of the radical map of the self-twist `(F.twist f).φ` is the determinant of the inverse Levi block, so the two orientation signs of `FaceAction.pairing_scale` cancel.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ)) {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ SL(3, ℤ) V)

/-- **The big stabilizer of the plane cusp `h⁻¹ P h` as a group of face automorphisms.** -/
def planeFaceAction : FaceAction hN (faceExt N h) (planeGRep ρ N h) ↥(bigPlaneStabAt h) where
  θ := planeGθ N hN h
  φ := planeGφ N hN h
  α := planeGα N hN h
  A := planeGA h
  T f := coeffEquiv ρ f.1
  T_one v := by
    change ρ ((1 : bigPlaneStabAt h) : SL(3, ℤ)) v = v
    rw [Subgroup.coe_one, map_one]; rfl
  T_mul f g v := by
    change ρ ((f * g : bigPlaneStabAt h) : SL(3, ℤ)) v = ρ f.1 (ρ g.1 v)
    rw [Subgroup.coe_mul, map_mul]; rfl
  inl_comm := planeG_inl_comm N hN h
  rightHom_comm := planeG_rightHom_comm N hN h
  hT f e v := planeGT_hT ρ N hN h f e v
  hA := planeG_hA N hN h

theorem planeFaceAction_radDet (f : bigPlaneStabAt h) :
    radDet ((planeFaceAction N hN h ρ).twist f).φ.toMonoidHom = ((((planeFaceAction N hN h ρ).A f)⁻¹).val.det : ℤ) :=
  planeGφ_inv_radDet_inv N hN h f

end TernaryPeriodPolynomials.Argument.FaceDescent
