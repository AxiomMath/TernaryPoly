module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineSelfGroup

@[expose] public section


/-!
# The big stabilizer of a line face as a `FaceAction`

Formalized by Claude Sonnet 5.5.

`lineFaceAction`: the group `bigLineStabAt h` acts on the extension of the line cusp `h⁻¹ L h` of `Γ(N)` (`N ≥ 3`) by conjugation, on the radical lattice by `lineGφ`, on the Levi `Γ(N)` by conjugation by the Levi block `lineGA`, and on a coefficient module of `SL₃(ℤ)` by `ρ f`.
`lineFaceAction_radDet`: the determinant of the radical map of the self-twist `(F.twist f).φ` is the determinant of the inverse Levi block, so the two orientation signs of `FaceAction.pairing_scale` cancel.
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

/-- **The big stabilizer of the line cusp `h⁻¹ L h` as a group of face automorphisms.** -/
def lineFaceAction : FaceAction hN (lineFaceExt N h) (lineGRep ρ N h) ↥(bigLineStabAt h) where
  θ := lineGθ N hN h
  φ := lineGφ N hN h
  α := lineGα N hN h
  A := lineGA h
  T f := coeffEquiv ρ f.1
  T_one v := by
    change ρ ((1 : bigLineStabAt h) : SL(3, ℤ)) v = v
    rw [Subgroup.coe_one, map_one]; rfl
  T_mul f g v := by
    change ρ ((f * g : bigLineStabAt h) : SL(3, ℤ)) v = ρ f.1 (ρ g.1 v)
    rw [Subgroup.coe_mul, map_mul]; rfl
  inl_comm := lineG_inl_comm N hN h
  rightHom_comm := lineG_rightHom_comm N hN h
  hT f e v := lineGT_hT ρ N hN h f e v
  hA := lineG_hA N hN h

theorem lineFaceAction_radDet (f : bigLineStabAt h) :
    radDet ((lineFaceAction N hN h ρ).twist f).φ.toMonoidHom = ((((lineFaceAction N hN h ρ).A f)⁻¹).val.det : ℤ) :=
  lineGφ_inv_radDet_inv N hN h f

end TernaryPeriodPolynomials.Argument.FaceDescent
