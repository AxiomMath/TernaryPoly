module

public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationGroup
public import Mathlib.Topology.Homeomorph.TransferInstance
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpacePlaneBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

/-- Product coordinates give the parameter group its natural real topology. -/
def parameterEquiv : Parameters ≃ RealGL2 × (Vec2 × ℝˣ) where
  toFun p := (p.A,(p.u,p.d))
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance parametersTopology : TopologicalSpace Parameters := parameterEquiv.topologicalSpace

def parameterHomeomorph : Parameters ≃ₜ RealGL2 × (Vec2 × ℝˣ) := parameterEquiv.homeomorph

theorem continuous_A : Continuous Parameters.A :=
  continuous_fst.comp parameterHomeomorph.continuous

theorem continuous_u : Continuous Parameters.u :=
  (continuous_fst.comp continuous_snd).comp parameterHomeomorph.continuous

theorem continuous_d : Continuous Parameters.d :=
  (continuous_snd.comp continuous_snd).comp parameterHomeomorph.continuous

theorem continuous_parameters_mk {X : Type*} [TopologicalSpace X]
    {A : X → RealGL2} {u : X → Vec2} {d : X → ℝˣ}
    (hA : Continuous A) (hu : Continuous u) (hd : Continuous d) :
    Continuous (fun x => (⟨A x,u x,d x⟩ : Parameters)) :=
  parameterHomeomorph.symm.continuous.comp (hA.prodMk (hu.prodMk hd))

/-- Continuity follows from the literal signed block multiplication and inverse formulas. -/
instance parametersTopologicalGroup : IsTopologicalGroup Parameters where
  continuous_mul := by
    apply continuous_parameters_mk
    · exact (continuous_A.comp continuous_fst).mul (continuous_A.comp continuous_snd)
    · exact ((Units.continuous_val.comp (continuous_A.comp continuous_fst)).matrix_mulVec
        (continuous_u.comp continuous_snd)).add
        ((Units.continuous_val.comp (continuous_d.comp continuous_snd)).smul
          (continuous_u.comp continuous_fst))
    · exact (continuous_d.comp continuous_fst).mul (continuous_d.comp continuous_snd)
  continuous_inv := by
    apply continuous_parameters_mk
    · exact continuous_A.inv
    · have hd : Continuous (fun p : Parameters => (p.d : ℝ)⁻¹) :=
        (Units.continuous_val.comp continuous_d).inv₀ (fun p => p.d.ne_zero)
      exact (hd.smul ((Units.continuous_coe_inv.comp continuous_A).matrix_mulVec
        continuous_u)).neg
    · exact continuous_d.inv

end TernaryPoly.SymmetricSpacePlaneBordification
