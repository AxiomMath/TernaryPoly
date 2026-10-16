module

public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Star.Real

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpacePositive

/-- The actual normalized congruence action is jointly continuous in the real matrix and form. -/
theorem continuous_uncurried_act : Continuous (fun p : RealGL × Space => act p.1 p.2) := by
  apply Continuous.subtype_mk
  have hg : Continuous (fun p : RealGL × Space => p.1.val) :=
    Units.continuous_val.comp continuous_fst
  have hc : Continuous (fun p : RealGL × Space => conjugate p.1 p.2.val) :=
    (hg.mul (continuous_subtype_val.comp continuous_snd)).mul hg.star
  exact (hc.matrix_trace.inv₀ (fun p =>
    ne_of_gt (conjugate_positive p.1 p.2.val p.2.property.1).trace_pos)).smul hc

/-- An actual real-matrix path supplies an isotopy of the actual normalized positive-form space. -/
def actionHomotopy {g : RealGL} (p : Path 1 g) :
    ContinuousMap.Homotopy (ContinuousMap.id Space) (actionHomeomorph g).toHomotopyEquiv.toFun where
  toFun z := act (p z.1) z.2
  continuous_toFun := by
    have hp : Continuous (fun z : unitInterval × Space => p z.1) :=
      p.continuous.comp continuous_fst
    exact Continuous.comp (g := fun z : RealGL × Space => act z.1 z.2)
      (f := fun z : unitInterval × Space => (p z.1,z.2))
      continuous_uncurried_act (hp.prodMk continuous_snd)
  map_zero_left S := by simp
  map_one_left S := by simp; rfl

/-- Every time slice of the actual matrix-action isotopy is injective. -/
theorem actionHomotopy_injective {g : RealGL} (p : Path 1 g) (t : unitInterval) :
    Function.Injective (fun S => actionHomotopy p (t,S)) :=
  (actionHomeomorph (p t)).injective

end TernaryPoly.SymmetricSpacePositive
