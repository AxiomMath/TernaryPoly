module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalStaircase
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ModuleQuasiIso

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal.TotalAugmentation
open CategoryTheory Limits

variable {K : RealBicomplex} {C : CochainComplex (ModuleCat.{0} ℝ) ℕ}
variable (a : TotalAugmentation C K) (hr : a.ExactRows)

include hr in
/-- Exact augmented horizontal rows make the actual degree-two total augmentation a
quasi-isomorphism, via the proved finite cocycle and boundary lifts. -/
theorem totalAugmentationMap_quasiIso : ShortComplex.QuasiIso a.totalAugmentationMap :=
  module_quasiIso_of_cycle_boundary_lifts a.totalAugmentationMap
    (fun x hx => by
      obtain ⟨z,hz,y,hy⟩ := a.total_cycle_lift hr x hx
      exact ⟨z,hz,y,hy⟩) (fun z _ y hy => a.total_boundary_lift hr z y hy)

/-- The actual degree-two homology isomorphism of an exact horizontal resolution. -/
def totalAugmentationHomologyIso : (C.sc' 1 2 3).homology ≅ (totalWindow K).homology := by
  have := a.totalAugmentationMap_quasiIso hr
  exact asIso (ShortComplex.homologyMap a.totalAugmentationMap)

/-- The isomorphism is induced by the literal augmented chain map. -/
theorem totalAugmentationHomologyIso_hom :
    (a.totalAugmentationHomologyIso hr).hom = ShortComplex.homologyMap a.totalAugmentationMap := rfl

end TernaryPoly.SmoothSingularGlobal.TotalAugmentation
