module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFamilies

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set

/-- Componentwise injective linear maps detect finite dependent-family support. -/
theorem finiteFamily_of_injective_map {ι : Type*} {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℝ (B i)]
    (f : ∀ i, A i →ₗ[ℝ] B i) (hf : ∀ i, Function.Injective (f i)) (w : ∀ i, A i)
    (hw : (familySupport (fun i => f i (w i))).Finite) : (familySupport w).Finite := by
  apply hw.subset
  intro i hi hz
  apply hi
  apply hf i
  exact hz.trans (map_zero _).symm

end TernaryPoly.SmoothSingularGlobal
