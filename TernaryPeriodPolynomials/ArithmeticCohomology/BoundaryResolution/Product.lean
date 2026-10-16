module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.FamilyCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison.Family
open CategoryTheory Category Limits HomologicalComplex

variable {I : Type}

/-- The full product of rational cochain complexes. -/
def productComplex (C : I → CochainComplex (ModuleCat.{0} ℚ) ℕ) :
    CochainComplex (ModuleCat ℚ) ℕ where
  X n := ModuleCat.of ℚ (∀ i,(C i).X n)
  d n m := ModuleCat.ofHom (LinearMap.pi (fun i => ((C i).d n m).hom.comp (LinearMap.proj i)))
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    funext i
    exact congrArg (fun u : (C i).X n ⟶ (C i).X m => u (f i)) ((C i).shape n m h)
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    funext i
    exact congrArg (fun u : (C i).X n ⟶ (C i).X k => u (f i)) ((C i).d_comp_d n m k)

/-- Isomorphisms of every cochain factor give a genuine product cochain isomorphism. -/
def productComplexIso {C D : I → CochainComplex (ModuleCat.{0} ℚ) ℕ} (e : ∀ i,C i ≅ D i) :
    productComplex C ≅ productComplex D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.piCongrRight (fun i => ((HomologicalComplex.eval _ _ n).mapIso (e i)).toLinearEquiv)).toModuleIso)
    (fun n m _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      funext i
      exact congrArg (fun u : (C i).X n ⟶ (D i).X m => u (f i)) ((e i).hom.comm n m))

end TernaryPoly.BoundaryFaceResolutionComparison.Family
