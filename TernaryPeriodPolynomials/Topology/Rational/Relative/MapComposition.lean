module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.Homotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSingular
open CategoryTheory Limits HomologicalComplex RationalSingularAugmentation
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Actual maps of relative singular complexes respect composition of topological pairs. -/
theorem relativeMap_comp (f : C(X,Y)) (g : C(Y,Z)) (A : Set X) (B : Set Y) (C : Set Z)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    relativeMap f A B hf ≫ relativeMap g B C hg =
      relativeMap (g.comp f) A C (fun _ hx => hg (hf hx)) := by
  apply (cancel_epi (cokernel.π (inclusion A))).mp
  simp [relativeMap,cokernel.map,Category.assoc,chainMap_comp]

end TernaryPoly.RationalRelativeSingular
