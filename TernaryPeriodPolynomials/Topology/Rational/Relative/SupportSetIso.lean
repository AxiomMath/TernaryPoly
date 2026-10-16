module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular
variable {X : Type} [TopologicalSpace X]

/-- Equality of actual excluded subsets gives the literal relative-chain isomorphism. -/
def relativeSetIso (S T : Set X) (h : S = T) : relativeChains S ≅ relativeChains T :=
  eqToIso (congrArg (fun W : Set X => relativeChains W) h)

/-- Changing an excluded subset by equality preserves the literal inclusion map. -/
theorem relativeSetIso_hom_inclusion (S S' T : Set X) (h : S = S') (hST : S ⊆ T) (hS'T : S' ⊆ T) :
    (relativeSetIso S S' h).hom ≫ relativeInclusion S' T hS'T = relativeInclusion S T hST := by
  subst S'
  simp [relativeSetIso]

/-- Changing the target excluded subset by equality preserves the literal inclusion map. -/
theorem relativeInclusion_setIso (S T T' : Set X) (h : T = T') (hST : S ⊆ T) (hST' : S ⊆ T') :
    relativeInclusion S T hST ≫ (relativeSetIso T T' h).hom = relativeInclusion S T' hST' := by
  subst T'
  simp [relativeSetIso]

/-- The actual homology isomorphism induced by equality of excluded subsets. -/
def relativeHomologySetIso (S T : Set X) (h : S = T) (k : ℕ) :
    (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).obj (relativeChains S) ≅
      (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).obj (relativeChains T) :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso (relativeSetIso S T h)

/-- Equality transport commutes with the actual relative homology restriction at the source. -/
theorem relativeHomologySetIso_hom_inclusion (S S' T : Set X) (h : S = S')
    (hST : S ⊆ T) (hS'T : S' ⊆ T) (k : ℕ) :
    (relativeHomologySetIso S S' h k).hom ≫ homologyMap (relativeInclusion S' T hS'T) k =
      homologyMap (relativeInclusion S T hST) k := by
  subst S'
  simp [relativeHomologySetIso, relativeSetIso]
  exact Category.id_comp _

/-- Equality transport commutes with the actual relative homology restriction at the target. -/
theorem homologyInclusion_setIso (S T T' : Set X) (h : T = T')
    (hST : S ⊆ T) (hST' : S ⊆ T') (k : ℕ) :
    homologyMap (relativeInclusion S T hST) k ≫ (relativeHomologySetIso T T' h k).hom =
      homologyMap (relativeInclusion S T' hST') k := by
  subst T'
  simp [relativeHomologySetIso, relativeSetIso]
  exact Category.comp_id _

end TernaryPoly.RationalRelativeSupport
