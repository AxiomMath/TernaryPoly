module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactGluing

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular
variable {X : Type} [TopologicalSpace X]

/-- Empty support gives the zero actual relative chain complex on any topological space. -/
theorem empty_support_isZero : IsZero (supportChains (∅ : Set X)) := by
  have : IsIso (inclusion (Set.univ : Set X)) :=
    (show IsIso (chainHomeomorphIso (Homeomorph.Set.univ X)).hom from inferInstance)
  change IsZero (cokernel (inclusion ((∅ : Set X)ᶜ)))
  rw [Set.compl_empty]
  exact isZero_cokernel_of_epi (inclusion (Set.univ : Set X))

/-- All actual relative homology groups with empty support vanish. -/
theorem empty_support_homology_isZero (k : ℕ) : IsZero ((supportChains (∅ : Set X)).homology k) :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) k).map_isZero empty_support_isZero

end TernaryPoly.RationalManifoldCompact
