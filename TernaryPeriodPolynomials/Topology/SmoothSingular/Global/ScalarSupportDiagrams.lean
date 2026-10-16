module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarCoverSupport
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set SymmetricSpaceCovering TopologicalSpace
variable (A : Rep.{0} ℚ DeckGroup)

/-- Fixed-support rational enlargement is the same actual ambient cochain. -/
theorem rationalCoverSupportMap_forget (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    rationalCoverSupportMap A K L hKL ≫ kernel.ι (rationalCoverRestriction A (subset_univ Lᶜ)) =
      kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ)) := kernel.lift_ι _ _ _

/-- Fixed-support real enlargement is the same actual ambient cochain. -/
theorem realCoverSupportMap_forget (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    realCoverSupportMap A K L hKL ≫ kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Lᶜ)) =
      kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Kᶜ)) := kernel.lift_ι _ _ _

/-- Rational support enlargement is the identity on equal supports. -/
theorem rationalCoverSupportMap_id (K : Set OrbitSpace) :
    rationalCoverSupportMap A K K (Subset.refl K) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ)))).mp
  exact (rationalCoverSupportMap_forget A K K _).trans (Category.id_comp _).symm

/-- Rational support enlargement composes. -/
theorem rationalCoverSupportMap_comp (K L M : Set OrbitSpace) (hKL : K ⊆ L) (hLM : L ⊆ M) :
    rationalCoverSupportMap A K L hKL ≫ rationalCoverSupportMap A L M hLM =
      rationalCoverSupportMap A K M (hKL.trans hLM) := by
  apply (cancel_mono (kernel.ι (rationalCoverRestriction A (subset_univ Mᶜ)))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun u => rationalCoverSupportMap A K L hKL ≫ u) (rationalCoverSupportMap_forget A L M hLM)).trans
      ((rationalCoverSupportMap_forget A K L hKL).trans (rationalCoverSupportMap_forget A K M _).symm))

/-- Real support enlargement is the identity on equal supports. -/
theorem realCoverSupportMap_id (K : Set OrbitSpace) :
    realCoverSupportMap A K K (Subset.refl K) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Kᶜ)))).mp
  exact (realCoverSupportMap_forget A K K _).trans (Category.id_comp _).symm

/-- Real support enlargement composes. -/
theorem realCoverSupportMap_comp (K L M : Set OrbitSpace) (hKL : K ⊆ L) (hLM : L ⊆ M) :
    realCoverSupportMap A K L hKL ≫ realCoverSupportMap A L M hLM =
      realCoverSupportMap A K M (hKL.trans hLM) := by
  apply (cancel_mono (kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Mᶜ)))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun u => realCoverSupportMap A K L hKL ≫ u) (realCoverSupportMap_forget A L M hLM)).trans
      ((realCoverSupportMap_forget A K L hKL).trans (realCoverSupportMap_forget A K M _).symm))

/-- Actual complement-relative rational singular cohomology on all compact supports. -/
def rationalCoverCompactDiagram (n : ℕ) : Compacts OrbitSpace ⥤ ModuleCat.{0} ℚ :=
  (show Compacts OrbitSpace ⥤ CochainComplex (ModuleCat.{0} ℚ) ℕ from {
    obj K := rationalCoverSupport A (K : Set OrbitSpace)
    map f := rationalCoverSupportMap A _ _ (leOfHom f)
    map_id K := rationalCoverSupportMap_id A K
    map_comp f g := (rationalCoverSupportMap_comp A _ _ _ (leOfHom f) (leOfHom g)).symm }) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n

/-- Actual complement-relative real singular cohomology on all compact supports. -/
def realCoverCompactDiagram (n : ℕ) : Compacts OrbitSpace ⥤ ModuleCat.{0} ℝ :=
  (show Compacts OrbitSpace ⥤ CochainComplex (ModuleCat.{0} ℝ) ℕ from {
    obj K := realCoverSupport A (K : Set OrbitSpace)
    map f := realCoverSupportMap A _ _ (leOfHom f)
    map_id K := realCoverSupportMap_id A K
    map_comp f g := (realCoverSupportMap_comp A _ _ _ (leOfHom f) (leOfHom g)).symm }) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ) (ComplexShape.up ℕ) n

end TernaryPoly.SmoothSingularGlobal
