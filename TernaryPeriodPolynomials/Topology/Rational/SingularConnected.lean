module

public import TernaryPeriodPolynomials.Topology.Rational.SingularAugmentation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalSingularAugmentation
open CategoryTheory Limits ContractibleSingularHomology

/-- For every path-connected space, the genuine point-induced augmentation is an isomorphism.
Only H0 is finite-dimensional here; no finiteness of the singular chains is used. -/
theorem augmentation_isIso_of_pathConnected (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : IsIso (augmentation X) := by
  have : PathConnectedSpace (TopCat.of X) := inferInstanceAs (PathConnectedSpace X)
  let e : (chains X).homology 0 ≅ ModuleCat.of.{0} ℚ ℚ :=
    @asIso (ModuleCat.{0} ℚ) _ _ _
      ((TopCat.of X).singularHomology₀ε (ModuleCat.of.{0} ℚ ℚ))
      (TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier
        (TopCat.of X) (ModuleCat.of.{0} ℚ ℚ))
  have : Module.Finite ℚ ((chains X).homology 0) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  have hs := augmentation_surjective X
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    e.toLinearEquiv.finrank_eq (f := (augmentation X).hom)).mpr hs
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hi,hs⟩

end TernaryPoly.RationalSingularAugmentation
